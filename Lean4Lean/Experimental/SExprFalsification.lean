import Lean4Lean.Experimental.SExprParamsD0

/-!
# NORM-DI falsification probes

This module is an additive truth-status harness for the direct logical-
relation route.  It deliberately imports the concrete Nat fixture but is not
imported by the production development.  The first probes pin one literal
generated zero rule, show that its redex and contractum are not syntactically
identical, expose its registered contraction, and recover the actual
stratification depth of its evidence-rich typing derivation.

The two semantic T2 claims are witnessed below by premise-free informative
(non-bottom) level-one observations.  T3 now also has clean concrete strong
and stratified derivations, including strict successor-predecessor depth
provenance; completing the full self-adequacy induction still requires the
concrete Nat coherent typed-iota leaf.  None of the results below treats a
bottom observation or an uninhabited certificate premise as evidence for
adequacy.
-/

namespace Lean4Lean
namespace SExpr
namespace ParamsD0
namespace Falsification

/-! ## F0: concrete identity boundary -/

/-- The target context used by the first exact-redex probe is genuinely
empty and well formed. -/
theorem emptyTargetWF (univs : Nat) :
    letI : Params := natParams univs
    Ctx.WF ([] : List SExpr) := by
  letI : Params := natParams univs
  exact ⟨⟩

/-- The substitution boundary of the first probe is the direct identity
substitution, not an erased legacy substitution. -/
theorem emptyDirectIdentity (univs : Nat) :
    letI : Params := natParams univs
    LR.DirectSubstWF ([] : List SExpr) .id .id [] .nil := by
  letI : Params := natParams univs
  exact .id

/-! ## F2: the monotone telescope cannot hide a bottom head type -/

/-- An informative terminal observation forces the registered head-type
observation of every direct fixed-head telescope to be informative as well.
The empty telescope uses its retained typing/order facts; every nonempty
telescope has a literal Pi head type.  Thus a producer cannot discharge an
informative request solely by choosing `Witness.bot`. -/
theorem directFixedHeadTelescopeLE_headTy_nonbot
    [Params] [Params.Semantic]
    {Γ : List SExpr}
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {head out headTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out}
    (H : LR.DirectFixedHeadTelescopeLE
      (headTy := headTy) (outTy := outTy)
      Γ mx my captureType spine)
    (houtNonbot : ¬out ≤ TShape.bot) :
    ¬headTy ≤ TShape.bot := by
  cases H with
  | nil htyped hle =>
      intro hheadTyBot
      exact houtNonbot <| TShape.HasType.bot_r'
        (hle.trans hheadTyBot) htyped
  | cons =>
      exact TShape.forallE_not_le_bot

/-- Non-bottomness does not make shape typing functional, or even force two
type observations of the same term to be compatible.  The same informative
singleton lambda is typed at two Pi shapes whose domains are the incompatible
sort observations `sort false` and `sort true`.

This is the two-sort rejection needed by the fixed-head audit: a semantic
typing package and a capture-built telescope cannot be synchronized from
their shared non-bottom term and two `HasType` proofs alone.  Any producer
using that route must retain an explicit comparison (or build the registered
type witness at the telescope's own observation). -/
theorem nonbottom_lambda_has_incompatible_type_shapes [Params] :
    ∃ (term typeFalse typeTrue : WShape 2),
      ¬term ≤ WShape.bot ∧
        term.HasType typeFalse ∧ term.HasType typeTrue ∧
          ¬typeFalse.Compat typeTrue := by
  let arg : WShape 1 := .bot
  let result : WShape 1 := .sort false
  let termFun : WShapeFun 1 := .single arg result
  have htermFun : termFun.NonZero := by
    apply WShapeFun.NonZero.iff.2
    exact ⟨(arg, result), WShapeFun.mem_single.2 (.inl rfl),
      WShape.sort_not_le_bot⟩
  let typeFun : WShapeFun 1 := .single arg .type
  have typed (dom : WShape 1) (hdom : dom.HasType .type) :
      (WShape.lam termFun htermFun).HasType
        (.forallE dom typeFun) := by
    rw [WShape.lam_eq_lam']
    apply WShape.HasType.lam
    have harg : arg.HasType dom := WShape.HasType.bot' hdom
    refine WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
    · refine WShape.HasTypePi.def.2
        ⟨WShape.HasDom.single.2 (.inl harg), ?_⟩
      intro x y hxy
      obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ :=
        WShapeFun.mem_single.1 hxy
      · exact WShape.HasType.sort
      · exact WShape.HasType.bot' WShape.HasType.sort
    · exact WShape.HasDom.single.2 (.inl harg)
    · simp only [termFun, typeFun, WShapeFun.single_app]
      split
      · exact WShape.HasType.sort
      · exact WShape.HasType.bot' <|
          WShape.HasType.bot' WShape.HasType.sort
  let term : WShape 2 := .lam termFun htermFun
  let typeFalse : WShape 2 :=
    .forallE (WShape.sort false) typeFun
  let typeTrue : WShape 2 :=
    .forallE (WShape.sort true) typeFun
  have htermNonbot : ¬term ≤ WShape.bot := by
    intro hbot
    have hval : ShapeS.lam termFun.1 = ShapeS.bot :=
      Shape.le_bot.1 hbot
    cases hval
  have hincompat : ¬typeFalse.Compat typeTrue := by
    intro hcompat
    have hdomCompat :=
      (WShape.Compat.forallE_forallE.1 hcompat).1
    have hfalseTrue : false = true :=
      WShape.Compat.sort_sort.1 hdomCompat
    exact Bool.false_ne_true hfalseTrue
  exact ⟨term, typeFalse, typeTrue, htermNonbot,
    typed (.sort false) WShape.HasType.sort,
    typed (.sort true) WShape.HasType.sort, hincompat⟩

/-! ## F1/T0: one literal generated Nat-zero contraction -/

def zeroMotive (univs : Nat) (level : @SLevel (natParams univs)) :
    @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact SExpr.forallE (SExpr.const ``Nat []) (SExpr.sort level)

def zeroMinorType (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])

def zeroSuccMinorType (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact SExpr.forallE (SExpr.const ``Nat []) <|
    SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
      (SExpr.bvar 3).app ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))

/-- The source telescope is exactly the three literal binders of the
generated zero equation. -/
def zeroSourceContext (univs : Nat)
    (level : @SLevel (natParams univs)) :
    List (@SExpr (natParams univs)) :=
  [zeroSuccMinorType univs, zeroMinorType univs, zeroMotive univs level]

/-- The actual `Nat.rec`/`Nat.zero` redex under the literal generated-rule
telescope. -/
def zeroRedex (univs : Nat) (level : @SLevel (natParams univs)) :
    @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
    (SExpr.bvar 1)).app (SExpr.bvar 0)).app
      (SExpr.const ``Nat.zero [])

/-- The post-contraction term selected by the zero rule: the captured zero
minor at binder index one. -/
def zeroContractum (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact SExpr.bvar 1

/-- The informative result type of the zero contraction. -/
def zeroResultType (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])

/-- Literal capture valuation for the three paths of the generated zero
descriptor.  The final branch is the successor-minor path because those are
the only paths in this descriptor; the named-value lemmas below make every
live lookup explicit. -/
def zeroCapture (univs : Nat) :
    (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path →
      @SExpr (natParams univs) := by
  letI : Params := natParams univs
  intro path
  rcases path with path | path
  · rcases path with _ | path
    · exact .bvar 0
    · rcases path with _ | path
      · exact .bvar 1
      · rcases path with _ | path
        · exact .bvar 2
        · exact path.elim
  · exact path.elim

@[simp] theorem zeroCapture_motive (univs : Nat) :
    zeroCapture univs natZeroMotivePath =
      (@SExpr.bvar (natParams univs) 2) := by
  rfl

@[simp] theorem zeroCapture_minor (univs : Nat) :
    zeroCapture univs natZeroMinorPath =
      (@SExpr.bvar (natParams univs) 1) := by
  rfl

@[simp] theorem zeroCapture_succMinor (univs : Nat) :
    zeroCapture univs natZeroSuccMinorPath =
      (@SExpr.bvar (natParams univs) 0) := by
  rfl

/-- The real generated `Pattern.RHS`, instantiated with the literal universe
and capture valuation. -/
def zeroGeneratedApplication (univs : Nat)
    (level : @SLevel (natParams univs)) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact (NatGeneration.ruleRHS natRuleClosure
    probeNatFlatCtorZero_lookup).applyS [level] (zeroCapture univs)

/-- The same generated application displayed as the fixed registered body
followed by its three captures. -/
def zeroAppliedRhs (univs : Nat)
    (level : @SLevel (natParams univs)) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact [SExpr.bvar 2, SExpr.bvar 1, SExpr.bvar 0].foldl
    (fun f a => f.app a)
    (SExpr.mkInst [level]
      (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)

theorem zeroGeneratedApplication_eq_appliedRhs (univs : Nat)
    (level : @SLevel (natParams univs)) :
    zeroGeneratedApplication univs level = zeroAppliedRhs univs level := by
  letI : Params := natParams univs
  rw [zeroGeneratedApplication, natZeroRuleRHS_applyS]
  simp [zeroAppliedRhs]

/-- The selected descriptor is definitionally the literal zero entry and
retains exactly the three advertised paths. -/
theorem zeroDescriptorSelected (univs : Nat) :
    letI : Params := natParams univs
    (natZeroDirectIotaRule univs).df =
        NatGeneration.rule 0 NatGeneration.flatCtors[0] ∧
      (natZeroDirectIotaRule univs).capturePaths =
        [natZeroMotivePath, natZeroMinorPath, natZeroSuccMinorPath] ∧
      Params.env.defeqs (natZeroDirectIotaRule univs).df := by
  letI : Params := natParams univs
  exact ⟨rfl, natZeroDirectIotaRule_capturePaths univs,
    (natZeroDirectIotaRule univs).registered⟩

/-- The redex is not the term obtained after contraction.  This blocks a
reflexivity-only interpretation of the local computation probe. -/
theorem zeroRedex_ne_contractum (univs : Nat)
    (level : @SLevel (natParams univs)) :
    zeroRedex univs level ≠ zeroContractum univs := by
  simp [zeroRedex, zeroContractum]

/-- The actual generated RHS performs its three beta steps and reaches the
literal captured zero minor. -/
theorem zeroGeneratedApplication_beta (univs : Nat)
    (level : @SLevel (natParams univs)) :
    letI : Params := natParams univs
    WHRedS (zeroSourceContext univs level)
      (zeroGeneratedApplication univs level) (zeroContractum univs) := by
  letI : Params := natParams univs
  simpa [zeroGeneratedApplication, zeroContractum] using
    natZeroRuleRHS_beta univs level (zeroSourceContext univs level)
      (zeroCapture univs)

/-- The registered local iota action connects the literal redex to the real
generated RHS application at its informative dependent result type. -/
theorem zeroRegisteredContraction (univs : Nat)
    (level : @SLevel (natParams univs)) :
    letI : Params := natParams univs
    IsDefEq (zeroSourceContext univs level)
      (zeroRedex univs level) (zeroGeneratedApplication univs level)
      (zeroResultType univs) := by
  letI : Params := natParams univs
  rw [zeroGeneratedApplication_eq_appliedRhs]
  simpa [zeroSourceContext, zeroRedex, zeroAppliedRhs, zeroResultType,
    zeroMotive, zeroMinorType, zeroSuccMinorType] using
    natZeroRuleActionSound univs (Gamma := []) level

/-! ## F1/T2 witness boundary: a fixed informative level-one observation -/

/-- Three concrete object-language universes.  The spacing is intentional:
`Sort u0 : Sort u1`, while the constant motive returning `Sort u1` itself
lives in the recursor universe `u2`. -/
def zeroT2U0 (univs : Nat) : @SLevel (natParams univs) := by
  letI : Params := natParams univs
  exact .zero

def zeroT2U1 (univs : Nat) : @SLevel (natParams univs) := by
  letI : Params := natParams univs
  exact (zeroT2U0 univs).succ

def zeroT2U2 (univs : Nat) : @SLevel (natParams univs) := by
  letI : Params := natParams univs
  exact (zeroT2U1 univs).succ

/-- The smallest useful closed motive is sort-valued.  A Nat-valued motive
would force its body action down to shape level zero, where an inductive-type
observation is unavailable. -/
def zeroT2Motive (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact SExpr.lam (SExpr.const ``Nat []) (SExpr.sort (zeroT2U1 univs))

def zeroT2ZeroMinor (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact SExpr.sort (zeroT2U0 univs)

def zeroT2SuccMinor (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact SExpr.lam (SExpr.const ``Nat []) <|
    SExpr.lam ((zeroT2Motive univs).app (SExpr.bvar 0)) <|
      SExpr.sort (zeroT2U0 univs)

/-- A closed, sort-valued `Nat.rec`/`Nat.zero` redex. -/
def zeroT2Redex (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact ((((SExpr.const ``Nat.rec [zeroT2U2 univs]).app
    (zeroT2Motive univs)).app (zeroT2ZeroMinor univs)).app
      (zeroT2SuccMinor univs)).app (SExpr.const ``Nat.zero [])

/-- The reduced term is `Sort u0`; its unreduced dependent result type is
the dynamic beta redex `motive Nat.zero`. -/
def zeroT2Contractum (univs : Nat) : @SExpr (natParams univs) :=
  zeroT2ZeroMinor univs

def zeroT2ResultType (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact (zeroT2Motive univs).app (SExpr.const ``Nat.zero [])

/-- The normal form of `zeroT2ResultType`. -/
def zeroT2ReducedResultType (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact SExpr.sort (zeroT2U1 univs)

def zeroT2Capture (univs : Nat) :
    (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path →
      @SExpr (natParams univs) := by
  intro path
  rcases path with path | path
  · rcases path with _ | path
    · exact zeroT2SuccMinor univs
    · rcases path with _ | path
      · exact zeroT2ZeroMinor univs
      · rcases path with _ | path
        · exact zeroT2Motive univs
        · exact path.elim
  · exact path.elim

@[simp] theorem zeroT2Capture_motive (univs : Nat) :
    zeroT2Capture univs natZeroMotivePath = zeroT2Motive univs := rfl

@[simp] theorem zeroT2Capture_minor (univs : Nat) :
    zeroT2Capture univs natZeroMinorPath = zeroT2ZeroMinor univs := rfl

@[simp] theorem zeroT2Capture_succMinor (univs : Nat) :
    zeroT2Capture univs natZeroSuccMinorPath = zeroT2SuccMinor univs := rfl

def zeroT2GeneratedApplication (univs : Nat) :
    @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact (NatGeneration.ruleRHS natRuleClosure
    probeNatFlatCtorZero_lookup).applyS [zeroT2U2 univs]
      (zeroT2Capture univs)

theorem zeroT2Redex_ne_contractum (univs : Nat) :
    zeroT2Redex univs ≠ zeroT2Contractum univs := by
  simp [zeroT2Redex, zeroT2Contractum, zeroT2ZeroMinor]

/-- The real generated closed RHS reaches the chosen contractum. -/
theorem zeroT2GeneratedApplication_beta (univs : Nat) :
    letI : Params := natParams univs
    WHRedS [] (zeroT2GeneratedApplication univs)
      (zeroT2Contractum univs) := by
  letI : Params := natParams univs
  simpa [zeroT2GeneratedApplication, zeroT2Contractum] using
    natZeroRuleRHS_beta univs (zeroT2U2 univs) [] (zeroT2Capture univs)

/-- The displayed result type itself performs the dynamic beta step.  The
step is path-typed locally at `Sort u2`; it does not appeal to global subject
reduction or a Pi-inversion oracle. -/
theorem zeroT2ResultType_typedBeta (univs : Nat) :
    letI : Params := natParams univs
    TypedWHRedS [] (zeroT2ResultType univs)
      (zeroT2ReducedResultType univs) (SExpr.sort (zeroT2U2 univs)) := by
  letI : Params := natParams univs
  have h := TypedWHRedS.beta (Γ := ([] : List SExpr))
    (A := SExpr.const ``Nat [])
    (body := SExpr.sort (zeroT2U1 univs))
    (B := SExpr.sort (zeroT2U2 univs))
    (arg := SExpr.const ``Nat.zero [])
    (IsDefEqStrong.sort.defeq) ((natZeroStrong univs []).defeq)
  simpa [zeroT2ResultType, zeroT2ReducedResultType, zeroT2Motive,
    SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.id] using h

/-- The fixed T2 term and type observations live literally at shape level
one and are both informative sort observations. -/
def zeroT2TermShape (univs : Nat) : @WShape (natParams univs) 1 := by
  letI : Params := natParams univs
  exact .sort false

def zeroT2TypeShape (univs : Nat) : @WShape (natParams univs) 1 := by
  letI : Params := natParams univs
  exact .sort true

theorem zeroT2ShapeTyping (univs : Nat) :
    letI : Params := natParams univs
    (zeroT2TermShape univs).HasType (zeroT2TypeShape univs) := by
  letI : Params := natParams univs
  exact WShape.HasType.sort

theorem zeroT2Shapes_nonbottom (univs : Nat) :
    letI : Params := natParams univs
    ¬(zeroT2TermShape univs ≤ WShape.bot) ∧
      ¬(zeroT2TypeShape univs ≤ WShape.bot) := by
  letI : Params := natParams univs
  constructor
  · rw [WShape.le_bot]
    intro h
    have h := congrArg Subtype.val h
    change ShapeS.sort false = ShapeS.bot at h
    cases h
  · rw [WShape.le_bot]
    intro h
    have h := congrArg Subtype.val h
    change ShapeS.sort true = ShapeS.bot at h
    cases h

/-- The chosen term observation genuinely interprets the reduced `Sort u0`;
this is not a bottom-only adequacy witness. -/
theorem zeroT2ContractumInterp (univs : Nat) :
    letI : Params := natParams univs
    LE_Interp .nil (zeroT2TermShape univs).T
      (zeroT2Contractum univs) := by
  letI : Params := natParams univs
  apply LE_Interp.sort
  simpa [zeroT2TermShape, zeroT2Contractum, zeroT2ZeroMinor, zeroT2U0]
    using (TShape.sort_eqv (n := 1) (r := false)).1

/-- Likewise the non-bottom type observation interprets the reduced result
type `Sort u1`.  The next T2 step is to transport this exact observation
across the typed beta edge from `zeroT2ResultType`. -/
theorem zeroT2ReducedResultTypeInterp (univs : Nat) :
    letI : Params := natParams univs
    LE_Interp .nil (zeroT2TypeShape univs).T
      (zeroT2ReducedResultType univs) := by
  letI : Params := natParams univs
  apply LE_Interp.sort
  simpa [zeroT2TypeShape, zeroT2ReducedResultType, zeroT2U1, zeroT2U0]
    using (TShape.sort_eqv (n := 1) (r := true)).1

/-! ## F1/T3 syntax half: inhabited exact stratification depth -/

/-- The real registered zero RHS is strongly self-typed under the concrete
Nat semantic instance. -/
theorem zeroRhsStrong (univs : Nat)
    (level : @SLevel (natParams univs)) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    IsDefEqStrong ([] : List SExpr)
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (probeNatZeroRuleType univs level) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  have h := Params.Semantic.registeredRhsStrong
    (Γ := ([] : List SExpr)) (ls := [level])
    (natRule_registered probeNatFlatCtorZero_lookup)
  simpa only [probeNatZeroRuleTypeS_eq] using h

/-- Consequently the generated rule type has an inhabited strong validity
derivation; the premise used by the older body lemma is not vacuous. -/
theorem zeroRuleTypeStrong (univs : Nat)
    (level : @SLevel (natParams univs)) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    ∃ u, IsDefEqStrong ([] : List SExpr)
      (probeNatZeroRuleType univs level)
      (probeNatZeroRuleType univs level) (SExpr.sort u) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  exact (zeroRhsStrong univs level).isType

/-! ## F1/T2 structural generated-RHS certificate -/

/-- The concrete sort-valued motive is strongly typed at the exact outer
binder of the generated zero rule. -/
theorem zeroT2MotiveStrong (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    IsDefEqStrong ([] : List SExpr)
      (zeroT2Motive univs) (zeroT2Motive univs)
      (.forallE (.const ``Nat []) (.sort (zeroT2U2 univs))) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  have hNat := natTypeStrong univs ([] : List SExpr)
  have hBody : IsDefEqStrong
      ([SExpr.const ``Nat []] : List SExpr)
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U1 univs))
      (.sort (zeroT2U2 univs)) := by
    simpa [zeroT2U2, zeroT2U1] using
      (IsDefEqStrong.sort (Γ := [SExpr.const ``Nat []])
        (l := zeroT2U1 univs))
  have hPi : IsDefEqStrong
      ([SExpr.const ``Nat []] : List SExpr)
      (.sort (zeroT2U2 univs)) (.sort (zeroT2U2 univs))
      (.sort (SLevel.succ (zeroT2U2 univs))) := .sort
  simpa [zeroT2Motive] using
    (IsDefEqStrong.lamDF hNat hPi hPi hBody hBody)

/-- The exact generated successor-minor binder after the concrete motive and
zero minor have been substituted. -/
def zeroT2SuccMinorType (univs : Nat) :
    @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact .forallE (.const ``Nat []) <|
    .forallE ((zeroT2Motive univs).app (.bvar 0)) <|
      (zeroT2Motive univs).app
        ((SExpr.const ``Nat.succ []).app (.bvar 1))

/-- The selected zero minor has the reduced form of its dynamic result
type. -/
theorem zeroT2ZeroMinorTyped (univs : Nat) :
    letI : Params := natParams univs
    IsDefEq ([] : List SExpr)
      (zeroT2ZeroMinor univs) (zeroT2ZeroMinor univs)
      (.sort (zeroT2U1 univs)) := by
  letI : Params := natParams univs
  simpa [zeroT2ZeroMinor, zeroT2U1] using
    (IsDefEq.sort (Γ := ([] : List SExpr)) (l := zeroT2U0 univs))

/-- The constant successor minor inhabits the literal generated binder type.
Its result is typed by the motive's two local beta edges, not by a global
normalization or subject-reduction theorem. -/
theorem zeroT2SuccMinorTyped (univs : Nat) :
    letI : Params := natParams univs
    IsDefEq ([] : List SExpr)
      (zeroT2SuccMinor univs) (zeroT2SuccMinor univs)
      (zeroT2SuccMinorType univs) := by
  letI : Params := natParams univs
  let NatS : SExpr := .const ``Nat []
  let Motive : SExpr := zeroT2Motive univs
  let G1 : List SExpr := [NatS]
  let Domain : SExpr := Motive.app (.bvar 0)
  let G2 : List SExpr := [Domain, NatS]
  let SuccN : SExpr := (SExpr.const ``Nat.succ []).app (.bvar 1)
  have hNat := (natTypeStrong univs ([] : List SExpr)).defeq
  have hn : IsDefEq G1 (.bvar 0) (.bvar 0) NatS := by
    simpa [G1, NatS, SExpr.lift, SExpr.lift'] using
      (IsDefEq.bvar (.zero : Lookup G1 0 NatS.lift))
  have hSortBody1 : IsDefEq (NatS :: G1)
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U1 univs))
      (.sort (zeroT2U2 univs)) := by
    simpa [zeroT2U2, zeroT2U1] using
      (IsDefEq.sort (Γ := NatS :: G1) (l := zeroT2U1 univs))
  have hDomainBeta : IsDefEq G1 Domain
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U2 univs)) := by
    simpa [Domain, Motive, zeroT2Motive, NatS, SExpr.inst,
      SExpr.subst, Subst.one, Subst.cons, Subst.id] using
      (IsDefEq.beta hSortBody1 hn)
  have hDomain : IsDefEq G1 Domain Domain
      (.sort (zeroT2U2 univs)) := hDomainBeta.hasType.1
  have hnG2 : IsDefEq G2 (.bvar 1) (.bvar 1) NatS := by
    simpa [G2, Domain, G1, NatS, SExpr.lift, SExpr.lift'] using
      (IsDefEq.bvar (.succ (.zero : Lookup G1 0 NatS.lift)))
  have hSuccN : IsDefEq G2 SuccN SuccN NatS := by
    simpa [SuccN, NatS, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.id] using
      (IsDefEq.appDF (natSuccStrong univs G2).defeq hnG2)
  have hSortBody2 : IsDefEq (NatS :: G2)
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U1 univs))
      (.sort (zeroT2U2 univs)) := by
    simpa [zeroT2U2, zeroT2U1] using
      (IsDefEq.sort (Γ := NatS :: G2) (l := zeroT2U1 univs))
  have hCodBeta : IsDefEq G2 (Motive.app SuccN)
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U2 univs)) := by
    simpa [Motive, zeroT2Motive, NatS, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.id] using
      (IsDefEq.beta hSortBody2 hSuccN)
  have hSort0 : IsDefEq G2
      (.sort (zeroT2U0 univs)) (.sort (zeroT2U0 univs))
      (.sort (zeroT2U1 univs)) := by
    simpa [zeroT2U1] using
      (IsDefEq.sort (Γ := G2) (l := zeroT2U0 univs))
  have hBody : IsDefEq G2
      (.sort (zeroT2U0 univs)) (.sort (zeroT2U0 univs))
      (Motive.app SuccN) := hCodBeta.symm.defeqDF hSort0
  have hInner : IsDefEq G1
      (.lam Domain (.sort (zeroT2U0 univs)))
      (.lam Domain (.sort (zeroT2U0 univs)))
      (.forallE Domain (Motive.app SuccN)) := by
    simpa [G2, Domain, G1] using IsDefEq.lamDF hDomain hBody
  simpa [zeroT2SuccMinor, zeroT2SuccMinorType, NatS, Motive,
    Domain, SuccN, G1] using IsDefEq.lamDF hNat hInner

/-- The actual registered zero RHS, at the fixed T2 captures, reaches its
selected minor through three typed beta edges.  Every edge is retained at the
unreduced dependent result type `zeroT2ResultType`; the proof uses structural
inversion only on the literal generated rule type. -/
theorem zeroT2GeneratedApplication_typedBeta (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    TypedWHRedS ([] : List SExpr)
      (zeroT2GeneratedApplication univs) (zeroT2Contractum univs)
      (zeroT2ResultType univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  let NatS : SExpr := SExpr.const ``Nat []
  let MotiveTy : SExpr := .forallE NatS (.sort (zeroT2U2 univs))
  let ZeroTy : SExpr := (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let SuccTy : SExpr :=
    .forallE NatS <| .forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
      (SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Result : SExpr := (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
  let Body2 : SExpr := .lam SuccTy (SExpr.bvar 1)
  let Body1 : SExpr := .lam ZeroTy Body2
  let G1 : List SExpr := [MotiveTy]
  let G2 : List SExpr := [ZeroTy, MotiveTy]
  let G3 : List SExpr := NatS :: G2
  let RecDomain : SExpr := (SExpr.bvar 2).app (SExpr.bvar 0)
  let G4 : List SExpr := RecDomain :: G3
  let SuccN : SExpr :=
    (SExpr.const ``Nat.succ []).app (SExpr.bvar 1)
  let RecCod : SExpr := (SExpr.bvar 3).app SuccN
  let natSort : SLevel := SLevel.instV [] VLevel.zero.succ
  let innerSort : SLevel :=
    (zeroT2U2 univs).imax (zeroT2U2 univs)
  let succU : SLevel := natSort.imax innerSort
  have hMotiveVar : IsDefEq G1 (.bvar 0) (.bvar 0) MotiveTy := by
    simpa [G1, MotiveTy, NatS, SExpr.lift, SExpr.lift'] using
      (IsDefEq.bvar (.zero : Lookup G1 0 MotiveTy.lift))
  have hZeroConst : IsDefEq G1 (SExpr.const ``Nat.zero [])
      (SExpr.const ``Nat.zero []) NatS := by
    simpa [G1, NatS] using (natZeroStrong univs G1).defeq
  have hZeroTy : IsDefEq G1 ZeroTy ZeroTy
      (.sort (zeroT2U2 univs)) := by
    simpa [G1, ZeroTy, MotiveTy, NatS, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.id] using
      IsDefEq.appDF hMotiveVar hZeroConst
  have hNatG2 := (natTypeStrong univs G2).defeq
  change IsDefEq G2 NatS NatS
    (SExpr.mkInst [] InductiveFixtures.natType.type) at hNatG2
  rw [probeNatTypeTypeV_eq] at hNatG2
  have hNatG2' : IsDefEq G2 NatS NatS (.sort natSort) := by
    simpa [natSort, SExpr.mkInst] using hNatG2
  have hMotiveG3 : IsDefEq G3 (.bvar 2) (.bvar 2) MotiveTy := by
    have hLookup : Lookup G3 2 MotiveTy.lift.lift.lift :=
      .succ (.succ .zero)
    simpa [G3, G2, MotiveTy, NatS, SExpr.lift, SExpr.lift'] using
      (IsDefEq.bvar hLookup)
  have hPred : IsDefEq G3 (.bvar 0) (.bvar 0) NatS := by
    simpa [G3, G2, NatS, SExpr.lift, SExpr.lift'] using
      (IsDefEq.bvar (.zero : Lookup G3 0 NatS.lift))
  have hRecDomain : IsDefEq G3 RecDomain RecDomain
      (.sort (zeroT2U2 univs)) := by
    simpa [RecDomain, MotiveTy, NatS, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.id] using
      IsDefEq.appDF hMotiveG3 hPred
  have hMotiveG4 : IsDefEq G4 (.bvar 3) (.bvar 3) MotiveTy := by
    have hLookup : Lookup G4 3 MotiveTy.lift.lift.lift.lift :=
      .succ (.succ (.succ .zero))
    simpa [G4, G3, G2, MotiveTy, NatS, SExpr.lift,
      SExpr.lift'] using (IsDefEq.bvar hLookup)
  have hPredG4 : IsDefEq G4 (.bvar 1) (.bvar 1) NatS := by
    have hLookup : Lookup G4 1 NatS.lift.lift := .succ .zero
    simpa [G4, G3, G2, NatS, SExpr.lift, SExpr.lift'] using
      (IsDefEq.bvar hLookup)
  have hSuccN : IsDefEq G4 SuccN SuccN NatS := by
    simpa [SuccN, NatS, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.id] using
      IsDefEq.appDF (natSuccStrong univs G4).defeq hPredG4
  have hRecCod : IsDefEq G4 RecCod RecCod
      (.sort (zeroT2U2 univs)) := by
    simpa [RecCod, MotiveTy, NatS, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.id] using
      IsDefEq.appDF hMotiveG4 hSuccN
  have hInnerTy : IsDefEq G3 (.forallE RecDomain RecCod)
      (.forallE RecDomain RecCod) (.sort innerSort) := by
    simpa [innerSort] using IsDefEq.forallEDF hRecDomain hRecCod
  have hSuccTy : IsDefEq G2 SuccTy SuccTy (.sort succU) := by
    simpa [SuccTy, G4, G3, RecDomain, RecCod, SuccN, succU] using
      IsDefEq.forallEDF hNatG2' hInnerTy
  have hLookup : Lookup (SuccTy :: ZeroTy :: MotiveTy :: []) 1
      ZeroTy.lift.lift := .succ .zero
  have hVar : IsDefEq (SuccTy :: ZeroTy :: MotiveTy :: [])
      (.bvar 1) (.bvar 1) Result := by
    simpa [ZeroTy, Result, SExpr.lift, SExpr.lift'] using
      (IsDefEq.bvar hLookup)
  have hBody2 : IsDefEq (ZeroTy :: MotiveTy :: []) Body2 Body2
      (.forallE SuccTy Result) := by
    simpa [Body2] using IsDefEq.lamDF hSuccTy hVar
  have hBody1 : IsDefEq (MotiveTy :: []) Body1 Body1
      (.forallE ZeroTy (.forallE SuccTy Result)) := by
    simpa [Body1] using IsDefEq.lamDF hZeroTy hBody2
  have hMotive : IsDefEq ([] : List SExpr)
      (zeroT2Motive univs) (zeroT2Motive univs) MotiveTy := by
    simpa [MotiveTy, NatS] using (zeroT2MotiveStrong univs).defeq
  let CZeroTy : SExpr := zeroT2ResultType univs
  let CSuccTy : SExpr := zeroT2SuccMinorType univs
  have hStep1Raw := TypedWHRedS.beta hBody1 hMotive
  have hStep1 : TypedWHRedS ([] : List SExpr)
      ((probeNatZeroRuleRhs univs (zeroT2U2 univs)).app
        (zeroT2Motive univs))
      (.lam CZeroTy (.lam CSuccTy (.bvar 1)))
      (.forallE CZeroTy (.forallE CSuccTy CZeroTy)) := by
    simpa [probeNatZeroRuleRhs, Body1, Body2, Result, SuccTy, ZeroTy,
      MotiveTy, NatS, CZeroTy, CSuccTy, zeroT2Motive,
      zeroT2ResultType, zeroT2SuccMinorType, SExpr.inst,
      SExpr.subst, Subst.one, Subst.cons, Subst.lift, Subst.id] using
      hStep1Raw
  have hZero : IsDefEq ([] : List SExpr)
      (zeroT2ZeroMinor univs) (zeroT2ZeroMinor univs) CZeroTy := by
    exact (zeroT2ResultType_typedBeta univs).defeq.symm.defeqDF (by
      simpa [CZeroTy, zeroT2ReducedResultType] using
        zeroT2ZeroMinorTyped univs)
  have hSucc : IsDefEq ([] : List SExpr)
      (zeroT2SuccMinor univs) (zeroT2SuccMinor univs) CSuccTy := by
    simpa [CSuccTy] using zeroT2SuccMinorTyped univs
  have hStep1Apps := (hStep1.app hZero).app hSucc
  have hStep1Full : TypedWHRedS ([] : List SExpr)
      ((((probeNatZeroRuleRhs univs (zeroT2U2 univs)).app
        (zeroT2Motive univs)).app (zeroT2ZeroMinor univs)).app
          (zeroT2SuccMinor univs))
      (((SExpr.lam CZeroTy (SExpr.lam CSuccTy (SExpr.bvar 1))).app
        (zeroT2ZeroMinor univs)).app (zeroT2SuccMinor univs))
      CZeroTy := by
    simpa [CZeroTy, zeroT2ResultType, zeroT2Motive, SExpr.inst,
      SExpr.subst, Subst.one, Subst.cons, Subst.lift, Subst.id] using
      hStep1Apps
  have Wm : Ctx.Subst (fun Γ e A => IsDefEq Γ e e A) ([] : List SExpr)
      (.one (zeroT2Motive univs)) (MotiveTy :: []) :=
    Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar hMotive
  have WmLift := Wm.lift IsDefEq.weakCore IsDefEq.bvar (A := ZeroTy)
  have hSuccTyC : IsDefEq (CZeroTy :: []) CSuccTy CSuccTy
      (.sort succU) := by
    simpa [CZeroTy, CSuccTy, SuccTy, ZeroTy, MotiveTy, NatS,
      zeroT2Motive, zeroT2ResultType, zeroT2SuccMinorType,
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      Subst.id] using hSuccTy.subst WmLift
  have hLookupC : Lookup (CSuccTy :: CZeroTy :: []) 1 CZeroTy.lift.lift :=
    .succ .zero
  have hVarC : IsDefEq (CSuccTy :: CZeroTy :: [])
      (.bvar 1) (.bvar 1) CZeroTy := by
    simpa [CZeroTy, zeroT2ResultType, zeroT2Motive, SExpr.lift,
      SExpr.lift'] using (IsDefEq.bvar hLookupC)
  have hInnerC : IsDefEq (CZeroTy :: [])
      (.lam CSuccTy (.bvar 1)) (.lam CSuccTy (.bvar 1))
      (.forallE CSuccTy CZeroTy) :=
    IsDefEq.lamDF hSuccTyC hVarC
  have hStep2Raw := TypedWHRedS.beta hInnerC hZero
  have hStep2 : TypedWHRedS ([] : List SExpr)
      ((SExpr.lam CZeroTy (SExpr.lam CSuccTy (SExpr.bvar 1))).app
        (zeroT2ZeroMinor univs))
      (SExpr.lam CSuccTy (zeroT2ZeroMinor univs))
      (.forallE CSuccTy CZeroTy) := by
    simpa [CZeroTy, CSuccTy, zeroT2ZeroMinor, zeroT2ResultType,
      zeroT2Motive, zeroT2SuccMinorType, SExpr.lift, SExpr.lift',
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      Subst.id] using hStep2Raw
  have hStep2Full := hStep2.app hSucc
  have hZeroWeak : IsDefEq (CSuccTy :: [])
      (zeroT2ZeroMinor univs) (zeroT2ZeroMinor univs) CZeroTy := by
    simpa [CZeroTy, CSuccTy, zeroT2ZeroMinor, zeroT2ResultType,
      zeroT2Motive, zeroT2SuccMinorType, SExpr.lift,
      SExpr.lift'] using hZero.weak' (.skip .refl)
  have hStep3 := TypedWHRedS.beta hZeroWeak hSucc
  have hAll : TypedWHRedS ([] : List SExpr)
      ((((probeNatZeroRuleRhs univs (zeroT2U2 univs)).app
        (zeroT2Motive univs)).app (zeroT2ZeroMinor univs)).app
          (zeroT2SuccMinor univs))
      (zeroT2ZeroMinor univs) CZeroTy := by
    exact hStep1Full.trans (hStep2Full.trans hStep3)
  rw [zeroT2GeneratedApplication, natZeroRuleRHS_applyS,
    probeNatZeroRuleRhsS_eq]
  simpa [zeroT2Contractum, CZeroTy] using hAll

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.zeroT2GeneratedApplication_typedBeta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleRhsV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms zeroT2GeneratedApplication_typedBeta

/-- Direct validity of the literal dynamic result type follows by transporting
the canonical sort observation backward across its locally typed beta edge. -/
theorem zeroT2ResultType_directSelf (univs : Nat) :
    letI : Params := natParams univs
    (LRD ([] : List SExpr)).TyDefEq
      (zeroT2ResultType univs) (zeroT2ResultType univs)
      (zeroT2TypeShape univs) := by
  letI : Params := natParams univs
  have hBeta := zeroT2ResultType_typedBeta univs
  have hReduced : (LRD ([] : List SExpr)).TyDefEq
      (zeroT2ReducedResultType univs)
      (zeroT2ReducedResultType univs) (zeroT2TypeShape univs) := by
    simpa [zeroT2ReducedResultType, zeroT2TypeShape] using
      (LRD.TyDefEq.sort (Γ := ([] : List SExpr))
        (u := zeroT2U1 univs) (r := true) (n := 1))
  exact (LRD.TyDefEq.whr hBeta.toTypeWHRedPath
    hBeta.toTypeWHRedPath).2 hReduced

/-- The real generated zero RHS is directly self-related at the fixed
informative T2 observation.  The canonical reduced sort relation is converted
to the dynamic result type and then transported backward through the concrete
three-beta certificate. -/
theorem zeroT2GeneratedApplication_directSelf (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    (LRD ([] : List SExpr)).DefEq
      (zeroT2GeneratedApplication univs)
      (zeroT2GeneratedApplication univs)
      (zeroT2ResultType univs)
      (zeroT2TermShape univs) (zeroT2TypeShape univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  have hBeta := zeroT2ResultType_typedBeta univs
  have hTy := zeroT2ResultType_directSelf univs
  have hReduced : (LRD ([] : List SExpr)).DefEq
      (zeroT2ZeroMinor univs) (zeroT2ZeroMinor univs)
      (zeroT2ReducedResultType univs)
      (zeroT2TermShape univs) (zeroT2TypeShape univs) := by
    simpa [zeroT2ZeroMinor, zeroT2ReducedResultType, zeroT2TermShape,
      zeroT2TypeShape, zeroT2U1] using
      (LRD.DefEq.sort (Γ := ([] : List SExpr))
        (u := zeroT2U0 univs) (r := false) (s := true) (n := 1))
  have hTypeRefl : TypeWHRedPath ([] : List SExpr)
      (zeroT2ResultType univs) (zeroT2ResultType univs) :=
    .refl hBeta.defeq.hasType.1
  have hReducedDynamic : (LRD ([] : List SExpr)).TyDefEq
      (zeroT2ReducedResultType univs) (zeroT2ResultType univs)
      (zeroT2TypeShape univs) :=
    (LRD.TyDefEq.whr hBeta.toTypeWHRedPath hTypeRefl).1 hTy
  have hZero : (LRD ([] : List SExpr)).DefEq
      (zeroT2ZeroMinor univs) (zeroT2ZeroMinor univs)
      (zeroT2ResultType univs)
      (zeroT2TermShape univs) (zeroT2TypeShape univs) :=
    LRD.DefEq.conv hReducedDynamic hReduced
  have hApp := zeroT2GeneratedApplication_typedBeta univs
  exact (LRD.DefEq.whr hTy hApp hApp).2 hZero

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.zeroT2GeneratedApplication_directSelf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleRhsV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms zeroT2GeneratedApplication_directSelf

/-! ## F1/T2 clean registered-redex certificate -/

/-- The literal generated zero-rule type is strongly valid without consulting
the broad semantic environment lookup.  Each dependent binder is reconstructed
from the concrete Nat constants and the preceding telescope entries. -/
theorem zeroT2RuleTypeStrong (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    ∃ u, IsDefEqStrong ([] : List SExpr)
      (probeNatZeroRuleType univs (zeroT2U2 univs))
      (probeNatZeroRuleType univs (zeroT2U2 univs)) (.sort u) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  let level : SLevel := zeroT2U2 univs
  let NatS : SExpr := .const ``Nat []
  let Motive : SExpr := .forallE NatS (.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    .forallE NatS <| .forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
      (SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Result : SExpr :=
    (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
  let natSort : SLevel := SLevel.instV [] VLevel.zero.succ
  let motiveSort : SLevel := natSort.imax level.succ
  let innerSort : SLevel := level.imax level
  let succSort : SLevel := natSort.imax innerSort
  have natType (Γ : List SExpr) :
      IsDefEqStrong Γ NatS NatS (.sort natSort) := by
    have h := natTypeStrong univs Γ
    change IsDefEqStrong Γ NatS NatS
      (SExpr.mkInst [] InductiveFixtures.natType.type) at h
    rw [probeNatTypeTypeV_eq] at h
    simpa [NatS, natSort, SExpr.mkInst] using h
  have motiveType (Γ : List SExpr) :
      IsDefEqStrong Γ Motive Motive (.sort motiveSort) := by
    simpa [Motive, motiveSort] using
      IsDefEqStrong.forallEDF (natType Γ)
        (IsDefEqStrong.sort (Γ := NatS :: Γ) (l := level))
        (IsDefEqStrong.sort (Γ := NatS :: Γ) (l := level))
  let G1 : List SExpr := [Motive]
  have hMotiveVarG1 : IsDefEqStrong G1
      (.bvar 0) (.bvar 0) Motive := by
    have hLookup : Lookup G1 0 Motive.lift := .zero
    have h := IsDefEqStrong.bvar hLookup (motiveType G1)
    simpa [G1, Motive, NatS, SExpr.lift, SExpr.lift'] using h
  have hMinorZero : IsDefEqStrong G1 MinorZero MinorZero
      (.sort level) := by
    simpa [MinorZero, NatS, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natType G1) .sort hMotiveVarG1
        (natZeroStrong univs G1) .sort
  let G2 : List SExpr := MinorZero :: G1
  let G3 : List SExpr := NatS :: G2
  let RecDomain : SExpr := (SExpr.bvar 2).app (SExpr.bvar 0)
  have hMotiveVarG3 : IsDefEqStrong G3
      (.bvar 2) (.bvar 2) Motive := by
    have hLookup : Lookup G3 2 Motive.lift.lift.lift :=
      .succ (.succ .zero)
    have h := IsDefEqStrong.bvar hLookup (motiveType G3)
    simpa [G3, G2, G1, Motive, NatS, SExpr.lift, SExpr.lift'] using h
  have hPredG3 : IsDefEqStrong G3 (.bvar 0) (.bvar 0) NatS := by
    have hLookup : Lookup G3 0 NatS.lift := .zero
    have h := IsDefEqStrong.bvar hLookup (natType G3)
    simpa [G3, G2, G1, NatS, SExpr.lift, SExpr.lift'] using h
  have hRecDomain : IsDefEqStrong G3 RecDomain RecDomain
      (.sort level) := by
    simpa [RecDomain, Motive, NatS, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natType G3) .sort hMotiveVarG3 hPredG3 .sort
  let G4 : List SExpr := RecDomain :: G3
  let SuccN : SExpr :=
    (SExpr.const ``Nat.succ []).app (SExpr.bvar 1)
  let RecCod : SExpr := (SExpr.bvar 3).app SuccN
  have hMotiveVarG4 : IsDefEqStrong G4
      (.bvar 3) (.bvar 3) Motive := by
    have hLookup : Lookup G4 3 Motive.lift.lift.lift.lift :=
      .succ (.succ (.succ .zero))
    have h := IsDefEqStrong.bvar hLookup (motiveType G4)
    simpa [G4, G3, G2, G1, Motive, NatS,
      SExpr.lift, SExpr.lift'] using h
  have hPredG4 : IsDefEqStrong G4 (.bvar 1) (.bvar 1) NatS := by
    have hLookup : Lookup G4 1 NatS.lift.lift := .succ .zero
    have h := IsDefEqStrong.bvar hLookup (natType G4)
    simpa [G4, G3, G2, G1, NatS, SExpr.lift, SExpr.lift'] using h
  have hSuccN : IsDefEqStrong G4 SuccN SuccN NatS := by
    simpa [SuccN, NatS, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natType G4) (natType (NatS :: G4))
        (natSuccStrong univs G4) hPredG4 (natType G4)
  have hRecCod : IsDefEqStrong G4 RecCod RecCod (.sort level) := by
    simpa [RecCod, Motive, NatS, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natType G4) .sort hMotiveVarG4 hSuccN .sort
  have hInner : IsDefEqStrong G3
      (.forallE RecDomain RecCod) (.forallE RecDomain RecCod)
      (.sort innerSort) := by
    simpa [innerSort] using
      IsDefEqStrong.forallEDF hRecDomain hRecCod hRecCod
  have hMinorSucc : IsDefEqStrong G2 MinorSucc MinorSucc
      (.sort succSort) := by
    simpa [MinorSucc, RecDomain, RecCod, SuccN, G4, G3, succSort] using
      IsDefEqStrong.forallEDF (natType G2) hInner hInner
  let G5 : List SExpr := MinorSucc :: G2
  have hMotiveVarG5 : IsDefEqStrong G5
      (.bvar 2) (.bvar 2) Motive := by
    have hLookup : Lookup G5 2 Motive.lift.lift.lift :=
      .succ (.succ .zero)
    have h := IsDefEqStrong.bvar hLookup (motiveType G5)
    simpa [G5, G2, G1, Motive, NatS, SExpr.lift, SExpr.lift'] using h
  have hResult : IsDefEqStrong G5 Result Result (.sort level) := by
    simpa [Result, Motive, NatS, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natType G5) .sort hMotiveVarG5
        (natZeroStrong univs G5) .sort
  have hAfterSucc : IsDefEqStrong G2
      (.forallE MinorSucc Result) (.forallE MinorSucc Result)
      (.sort (succSort.imax level)) :=
    .forallEDF hMinorSucc hResult hResult
  have hAfterZero : IsDefEqStrong G1
      (.forallE MinorZero (.forallE MinorSucc Result))
      (.forallE MinorZero (.forallE MinorSucc Result))
      (.sort (level.imax (succSort.imax level))) :=
    .forallEDF hMinorZero hAfterSucc hAfterSucc
  have hRule : IsDefEqStrong ([] : List SExpr)
      (.forallE Motive (.forallE MinorZero (.forallE MinorSucc Result)))
      (.forallE Motive (.forallE MinorZero (.forallE MinorSucc Result)))
      (.sort (motiveSort.imax (level.imax (succSort.imax level)))) :=
    .forallEDF (motiveType []) hAfterZero hAfterZero
  refine ⟨motiveSort.imax (level.imax (succSort.imax level)), ?_⟩
  simpa [probeNatZeroRuleType, level, Motive, MinorZero, MinorSucc,
    Result, NatS] using hRule

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.zeroT2RuleTypeStrong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms zeroT2RuleTypeStrong

/-- The closed Nat-zero redex is definitionally equal to its real generated
RHS application.  The generated LHS is exposed locally, beta-reduced through
the three concrete captures, and composed with the primitive registered head
equality; no environment-wide action-soundness theorem is used. -/
theorem zeroT2RegisteredDefEq (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    IsDefEq ([] : List SExpr)
      (zeroT2Redex univs) (zeroT2GeneratedApplication univs)
      (zeroT2ResultType univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  let level : SLevel := zeroT2U2 univs
  let NatS : SExpr := SExpr.const ``Nat []
  let MotiveTy : SExpr := .forallE NatS (.sort level)
  let ZeroTy : SExpr := (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let SuccTy : SExpr :=
    .forallE NatS <| .forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
      (SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Result : SExpr :=
    (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
  let G1 : List SExpr := [MotiveTy]
  let G2 : List SExpr := ZeroTy :: G1
  let G3 : List SExpr := SuccTy :: G2
  let Redex : SExpr :=
    ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
      (SExpr.bvar 1)).app (SExpr.bvar 0)).app
        (SExpr.const ``Nat.zero [])
  obtain ⟨ruleSort, hRule0⟩ := zeroT2RuleTypeStrong univs
  have hRule : IsDefEqStrong ([] : List SExpr)
      (.forallE MotiveTy (.forallE ZeroTy (.forallE SuccTy Result)))
      (.forallE MotiveTy (.forallE ZeroTy (.forallE SuccTy Result)))
      (.sort ruleSort) := by
    simpa [probeNatZeroRuleType, level, MotiveTy, ZeroTy, SuccTy,
      Result, NatS] using hRule0
  obtain ⟨⟨_, hMotiveTy⟩, _, hRest1⟩ :=
    hRule.forallE_inv' (.inl rfl)
  obtain ⟨⟨_, hZeroTy⟩, _, hRest2⟩ :=
    hRest1.forallE_inv' (.inl rfl)
  obtain ⟨⟨_, hSuccTy⟩, _, _hResultTy⟩ :=
    hRest2.forallE_inv' (.inl rfl)
  have hBody : IsDefEqStrong G3 Redex Redex Result := by
    simpa [G3, G2, G1, Redex, Result, MotiveTy, ZeroTy, SuccTy,
      NatS, level] using
      natZeroRuleBodyStrong univs (Gamma := []) level
        ⟨ruleSort, hRule0⟩
  have hLamS : IsDefEq G2
      (.lam SuccTy Redex) (.lam SuccTy Redex)
      (.forallE SuccTy Result) := by
    exact .lamDF hSuccTy.defeq hBody.defeq
  have hLamZ : IsDefEq G1
      (.lam ZeroTy (.lam SuccTy Redex))
      (.lam ZeroTy (.lam SuccTy Redex))
      (.forallE ZeroTy (.forallE SuccTy Result)) := by
    exact .lamDF hZeroTy.defeq hLamS
  have hLamP : IsDefEq ([] : List SExpr)
      (.lam MotiveTy (.lam ZeroTy (.lam SuccTy Redex)))
      (.lam MotiveTy (.lam ZeroTy (.lam SuccTy Redex)))
      (.forallE MotiveTy (.forallE ZeroTy (.forallE SuccTy Result))) := by
    exact .lamDF hMotiveTy.defeq hLamZ
  have hMotive : IsDefEq ([] : List SExpr)
      (zeroT2Motive univs) (zeroT2Motive univs) MotiveTy := by
    simpa [MotiveTy, NatS, level] using
      (zeroT2MotiveStrong univs).defeq
  have hZero : IsDefEq ([] : List SExpr)
      (zeroT2ZeroMinor univs) (zeroT2ZeroMinor univs)
      (zeroT2ResultType univs) :=
    (zeroT2ResultType_typedBeta univs).defeq.symm.defeqDF
      (by simpa [zeroT2ReducedResultType] using
        zeroT2ZeroMinorTyped univs)
  have hSucc : IsDefEq ([] : List SExpr)
      (zeroT2SuccMinor univs) (zeroT2SuccMinor univs)
      (zeroT2SuccMinorType univs) :=
    zeroT2SuccMinorTyped univs
  have Wm : Ctx.Subst (fun Γ e A => IsDefEq Γ e e A)
      ([] : List SExpr) (.one (zeroT2Motive univs)) (MotiveTy :: []) :=
    Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar hMotive
  have Wmz : Ctx.Subst (fun Γ e A => IsDefEq Γ e e A)
      ([] : List SExpr)
      ((Subst.one (zeroT2Motive univs)).cons (zeroT2ZeroMinor univs))
      (ZeroTy :: MotiveTy :: []) := by
    apply Wm.cons'
    simpa [ZeroTy, MotiveTy, NatS, zeroT2ResultType,
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.id] using hZero
  have hStep1Raw := IsDefEq.beta hLamZ hMotive
  have hStep1 := IsDefEq.appDF
    (IsDefEq.appDF hStep1Raw hZero) hSucc
  have hLamSC := hLamS.subst
    (Wm.lift IsDefEq.weakCore IsDefEq.bvar (A := ZeroTy))
  have hStep2Raw := IsDefEq.beta hLamSC hZero
  have hStep2 := IsDefEq.appDF hStep2Raw hSucc
  have hBodyC := hBody.defeq.subst
    (Wmz.lift IsDefEq.weakCore IsDefEq.bvar (A := SuccTy))
  have hStep3 := IsDefEq.beta hBodyC hSucc
  have hLhsBeta : IsDefEq ([] : List SExpr)
      (((((SExpr.lam MotiveTy (SExpr.lam ZeroTy
        (SExpr.lam SuccTy Redex))).app
        (zeroT2Motive univs)).app (zeroT2ZeroMinor univs)).app
          (zeroT2SuccMinor univs)))
      (zeroT2Redex univs) (zeroT2ResultType univs) := by
    have h := hStep1.trans (hStep2.trans hStep3)
    simpa [Redex, Result, MotiveTy, ZeroTy, SuccTy, NatS, level,
      zeroT2Redex, zeroT2ResultType, zeroT2Motive,
      zeroT2ZeroMinor, zeroT2SuccMinorType, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id] using h
  have hHead : IsDefEq ([] : List SExpr)
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs)
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (probeNatZeroRuleType univs level) := by
    rw [← probeNatZeroRuleTypeS_eq]
    exact IsDefEq.extra (Γ := ([] : List SExpr))
      (natRule_registered probeNatFlatCtorZero_lookup) rfl
  have hHeadApplied0 := IsDefEq.appDF hHead hMotive
  have hHeadApplied1 := IsDefEq.appDF hHeadApplied0 hZero
  have hHeadApplied2 := IsDefEq.appDF hHeadApplied1 hSucc
  have hHeadApplied : IsDefEq ([] : List SExpr)
      (SExpr.app
        (SExpr.app
          (SExpr.app
            (SExpr.mkInst [level]
              (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs)
            (zeroT2Motive univs))
          (zeroT2ZeroMinor univs))
        (zeroT2SuccMinor univs))
      (zeroT2GeneratedApplication univs)
      (zeroT2ResultType univs) := by
    rw [zeroT2GeneratedApplication, natZeroRuleRHS_applyS]
    simpa [MotiveTy, ZeroTy, SuccTy, Result, NatS, level,
      zeroT2ResultType, zeroT2Motive, zeroT2SuccMinorType,
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using hHeadApplied2
  have hLhsEq : SExpr.mkInst [level]
      (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs =
      SExpr.lam MotiveTy (SExpr.lam ZeroTy (SExpr.lam SuccTy Redex)) := by
    rw [probeNatZeroRuleLhsV_eq]
    rfl
  rw [hLhsEq] at hHeadApplied
  exact hLhsBeta.symm.trans hHeadApplied

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.zeroT2RegisteredDefEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms zeroT2RegisteredDefEq

/-- The clean registered equality, paired with the descriptor's literal match
and empty check list, is the actual typed weak-head iota contraction. -/
theorem zeroT2Registered_typedWHRedS (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    TypedWHRedS ([] : List SExpr)
      (zeroT2Redex univs) (zeroT2GeneratedApplication univs)
      (zeroT2ResultType univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  let rgen :=
    (NatGeneration.ruleRHS natRuleClosure probeNatFlatCtorZero_lookup,
      NatGeneration.ruleCheck natRuleClosure
        (List.mem_of_getElem? probeNatFlatCtorZero_lookup))
  have hpat : NatPat
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0) rgen :=
    .mk probeNatFlatCtorZero_lookup
  let rule : Pattern.IotaRule rgen := {
    pat := hpat
    df := NatGeneration.rule 0 NatGeneration.flatCtors[0]
    registered := natRule_registered probeNatFlatCtorZero_lookup
    rhsClosed := natRuleClosure.rhs_closed probeNatFlatCtorZero_lookup
    capturePaths := natCapturePaths NatGeneration.flatCtors[0]
    rhsTower := natRuleRHS_tower probeNatFlatCtorZero_lookup }
  obtain ⟨mcap, hmatch⟩ :=
    RecursorIotaPattern.matchesS_spines
      (rargs := [zeroT2SuccMinor univs, zeroT2ZeroMinor univs,
        zeroT2Motive univs])
      (cargs := []) (rls := [zeroT2U2 univs]) (cls := [])
      (by rfl) (by rfl)
  have hmatch' : (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).MatchesS
      (zeroT2Redex univs) [zeroT2U2 univs] mcap := by
    simpa [zeroT2Redex] using hmatch
  obtain ⟨_, _, hcaps⟩ := natZeroCaptureValues univs hmatch
  let AppliedRhs : SExpr :=
    [zeroT2Motive univs, zeroT2ZeroMinor univs,
      zeroT2SuccMinor univs].foldl
      (fun f a => f.app a)
      (SExpr.mkInst [zeroT2U2 univs]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
  have hGenerated : zeroT2GeneratedApplication univs = AppliedRhs := by
    rw [zeroT2GeneratedApplication, natZeroRuleRHS_applyS]
    simp [AppliedRhs]
  have hrhsEq : zeroT2GeneratedApplication univs =
      rgen.1.applyS [zeroT2U2 univs] mcap := by
    calc
      zeroT2GeneratedApplication univs = AppliedRhs := hGenerated
      _ = (rule.capturePaths.map mcap).foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst [zeroT2U2 univs] rule.df.rhs) := by
        simp [AppliedRhs, rule, hcaps]
      _ = rgen.1.applyS [zeroT2U2 univs] mcap :=
        rule.rhsApply [zeroT2U2 univs] mcap
  have hsound : IsDefEq ([] : List SExpr) (zeroT2Redex univs)
      (rgen.1.applyS [zeroT2U2 univs] mcap)
      (zeroT2ResultType univs) :=
    hrhsEq ▸ zeroT2RegisteredDefEq univs
  let action : Pattern.Action ([] : List SExpr) rgen
      (zeroT2Redex univs) [zeroT2U2 univs] mcap
      (zeroT2ResultType univs) := {
    pat := hpat
    matched := hmatch'
    dfs := []
    defeqs := by rfl
    checked := by simp
    sound := hsound }
  rw [hrhsEq]
  exact action.typedWHRedS

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.zeroT2Registered_typedWHRedS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms zeroT2Registered_typedWHRedS

/-- The concrete Nat-zero redex is directly self-related at the informative T2
observation.  Both sides take the same clean registered iota edge, after which
the generated RHS certificate supplies the semantic leaf. -/
theorem zeroT2Redex_directSelf (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    (LRD ([] : List SExpr)).DefEq
      (zeroT2Redex univs) (zeroT2Redex univs)
      (zeroT2ResultType univs)
      (zeroT2TermShape univs) (zeroT2TypeShape univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  have hTy := zeroT2ResultType_directSelf univs
  have hStep := zeroT2Registered_typedWHRedS univs
  exact (LRD.DefEq.whr hTy hStep hStep).2
    (zeroT2GeneratedApplication_directSelf univs)

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.zeroT2Redex_directSelf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleRhsV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms zeroT2Redex_directSelf

/-! ## F1/T2 fixed successor witness -/

/-- The predecessor selected by the fixed successor witness. -/
def succT2Pred (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact .const ``Nat.zero []

/-- The constructor-headed major `Nat.succ Nat.zero`. -/
def succT2Major (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact (SExpr.const ``Nat.succ []).app (succT2Pred univs)

/-- The closed successor redex reuses the fixed zero motive and minors. -/
def succT2Redex (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact ((((SExpr.const ``Nat.rec [zeroT2U2 univs]).app
    (zeroT2Motive univs)).app (zeroT2ZeroMinor univs)).app
      (zeroT2SuccMinor univs)).app (succT2Major univs)

def succT2ResultType (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact (zeroT2Motive univs).app (succT2Major univs)

def succT2ReducedResultType (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact .sort (zeroT2U1 univs)

/-- The literal generated successor body after its four outer beta steps. -/
def succT2GeneratedContractum (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact ((zeroT2SuccMinor univs).app (succT2Pred univs)).app
    (zeroT2Redex univs)

/-- Literal capture valuation for the generated successor descriptor. -/
def succT2Capture (univs : Nat) :
    (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path →
      @SExpr (natParams univs) := by
  intro path
  rcases path with path | path
  · rcases path with _ | path
    · exact zeroT2SuccMinor univs
    · rcases path with _ | path
      · exact zeroT2ZeroMinor univs
      · rcases path with _ | path
        · exact zeroT2Motive univs
        · exact path.elim
  · rcases path with _ | path
    · exact succT2Pred univs
    · exact path.elim

@[simp] theorem succT2Capture_motive (univs : Nat) :
    succT2Capture univs natSuccMotivePath = zeroT2Motive univs := rfl

@[simp] theorem succT2Capture_zeroMinor (univs : Nat) :
    succT2Capture univs natSuccZeroMinorPath = zeroT2ZeroMinor univs := rfl

@[simp] theorem succT2Capture_minor (univs : Nat) :
    succT2Capture univs natSuccMinorPath = zeroT2SuccMinor univs := rfl

@[simp] theorem succT2Capture_pred (univs : Nat) :
    succT2Capture univs natSuccPredPath = succT2Pred univs := rfl

def succT2GeneratedApplication (univs : Nat) :
    @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact (NatGeneration.ruleRHS natRuleClosure
    probeNatFlatCtorSucc_lookup).applyS [zeroT2U2 univs]
      (succT2Capture univs)

/-- Strong validity of the literal successor-rule type.  The common motive
and minor binders are recovered from the clean zero certificate; only the
predecessor binder and successor result are added. -/
theorem succT2RuleTypeStrong (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    ∃ u, IsDefEqStrong ([] : List SExpr)
      (probeNatSuccRuleType univs (zeroT2U2 univs))
      (probeNatSuccRuleType univs (zeroT2U2 univs)) (.sort u) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  let level : SLevel := zeroT2U2 univs
  let NatS : SExpr := .const ``Nat []
  let Motive : SExpr := .forallE NatS (.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    .forallE NatS <| .forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
      (SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Result : SExpr :=
    (SExpr.bvar 3).app
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  let G1 : List SExpr := [Motive]
  let G2 : List SExpr := MinorZero :: G1
  let G3 : List SExpr := MinorSucc :: G2
  let G4 : List SExpr := NatS :: G3
  obtain ⟨zeroSort, hZeroRule0⟩ := zeroT2RuleTypeStrong univs
  have hZeroRule : IsDefEqStrong ([] : List SExpr)
      (.forallE Motive (.forallE MinorZero
        (.forallE MinorSucc
          ((SExpr.bvar 2).app (SExpr.const ``Nat.zero [])))))
      (.forallE Motive (.forallE MinorZero
        (.forallE MinorSucc
          ((SExpr.bvar 2).app (SExpr.const ``Nat.zero [])))))
      (.sort zeroSort) := by
    simpa [probeNatZeroRuleType, level, Motive, MinorZero, MinorSucc,
      NatS] using hZeroRule0
  obtain ⟨⟨motiveSort, hMotiveType⟩, _, hRest1⟩ :=
    hZeroRule.forallE_inv' (.inl rfl)
  obtain ⟨⟨minorZeroSort, hMinorZeroType⟩, _, hRest2⟩ :=
    hRest1.forallE_inv' (.inl rfl)
  obtain ⟨⟨minorSuccSort, hMinorSuccType⟩, _, _⟩ :=
    hRest2.forallE_inv' (.inl rfl)
  let natSort : SLevel := SLevel.instV [] VLevel.zero.succ
  have natType (Γ : List SExpr) :
      IsDefEqStrong Γ NatS NatS (.sort natSort) := by
    have h := natTypeStrong univs Γ
    change IsDefEqStrong Γ NatS NatS
      (SExpr.mkInst [] InductiveFixtures.natType.type) at h
    rw [probeNatTypeTypeV_eq] at h
    simpa [NatS, natSort, SExpr.mkInst] using h
  have hMotiveG4 : IsDefEqStrong G4
      (.bvar 3) (.bvar 3) Motive := by
    have hLookup : Lookup G4 3 Motive.lift.lift.lift.lift :=
      .succ (.succ (.succ .zero))
    have W : Ctx.Lift' (.skip (.skip (.skip (.skip .refl))))
        ([] : List SExpr) G4 := .skip (.skip (.skip (.skip .refl)))
    have h := IsDefEqStrong.bvar hLookup
      (natStrongWeak univs W hMotiveType)
    simpa [G4, G3, G2, G1, Motive, NatS,
      SExpr.lift, SExpr.lift'] using h
  have hPred : IsDefEqStrong G4 (.bvar 0) (.bvar 0) NatS := by
    have hLookup : Lookup G4 0 NatS.lift := .zero
    have h := IsDefEqStrong.bvar hLookup (natType G4)
    simpa [G4, G3, G2, G1, NatS, SExpr.lift, SExpr.lift'] using h
  have hSuccPred : IsDefEqStrong G4
      ((SExpr.const ``Nat.succ []).app (.bvar 0))
      ((SExpr.const ``Nat.succ []).app (.bvar 0)) NatS := by
    simpa [NatS, SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natType G4) (natType (NatS :: G4))
        (natSuccStrong univs G4) hPred (natType G4)
  have hResult : IsDefEqStrong G4 Result Result (.sort level) := by
    simpa [Result, Motive, NatS, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natType G4) .sort hMotiveG4 hSuccPred .sort
  have hAfterPred : IsDefEqStrong G3
      (.forallE NatS Result) (.forallE NatS Result)
      (.sort (natSort.imax level)) :=
    .forallEDF (natType G3) hResult hResult
  have hAfterSucc : IsDefEqStrong G2
      (.forallE MinorSucc (.forallE NatS Result))
      (.forallE MinorSucc (.forallE NatS Result))
      (.sort (minorSuccSort.imax (natSort.imax level))) :=
    .forallEDF hMinorSuccType hAfterPred hAfterPred
  have hAfterZero : IsDefEqStrong G1
      (.forallE MinorZero (.forallE MinorSucc (.forallE NatS Result)))
      (.forallE MinorZero (.forallE MinorSucc (.forallE NatS Result)))
      (.sort (minorZeroSort.imax
        (minorSuccSort.imax (natSort.imax level)))) :=
    .forallEDF hMinorZeroType hAfterSucc hAfterSucc
  have hRule : IsDefEqStrong ([] : List SExpr)
      (.forallE Motive
        (.forallE MinorZero (.forallE MinorSucc (.forallE NatS Result))))
      (.forallE Motive
        (.forallE MinorZero (.forallE MinorSucc (.forallE NatS Result))))
      (.sort (motiveSort.imax (minorZeroSort.imax
        (minorSuccSort.imax (natSort.imax level))))) :=
    .forallEDF hMotiveType hAfterZero hAfterZero
  refine ⟨motiveSort.imax (minorZeroSort.imax
    (minorSuccSort.imax (natSort.imax level))), ?_⟩
  simpa [probeNatSuccRuleType, level, Motive, MinorZero, MinorSucc,
    Result, NatS] using hRule

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.succT2RuleTypeStrong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms succT2RuleTypeStrong

/-- The fixed successor redex is definitionally equal to its generated RHS.
As in the zero proof, the generated LHS beta tower is typed locally and then
composed with the primitive registered head equality. -/
theorem succT2RegisteredDefEq (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    IsDefEq ([] : List SExpr)
      (succT2Redex univs) (succT2GeneratedApplication univs)
      (succT2ResultType univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  let level : SLevel := zeroT2U2 univs
  let NatS : SExpr := SExpr.const ``Nat []
  let MotiveTy : SExpr := .forallE NatS (.sort level)
  let ZeroTy : SExpr := (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let SuccTy : SExpr :=
    .forallE NatS <| .forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
      (SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Result : SExpr :=
    (SExpr.bvar 3).app
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  let G1 : List SExpr := [MotiveTy]
  let G2 : List SExpr := ZeroTy :: G1
  let G3 : List SExpr := SuccTy :: G2
  let G4 : List SExpr := NatS :: G3
  let Redex : SExpr :=
    ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3)).app
      (SExpr.bvar 2)).app (SExpr.bvar 1)).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  obtain ⟨ruleSort, hRule0⟩ := succT2RuleTypeStrong univs
  have hRule : IsDefEqStrong ([] : List SExpr)
      (.forallE MotiveTy (.forallE ZeroTy
        (.forallE SuccTy (.forallE NatS Result))))
      (.forallE MotiveTy (.forallE ZeroTy
        (.forallE SuccTy (.forallE NatS Result))))
      (.sort ruleSort) := by
    simpa [probeNatSuccRuleType, level, MotiveTy, ZeroTy, SuccTy,
      Result, NatS] using hRule0
  obtain ⟨⟨_, _hMotiveTy⟩, _, hRest1⟩ :=
    hRule.forallE_inv' (.inl rfl)
  obtain ⟨⟨_, hZeroTy⟩, _, hRest2⟩ :=
    hRest1.forallE_inv' (.inl rfl)
  obtain ⟨⟨_, hSuccTy⟩, _, hRest3⟩ :=
    hRest2.forallE_inv' (.inl rfl)
  obtain ⟨⟨_, hNatTy⟩, _, _⟩ :=
    hRest3.forallE_inv' (.inl rfl)
  have hBody : IsDefEqStrong G4 Redex Redex Result := by
    simpa [G4, G3, G2, G1, Redex, Result, MotiveTy, ZeroTy,
      SuccTy, NatS, level] using
      natSuccRuleBodyStrong univs (Gamma := []) level
        ⟨ruleSort, hRule0⟩
  have hLamN : IsDefEq G3
      (.lam NatS Redex) (.lam NatS Redex)
      (.forallE NatS Result) := by
    exact .lamDF hNatTy.defeq hBody.defeq
  have hLamS : IsDefEq G2
      (.lam SuccTy (.lam NatS Redex))
      (.lam SuccTy (.lam NatS Redex))
      (.forallE SuccTy (.forallE NatS Result)) := by
    exact .lamDF hSuccTy.defeq hLamN
  have hLamZ : IsDefEq G1
      (.lam ZeroTy (.lam SuccTy (.lam NatS Redex)))
      (.lam ZeroTy (.lam SuccTy (.lam NatS Redex)))
      (.forallE ZeroTy (.forallE SuccTy (.forallE NatS Result))) := by
    exact .lamDF hZeroTy.defeq hLamS
  have hMotive : IsDefEq ([] : List SExpr)
      (zeroT2Motive univs) (zeroT2Motive univs) MotiveTy := by
    simpa [MotiveTy, NatS, level] using
      (zeroT2MotiveStrong univs).defeq
  have hZero : IsDefEq ([] : List SExpr)
      (zeroT2ZeroMinor univs) (zeroT2ZeroMinor univs)
      (zeroT2ResultType univs) :=
    (zeroT2ResultType_typedBeta univs).defeq.symm.defeqDF
      (by simpa [zeroT2ReducedResultType] using
        zeroT2ZeroMinorTyped univs)
  have hSucc : IsDefEq ([] : List SExpr)
      (zeroT2SuccMinor univs) (zeroT2SuccMinor univs)
      (zeroT2SuccMinorType univs) :=
    zeroT2SuccMinorTyped univs
  have hPred : IsDefEq ([] : List SExpr)
      (succT2Pred univs) (succT2Pred univs) NatS := by
    simpa [succT2Pred, NatS] using (natZeroStrong univs []).defeq
  have Wm : Ctx.Subst (fun Γ e A => IsDefEq Γ e e A)
      ([] : List SExpr) (.one (zeroT2Motive univs)) (MotiveTy :: []) :=
    Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar hMotive
  have Wmz : Ctx.Subst (fun Γ e A => IsDefEq Γ e e A)
      ([] : List SExpr)
      ((Subst.one (zeroT2Motive univs)).cons (zeroT2ZeroMinor univs))
      (ZeroTy :: MotiveTy :: []) := by
    apply Wm.cons'
    simpa [ZeroTy, MotiveTy, NatS, zeroT2ResultType,
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.id] using hZero
  have Wmzs : Ctx.Subst (fun Γ e A => IsDefEq Γ e e A)
      ([] : List SExpr)
      (((Subst.one (zeroT2Motive univs)).cons (zeroT2ZeroMinor univs)).cons
        (zeroT2SuccMinor univs))
      (SuccTy :: ZeroTy :: MotiveTy :: []) := by
    apply Wmz.cons'
    simpa [SuccTy, ZeroTy, MotiveTy, NatS, zeroT2SuccMinorType,
      zeroT2Motive, SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using hSucc
  have hStep1Raw := IsDefEq.beta hLamZ hMotive
  have hStep1 := IsDefEq.appDF
    (IsDefEq.appDF (IsDefEq.appDF hStep1Raw hZero) hSucc) hPred
  have hLamSC := hLamS.subst
    (Wm.lift IsDefEq.weakCore IsDefEq.bvar (A := ZeroTy))
  have hStep2Raw := IsDefEq.beta hLamSC hZero
  have hStep2 := IsDefEq.appDF
    (IsDefEq.appDF hStep2Raw hSucc) hPred
  have hLamNC := hLamN.subst
    (Wmz.lift IsDefEq.weakCore IsDefEq.bvar (A := SuccTy))
  have hStep3Raw := IsDefEq.beta hLamNC hSucc
  have hStep3 := IsDefEq.appDF hStep3Raw hPred
  have hBodyC := hBody.defeq.subst
    (Wmzs.lift IsDefEq.weakCore IsDefEq.bvar (A := NatS))
  have hStep4 := IsDefEq.beta hBodyC hPred
  have hLhsBeta : IsDefEq ([] : List SExpr)
      ((((((SExpr.lam MotiveTy (SExpr.lam ZeroTy
        (SExpr.lam SuccTy (SExpr.lam NatS Redex)))).app
        (zeroT2Motive univs)).app (zeroT2ZeroMinor univs)).app
          (zeroT2SuccMinor univs)).app (succT2Pred univs)))
      (succT2Redex univs) (succT2ResultType univs) := by
    have h := hStep1.trans (hStep2.trans (hStep3.trans hStep4))
    simpa [Redex, Result, MotiveTy, ZeroTy, SuccTy, NatS, level,
      succT2Redex, succT2ResultType, succT2Major, succT2Pred,
      zeroT2Motive, zeroT2ZeroMinor, zeroT2SuccMinor, zeroT2SuccMinorType,
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      Subst.id] using h
  have hHead : IsDefEq ([] : List SExpr)
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs)
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (probeNatSuccRuleType univs level) := by
    rw [← probeNatSuccRuleTypeS_eq]
    exact IsDefEq.extra (Γ := ([] : List SExpr))
      (natRule_registered probeNatFlatCtorSucc_lookup) rfl
  have hHeadApplied0 := IsDefEq.appDF hHead hMotive
  have hHeadApplied1 := IsDefEq.appDF hHeadApplied0 hZero
  have hHeadApplied2 := IsDefEq.appDF hHeadApplied1 hSucc
  have hHeadApplied3 := IsDefEq.appDF hHeadApplied2 hPred
  have hHeadApplied : IsDefEq ([] : List SExpr)
      (SExpr.app
        (SExpr.app
          (SExpr.app
            (SExpr.app
              (SExpr.mkInst [level]
                (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs)
              (zeroT2Motive univs))
            (zeroT2ZeroMinor univs))
          (zeroT2SuccMinor univs))
        (succT2Pred univs))
      (succT2GeneratedApplication univs)
      (succT2ResultType univs) := by
    rw [succT2GeneratedApplication, natSuccRuleRHS_applyS]
    simpa [MotiveTy, ZeroTy, SuccTy, Result, NatS, level,
      succT2ResultType, succT2Major, succT2Pred, zeroT2Motive,
      zeroT2SuccMinorType, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.lift, Subst.id] using hHeadApplied3
  have hLhsEq : SExpr.mkInst [level]
      (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs =
      SExpr.lam MotiveTy (SExpr.lam ZeroTy
        (SExpr.lam SuccTy (SExpr.lam NatS Redex))) := by
    rw [probeNatSuccRuleLhsV_eq]
    rfl
  rw [hLhsEq] at hHeadApplied
  exact hLhsBeta.symm.trans hHeadApplied

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.succT2RegisteredDefEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms succT2RegisteredDefEq

/-- The real generated successor RHS performs its four outer beta steps while
retaining the recursive `Nat.rec` call.  The call is typed from the clean zero
rule telescope and the concrete recursor constant, not from registered-RHS
semantic lookup. -/
theorem succT2GeneratedApplication_typedBeta (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    TypedWHRedS ([] : List SExpr)
      (succT2GeneratedApplication univs)
      (succT2GeneratedContractum univs)
      (succT2ResultType univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  let level : SLevel := zeroT2U2 univs
  let NatS : SExpr := SExpr.const ``Nat []
  let MotiveTy : SExpr := .forallE NatS (.sort level)
  let ZeroTy : SExpr := (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let SuccTy : SExpr :=
    .forallE NatS <| .forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
      (SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Result : SExpr :=
    (SExpr.bvar 3).app
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  let G1 : List SExpr := [MotiveTy]
  let G2 : List SExpr := ZeroTy :: G1
  let G3 : List SExpr := SuccTy :: G2
  let G4 : List SExpr := NatS :: G3
  let RecResult : SExpr := (SExpr.bvar 3).app (SExpr.bvar 0)
  let RecCall : SExpr :=
    ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3)).app
      (SExpr.bvar 2)).app (SExpr.bvar 1)).app (SExpr.bvar 0)
  let Body : SExpr :=
    ((SExpr.bvar 1).app (SExpr.bvar 0)).app RecCall
  obtain ⟨ruleSort, hRule0⟩ := succT2RuleTypeStrong univs
  have hRule : IsDefEqStrong ([] : List SExpr)
      (.forallE MotiveTy (.forallE ZeroTy
        (.forallE SuccTy (.forallE NatS Result))))
      (.forallE MotiveTy (.forallE ZeroTy
        (.forallE SuccTy (.forallE NatS Result))))
      (.sort ruleSort) := by
    simpa [probeNatSuccRuleType, level, MotiveTy, ZeroTy, SuccTy,
      Result, NatS] using hRule0
  obtain ⟨⟨_, _hMotiveTy⟩, _, hRest1⟩ :=
    hRule.forallE_inv' (.inl rfl)
  obtain ⟨⟨_, hZeroTy⟩, _, hRest2⟩ :=
    hRest1.forallE_inv' (.inl rfl)
  obtain ⟨⟨_, hSuccTy⟩, _, hRest3⟩ :=
    hRest2.forallE_inv' (.inl rfl)
  obtain ⟨⟨_, hNatTy⟩, _, _⟩ :=
    hRest3.forallE_inv' (.inl rfl)
  obtain ⟨zeroRuleSort, hZeroRule0⟩ := zeroT2RuleTypeStrong univs
  let rho4 : Lift := .skip (.skip (.skip (.skip .refl)))
  have W4 : Ctx.Lift' rho4 ([] : List SExpr) G4 :=
    .skip (.skip (.skip (.skip .refl)))
  have hZeroRuleG4 : IsDefEqStrong G4
      (probeNatZeroRuleType univs level)
      (probeNatZeroRuleType univs level) (.sort zeroRuleSort) := by
    have h := natStrongWeak univs W4 hZeroRule0
    simpa [rho4, probeNatZeroRuleType, level, MotiveTy, ZeroTy,
      SuccTy, NatS, SExpr.lift, SExpr.lift'] using h
  have hRec0 := natRecStrongOfZeroRuleType univs (Gamma := G4) level
    ⟨zeroRuleSort, hZeroRuleG4⟩
  have hRec : IsDefEq G4
      (SExpr.const ``Nat.rec [level]) (SExpr.const ``Nat.rec [level])
      (.forallE MotiveTy (.forallE ZeroTy
        (.forallE SuccTy (.forallE NatS RecResult)))) := by
    have h := hRec0.defeq
    rw [probeNatRecTypeV_eq] at h
    simpa [probeNatRecTypeV, MotiveTy, ZeroTy, SuccTy, RecResult,
      NatS, level, SExpr.mkInst, probeInstVParamZero] using h
  have hP : IsDefEq G4 (.bvar 3) (.bvar 3) MotiveTy := by
    have hLookup : Lookup G4 3 MotiveTy.lift.lift.lift.lift :=
      .succ (.succ (.succ .zero))
    simpa [G4, G3, G2, G1, MotiveTy, NatS,
      SExpr.lift, SExpr.lift'] using (IsDefEq.bvar hLookup)
  have hZ : IsDefEq G4 (.bvar 2) (.bvar 2)
      ((SExpr.bvar 3).app (SExpr.const ``Nat.zero [])) := by
    have hLookup : Lookup G4 2 ZeroTy.lift.lift.lift :=
      .succ (.succ .zero)
    simpa [G4, G3, G2, G1, ZeroTy, SExpr.lift, SExpr.lift'] using
      (IsDefEq.bvar hLookup)
  have hS : IsDefEq G4 (.bvar 1) (.bvar 1)
      (.forallE NatS <|
        .forallE ((SExpr.bvar 4).app (SExpr.bvar 0)) <|
          (SExpr.bvar 5).app
            ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))) := by
    have hLookup : Lookup G4 1 SuccTy.lift.lift := .succ .zero
    simpa [G4, G3, G2, G1, SuccTy, NatS,
      SExpr.lift, SExpr.lift'] using (IsDefEq.bvar hLookup)
  have hPred : IsDefEq G4 (.bvar 0) (.bvar 0) NatS := by
    have hLookup : Lookup G4 0 NatS.lift := .zero
    simpa [G4, G3, G2, G1, NatS, SExpr.lift, SExpr.lift'] using
      (IsDefEq.bvar hLookup)
  have hRecCall0 := IsDefEq.appDF
    (IsDefEq.appDF (IsDefEq.appDF (IsDefEq.appDF hRec hP) hZ) hS) hPred
  have hRecCall : IsDefEq G4 RecCall RecCall RecResult := by
    simpa [RecCall, RecResult, MotiveTy, ZeroTy, SuccTy, NatS,
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      Subst.id, probeCancelUnderOne, probeCancelUnderTwo] using hRecCall0
  have hSPred0 := IsDefEq.appDF hS hPred
  have hSPred : IsDefEq G4
      ((SExpr.bvar 1).app (SExpr.bvar 0))
      ((SExpr.bvar 1).app (SExpr.bvar 0))
      (.forallE RecResult <|
        (SExpr.bvar 4).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))) := by
    simpa [RecResult, Result, MotiveTy, NatS, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id,
      probeCancelUnderOne, probeCancelUnderTwo] using hSPred0
  have hBody : IsDefEq G4 Body Body Result := by
    simpa [Body, Result, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.lift, Subst.id] using
      IsDefEq.appDF hSPred hRecCall
  have hLamN : IsDefEq G3
      (.lam NatS Body) (.lam NatS Body) (.forallE NatS Result) := by
    exact .lamDF hNatTy.defeq hBody
  have hLamS : IsDefEq G2
      (.lam SuccTy (.lam NatS Body)) (.lam SuccTy (.lam NatS Body))
      (.forallE SuccTy (.forallE NatS Result)) := by
    exact .lamDF hSuccTy.defeq hLamN
  have hLamZ : IsDefEq G1
      (.lam ZeroTy (.lam SuccTy (.lam NatS Body)))
      (.lam ZeroTy (.lam SuccTy (.lam NatS Body)))
      (.forallE ZeroTy (.forallE SuccTy (.forallE NatS Result))) := by
    exact .lamDF hZeroTy.defeq hLamS
  have hMotive : IsDefEq ([] : List SExpr)
      (zeroT2Motive univs) (zeroT2Motive univs) MotiveTy := by
    simpa [MotiveTy, NatS, level] using
      (zeroT2MotiveStrong univs).defeq
  have hZero : IsDefEq ([] : List SExpr)
      (zeroT2ZeroMinor univs) (zeroT2ZeroMinor univs)
      (zeroT2ResultType univs) :=
    (zeroT2ResultType_typedBeta univs).defeq.symm.defeqDF
      (by simpa [zeroT2ReducedResultType] using
        zeroT2ZeroMinorTyped univs)
  have hSucc : IsDefEq ([] : List SExpr)
      (zeroT2SuccMinor univs) (zeroT2SuccMinor univs)
      (zeroT2SuccMinorType univs) :=
    zeroT2SuccMinorTyped univs
  have hPredC : IsDefEq ([] : List SExpr)
      (succT2Pred univs) (succT2Pred univs) NatS := by
    simpa [succT2Pred, NatS] using (natZeroStrong univs []).defeq
  have Wm : Ctx.Subst (fun Γ e A => IsDefEq Γ e e A)
      ([] : List SExpr) (.one (zeroT2Motive univs)) (MotiveTy :: []) :=
    Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar hMotive
  have Wmz : Ctx.Subst (fun Γ e A => IsDefEq Γ e e A)
      ([] : List SExpr)
      ((Subst.one (zeroT2Motive univs)).cons (zeroT2ZeroMinor univs))
      (ZeroTy :: MotiveTy :: []) := by
    apply Wm.cons'
    simpa [ZeroTy, MotiveTy, NatS, zeroT2ResultType,
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.id] using hZero
  have Wmzs : Ctx.Subst (fun Γ e A => IsDefEq Γ e e A)
      ([] : List SExpr)
      (((Subst.one (zeroT2Motive univs)).cons (zeroT2ZeroMinor univs)).cons
        (zeroT2SuccMinor univs))
      (SuccTy :: ZeroTy :: MotiveTy :: []) := by
    apply Wmz.cons'
    simpa [SuccTy, ZeroTy, MotiveTy, NatS, zeroT2SuccMinorType,
      zeroT2Motive, SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using hSucc
  have hStep1Raw := TypedWHRedS.beta hLamZ hMotive
  have hStep1 := ((hStep1Raw.app hZero).app hSucc).app hPredC
  have hLamSC := hLamS.subst
    (Wm.lift IsDefEq.weakCore IsDefEq.bvar (A := ZeroTy))
  have hStep2Raw := TypedWHRedS.beta hLamSC hZero
  have hStep2 := (hStep2Raw.app hSucc).app hPredC
  have hLamNC := hLamN.subst
    (Wmz.lift IsDefEq.weakCore IsDefEq.bvar (A := SuccTy))
  have hStep3Raw := TypedWHRedS.beta hLamNC hSucc
  have hStep3 := hStep3Raw.app hPredC
  have hBodyC := hBody.subst
    (Wmzs.lift IsDefEq.weakCore IsDefEq.bvar (A := NatS))
  have hStep4 := TypedWHRedS.beta hBodyC hPredC
  have hAll : TypedWHRedS ([] : List SExpr)
      ((((probeNatSuccRuleRhs univs level).app (zeroT2Motive univs)).app
        (zeroT2ZeroMinor univs)).app (zeroT2SuccMinor univs) |>.app
          (succT2Pred univs))
      (succT2GeneratedContractum univs)
      (succT2ResultType univs) := by
    have h := hStep1.trans (hStep2.trans (hStep3.trans hStep4))
    simpa [probeNatSuccRuleRhs, Body, RecCall, RecResult, Result,
      MotiveTy, ZeroTy, SuccTy, NatS, level, succT2GeneratedContractum,
      succT2Redex, succT2ResultType, succT2Major, succT2Pred, zeroT2Redex,
      zeroT2Motive, zeroT2ZeroMinor, zeroT2SuccMinor,
      zeroT2SuccMinorType, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.lift, Subst.id] using h
  rw [succT2GeneratedApplication, natSuccRuleRHS_applyS,
    probeNatSuccRuleRhsS_eq]
  exact hAll

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.succT2GeneratedApplication_typedBeta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleRhsV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms succT2GeneratedApplication_typedBeta

/-- The successor result type is the same constant-motive beta redex at the
constructor-headed major. -/
theorem succT2ResultType_typedBeta (univs : Nat) :
    letI : Params := natParams univs
    TypedWHRedS ([] : List SExpr)
      (succT2ResultType univs) (succT2ReducedResultType univs)
      (.sort (zeroT2U2 univs)) := by
  letI : Params := natParams univs
  have hMajor : IsDefEq ([] : List SExpr)
      (succT2Major univs) (succT2Major univs) (.const ``Nat []) := by
    simpa [succT2Major, succT2Pred, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.id] using
      IsDefEq.appDF (natSuccStrong univs []).defeq
        (natZeroStrong univs []).defeq
  have h := TypedWHRedS.beta (Γ := ([] : List SExpr))
    (A := SExpr.const ``Nat [])
    (body := SExpr.sort (zeroT2U1 univs))
    (B := SExpr.sort (zeroT2U2 univs))
    (arg := succT2Major univs)
    IsDefEqStrong.sort.defeq hMajor
  simpa [succT2ResultType, succT2ReducedResultType, zeroT2Motive,
    SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.id] using h

/-- The constant successor minor consumes both the predecessor and the exact
recursive zero redex, then reaches the selected sort through two typed beta
steps. -/
theorem succT2GeneratedContractum_typedBeta (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    TypedWHRedS ([] : List SExpr)
      (succT2GeneratedContractum univs) (zeroT2ZeroMinor univs)
      (succT2ResultType univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  let NatS : SExpr := .const ``Nat []
  let Motive : SExpr := zeroT2Motive univs
  let G1 : List SExpr := [NatS]
  let Domain : SExpr := Motive.app (.bvar 0)
  let G2 : List SExpr := [Domain, NatS]
  let SuccN : SExpr := (SExpr.const ``Nat.succ []).app (.bvar 1)
  have hn : IsDefEq G1 (.bvar 0) (.bvar 0) NatS := by
    simpa [G1, NatS, SExpr.lift, SExpr.lift'] using
      (IsDefEq.bvar (.zero : Lookup G1 0 NatS.lift))
  have hSortBody1 : IsDefEq (NatS :: G1)
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U1 univs))
      (.sort (zeroT2U2 univs)) := by
    simpa [zeroT2U2, zeroT2U1] using
      (IsDefEq.sort (Γ := NatS :: G1) (l := zeroT2U1 univs))
  have hDomainBeta : IsDefEq G1 Domain
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U2 univs)) := by
    simpa [Domain, Motive, zeroT2Motive, NatS, SExpr.inst,
      SExpr.subst, Subst.one, Subst.cons, Subst.id] using
      (IsDefEq.beta hSortBody1 hn)
  have hDomain : IsDefEq G1 Domain Domain
      (.sort (zeroT2U2 univs)) := hDomainBeta.hasType.1
  have hnG2 : IsDefEq G2 (.bvar 1) (.bvar 1) NatS := by
    simpa [G2, Domain, G1, NatS, SExpr.lift, SExpr.lift'] using
      (IsDefEq.bvar (.succ (.zero : Lookup G1 0 NatS.lift)))
  have hSuccN : IsDefEq G2 SuccN SuccN NatS := by
    simpa [SuccN, NatS, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.id] using
      (IsDefEq.appDF (natSuccStrong univs G2).defeq hnG2)
  have hSortBody2 : IsDefEq (NatS :: G2)
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U1 univs))
      (.sort (zeroT2U2 univs)) := by
    simpa [zeroT2U2, zeroT2U1] using
      (IsDefEq.sort (Γ := NatS :: G2) (l := zeroT2U1 univs))
  have hCodBeta : IsDefEq G2 (Motive.app SuccN)
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U2 univs)) := by
    simpa [Motive, zeroT2Motive, NatS, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.id] using
      (IsDefEq.beta hSortBody2 hSuccN)
  have hSort0 : IsDefEq G2
      (.sort (zeroT2U0 univs)) (.sort (zeroT2U0 univs))
      (.sort (zeroT2U1 univs)) := by
    simpa [zeroT2U1] using
      (IsDefEq.sort (Γ := G2) (l := zeroT2U0 univs))
  have hBody : IsDefEq G2
      (.sort (zeroT2U0 univs)) (.sort (zeroT2U0 univs))
      (Motive.app SuccN) := hCodBeta.symm.defeqDF hSort0
  have hInner : IsDefEq G1
      (.lam Domain (.sort (zeroT2U0 univs)))
      (.lam Domain (.sort (zeroT2U0 univs)))
      (.forallE Domain (Motive.app SuccN)) := by
    simpa [G2, Domain, G1] using IsDefEq.lamDF hDomain hBody
  have hPred : IsDefEq ([] : List SExpr)
      (succT2Pred univs) (succT2Pred univs) NatS := by
    simpa [succT2Pred, NatS] using (natZeroStrong univs []).defeq
  have hRec : IsDefEq ([] : List SExpr)
      (zeroT2Redex univs) (zeroT2Redex univs)
      (zeroT2ResultType univs) :=
    (zeroT2RegisteredDefEq univs).hasType.1
  have hStep1Raw := TypedWHRedS.beta hInner hPred
  have hStep1 := hStep1Raw.app hRec
  have hResultWeak0 :=
    (succT2ResultType_typedBeta univs).defeq.weak'
      (Ctx.Lift'.one (A := zeroT2ResultType univs))
  have hResultWeak : IsDefEq (zeroT2ResultType univs :: [])
      (succT2ResultType univs) (succT2ReducedResultType univs)
      (.sort (zeroT2U2 univs)) := by
    simpa [succT2ResultType, succT2ReducedResultType, succT2Major,
      succT2Pred, zeroT2Motive, SExpr.lift, SExpr.lift'] using
      hResultWeak0
  have hSort0Weak : IsDefEq (zeroT2ResultType univs :: [])
      (.sort (zeroT2U0 univs)) (.sort (zeroT2U0 univs))
      (succT2ReducedResultType univs) := by
    simpa [succT2ReducedResultType, zeroT2U1] using
      (IsDefEq.sort (Γ := zeroT2ResultType univs :: [])
        (l := zeroT2U0 univs))
  have hBodyC : IsDefEq (zeroT2ResultType univs :: [])
      (.sort (zeroT2U0 univs)) (.sort (zeroT2U0 univs))
      (succT2ResultType univs) := by
    exact hResultWeak.symm.defeqDF hSort0Weak
  have hStep2 := TypedWHRedS.beta hBodyC hRec
  have hAll := hStep1.trans hStep2
  simpa [succT2GeneratedContractum, succT2Pred, succT2ResultType,
    succT2Major, zeroT2Redex, zeroT2Motive, zeroT2ZeroMinor,
    zeroT2SuccMinor, Domain, SuccN, Motive, NatS, SExpr.lift, SExpr.lift',
    SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
    Subst.id] using hAll

def succT2TermShape (univs : Nat) : @WShape (natParams univs) 1 :=
  zeroT2TermShape univs

def succT2TypeShape (univs : Nat) : @WShape (natParams univs) 1 :=
  zeroT2TypeShape univs

/-- The entire generated successor RHS reaches `Sort u0`: four outer betas
followed by the two constant-minor betas. -/
theorem succT2GeneratedApplication_fullTypedBeta (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    TypedWHRedS ([] : List SExpr)
      (succT2GeneratedApplication univs) (zeroT2ZeroMinor univs)
      (succT2ResultType univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  exact (succT2GeneratedApplication_typedBeta univs).trans
    (succT2GeneratedContractum_typedBeta univs)

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.succT2GeneratedApplication_fullTypedBeta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleRhsV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms succT2GeneratedApplication_fullTypedBeta

theorem succT2ShapeTyping (univs : Nat) :
    letI : Params := natParams univs
    (succT2TermShape univs).HasType (succT2TypeShape univs) := by
  letI : Params := natParams univs
  simpa [succT2TermShape, succT2TypeShape] using zeroT2ShapeTyping univs

theorem succT2Shapes_nonbottom (univs : Nat) :
    letI : Params := natParams univs
    ¬(succT2TermShape univs ≤ WShape.bot) ∧
      ¬(succT2TypeShape univs ≤ WShape.bot) := by
  letI : Params := natParams univs
  simpa [succT2TermShape, succT2TypeShape] using
    zeroT2Shapes_nonbottom univs

theorem succT2Redex_ne_contractum (univs : Nat) :
    succT2Redex univs ≠ zeroT2ZeroMinor univs := by
  simp [succT2Redex, succT2Major, succT2Pred, zeroT2ZeroMinor]

/-- Direct validity of the dynamic successor result type, transported
backward from its canonical sort. -/
theorem succT2ResultType_directSelf (univs : Nat) :
    letI : Params := natParams univs
    (LRD ([] : List SExpr)).TyDefEq
      (succT2ResultType univs) (succT2ResultType univs)
      (succT2TypeShape univs) := by
  letI : Params := natParams univs
  have hBeta := succT2ResultType_typedBeta univs
  have hReduced : (LRD ([] : List SExpr)).TyDefEq
      (succT2ReducedResultType univs)
      (succT2ReducedResultType univs) (succT2TypeShape univs) := by
    simpa [succT2ReducedResultType, succT2TypeShape, zeroT2TypeShape] using
      (LRD.TyDefEq.sort (Γ := ([] : List SExpr))
        (u := zeroT2U1 univs) (r := true) (n := 1))
  exact (LRD.TyDefEq.whr hBeta.toTypeWHRedPath
    hBeta.toTypeWHRedPath).2 hReduced

/-- The real generated successor RHS is directly self-related at the fixed
informative observation after its six typed beta edges. -/
theorem succT2GeneratedApplication_directSelf (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    (LRD ([] : List SExpr)).DefEq
      (succT2GeneratedApplication univs)
      (succT2GeneratedApplication univs)
      (succT2ResultType univs)
      (succT2TermShape univs) (succT2TypeShape univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  have hBeta := succT2ResultType_typedBeta univs
  have hTy := succT2ResultType_directSelf univs
  have hReduced : (LRD ([] : List SExpr)).DefEq
      (zeroT2ZeroMinor univs) (zeroT2ZeroMinor univs)
      (succT2ReducedResultType univs)
      (succT2TermShape univs) (succT2TypeShape univs) := by
    simpa [zeroT2ZeroMinor, succT2ReducedResultType, succT2TermShape,
      succT2TypeShape, zeroT2TermShape, zeroT2TypeShape, zeroT2U1] using
      (LRD.DefEq.sort (Γ := ([] : List SExpr))
        (u := zeroT2U0 univs) (r := false) (s := true) (n := 1))
  have hTypeRefl : TypeWHRedPath ([] : List SExpr)
      (succT2ResultType univs) (succT2ResultType univs) :=
    .refl hBeta.defeq.hasType.1
  have hReducedDynamic : (LRD ([] : List SExpr)).TyDefEq
      (succT2ReducedResultType univs) (succT2ResultType univs)
      (succT2TypeShape univs) :=
    (LRD.TyDefEq.whr hBeta.toTypeWHRedPath hTypeRefl).1 hTy
  have hZero : (LRD ([] : List SExpr)).DefEq
      (zeroT2ZeroMinor univs) (zeroT2ZeroMinor univs)
      (succT2ResultType univs)
      (succT2TermShape univs) (succT2TypeShape univs) :=
    LRD.DefEq.conv hReducedDynamic hReduced
  have hApp := succT2GeneratedApplication_fullTypedBeta univs
  exact (LRD.DefEq.whr hTy hApp hApp).2 hZero

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.succT2GeneratedApplication_directSelf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleRhsV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms succT2GeneratedApplication_directSelf

/-- The exact four-capture successor match packages the clean registered
equality as the actual typed weak-head iota edge. -/
theorem succT2Registered_typedWHRedS (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    TypedWHRedS ([] : List SExpr)
      (succT2Redex univs) (succT2GeneratedApplication univs)
      (succT2ResultType univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  let rgen :=
    (NatGeneration.ruleRHS natRuleClosure probeNatFlatCtorSucc_lookup,
      NatGeneration.ruleCheck natRuleClosure
        (List.mem_of_getElem? probeNatFlatCtorSucc_lookup))
  have hpat : NatPat
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1) rgen :=
    .mk probeNatFlatCtorSucc_lookup
  let rule : Pattern.IotaRule rgen := {
    pat := hpat
    df := NatGeneration.rule 1 NatGeneration.flatCtors[1]
    registered := natRule_registered probeNatFlatCtorSucc_lookup
    rhsClosed := natRuleClosure.rhs_closed probeNatFlatCtorSucc_lookup
    capturePaths := natCapturePaths NatGeneration.flatCtors[1]
    rhsTower := natRuleRHS_tower probeNatFlatCtorSucc_lookup }
  obtain ⟨mcap, hmatch⟩ :=
    RecursorIotaPattern.matchesS_spines
      (rargs := [zeroT2SuccMinor univs, zeroT2ZeroMinor univs,
        zeroT2Motive univs])
      (cargs := [succT2Pred univs])
      (rls := [zeroT2U2 univs]) (cls := [])
      (by rfl) (by rfl)
  have hmatch' : (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).MatchesS
      (succT2Redex univs) [zeroT2U2 univs] mcap := by
    simpa [succT2Redex, succT2Major] using hmatch
  obtain ⟨_, _, hcaps⟩ := natSuccCaptureValues univs hmatch
  let AppliedRhs : SExpr :=
    [zeroT2Motive univs, zeroT2ZeroMinor univs,
      zeroT2SuccMinor univs, succT2Pred univs].foldl
      (fun f a => f.app a)
      (SExpr.mkInst [zeroT2U2 univs]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
  have hGenerated : succT2GeneratedApplication univs = AppliedRhs := by
    rw [succT2GeneratedApplication, natSuccRuleRHS_applyS]
    simp [AppliedRhs]
  have hrhsEq : succT2GeneratedApplication univs =
      rgen.1.applyS [zeroT2U2 univs] mcap := by
    calc
      succT2GeneratedApplication univs = AppliedRhs := hGenerated
      _ = (rule.capturePaths.map mcap).foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst [zeroT2U2 univs] rule.df.rhs) := by
        simp [AppliedRhs, rule, hcaps]
      _ = rgen.1.applyS [zeroT2U2 univs] mcap :=
        rule.rhsApply [zeroT2U2 univs] mcap
  have hsound : IsDefEq ([] : List SExpr) (succT2Redex univs)
      (rgen.1.applyS [zeroT2U2 univs] mcap)
      (succT2ResultType univs) :=
    hrhsEq ▸ succT2RegisteredDefEq univs
  let action : Pattern.Action ([] : List SExpr) rgen
      (succT2Redex univs) [zeroT2U2 univs] mcap
      (succT2ResultType univs) := {
    pat := hpat
    matched := hmatch'
    dfs := []
    defeqs := by rfl
    checked := by simp
    sound := hsound }
  rw [hrhsEq]
  exact action.typedWHRedS

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.succT2Registered_typedWHRedS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms succT2Registered_typedWHRedS

/-- The explicit successor redex is directly self-related at the same
informative level-one sort observation as the zero witness. -/
theorem succT2Redex_directSelf (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    (LRD ([] : List SExpr)).DefEq
      (succT2Redex univs) (succT2Redex univs)
      (succT2ResultType univs)
      (succT2TermShape univs) (succT2TypeShape univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  have hTy := succT2ResultType_directSelf univs
  have hStep := succT2Registered_typedWHRedS univs
  exact (LRD.DefEq.whr hTy hStep hStep).2
    (succT2GeneratedApplication_directSelf univs)

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.succT2Redex_directSelf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleRhsV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms succT2Redex_directSelf

/-! ## F1/T3 clean closed strong derivations -/

/-- Structural strong typing data for the two fixed redexes.  This route
rebuilds the concrete dependent recursor spine and deliberately avoids the
generic weak-to-strong bridge, whose Nat closure is not trust-clean. -/
theorem zeroT2MotiveStrongAt (univs : Nat)
    (Γ : List (@SExpr (natParams univs))) :
    letI : Params := natParams univs
    IsDefEqStrong Γ
      (zeroT2Motive univs) (zeroT2Motive univs)
      (.forallE (.const ``Nat []) (.sort (zeroT2U2 univs))) := by
  letI : Params := natParams univs
  have hNat := natTypeStrong univs Γ
  have hBody : IsDefEqStrong
      (SExpr.const ``Nat [] :: Γ)
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U1 univs))
      (.sort (zeroT2U2 univs)) := by
    simpa [zeroT2U2, zeroT2U1] using
      (IsDefEqStrong.sort (Γ := SExpr.const ``Nat [] :: Γ)
        (l := zeroT2U1 univs))
  have hPi : IsDefEqStrong
      (SExpr.const ``Nat [] :: Γ)
      (.sort (zeroT2U2 univs)) (.sort (zeroT2U2 univs))
      (.sort (SLevel.succ (zeroT2U2 univs))) := .sort
  simpa [zeroT2Motive] using
    (IsDefEqStrong.lamDF hNat hPi hPi hBody hBody)

theorem zeroT2Motive_betaStrong (univs : Nat)
    (Γ : List (@SExpr (natParams univs))) {arg : @SExpr (natParams univs)}
    (harg : letI : Params := natParams univs
      IsDefEqStrong Γ arg arg (.const ``Nat [])) :
    letI : Params := natParams univs
    IsDefEqStrong Γ
      ((zeroT2Motive univs).app arg) (.sort (zeroT2U1 univs))
      (.sort (zeroT2U2 univs)) := by
  letI : Params := natParams univs
  have hBody : IsDefEqStrong
      (SExpr.const ``Nat [] :: Γ)
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U1 univs))
      (.sort (zeroT2U2 univs)) := by
    simpa [zeroT2U2, zeroT2U1] using
      (IsDefEqStrong.sort (Γ := SExpr.const ``Nat [] :: Γ)
        (l := zeroT2U1 univs))
  have hCod : IsDefEqStrong
      (SExpr.const ``Nat [] :: Γ)
      (.sort (zeroT2U2 univs)) (.sort (zeroT2U2 univs))
      (.sort (SLevel.succ (zeroT2U2 univs))) := .sort
  have hResult : IsDefEqStrong Γ
      (.sort (zeroT2U2 univs)) (.sort (zeroT2U2 univs))
      (.sort (SLevel.succ (zeroT2U2 univs))) := .sort
  have hApp : IsDefEqStrong Γ
      ((zeroT2Motive univs).app arg)
      ((zeroT2Motive univs).app arg)
      (.sort (zeroT2U2 univs)) := by
    simpa [zeroT2Motive, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.id] using
      IsDefEqStrong.appDF (natTypeStrong univs Γ) hCod
        (zeroT2MotiveStrongAt univs Γ) harg hResult
  have hInst : IsDefEqStrong Γ
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U1 univs))
      (.sort (zeroT2U2 univs)) := by
    simpa [zeroT2U2, zeroT2U1] using
      (IsDefEqStrong.sort (Γ := Γ) (l := zeroT2U1 univs))
  simpa [zeroT2Motive, SExpr.inst, SExpr.subst, Subst.one,
    Subst.cons, Subst.id] using
    IsDefEqStrong.beta hBody harg hApp hInst

theorem zeroT2ResultTypeStrong (univs : Nat) :
    letI : Params := natParams univs
    IsDefEqStrong ([] : List SExpr)
      (zeroT2ResultType univs) (zeroT2ResultType univs)
      (.sort (zeroT2U2 univs)) := by
  letI : Params := natParams univs
  simpa [zeroT2ResultType] using
    (zeroT2Motive_betaStrong univs ([] : List SExpr)
      (natZeroStrong univs [])).hasType.1

theorem zeroT2ZeroMinorStrong (univs : Nat) :
    letI : Params := natParams univs
    IsDefEqStrong ([] : List SExpr)
      (zeroT2ZeroMinor univs) (zeroT2ZeroMinor univs)
      (zeroT2ResultType univs) := by
  letI : Params := natParams univs
  have hBeta := zeroT2Motive_betaStrong univs ([] : List SExpr)
    (natZeroStrong univs [])
  have hSort0 : IsDefEqStrong ([] : List SExpr)
      (.sort (zeroT2U0 univs)) (.sort (zeroT2U0 univs))
      (.sort (zeroT2U1 univs)) := by
    simpa [zeroT2U1] using
      (IsDefEqStrong.sort (Γ := ([] : List SExpr)) (l := zeroT2U0 univs))
  simpa [zeroT2ZeroMinor, zeroT2ResultType] using
    hBeta.symm.defeqDF hSort0

theorem succT2MajorStrong (univs : Nat) :
    letI : Params := natParams univs
    IsDefEqStrong ([] : List SExpr)
      (succT2Major univs) (succT2Major univs) (.const ``Nat []) := by
  letI : Params := natParams univs
  simpa [succT2Major, succT2Pred, SExpr.inst, SExpr.subst,
    Subst.one, Subst.cons, Subst.id] using
    IsDefEqStrong.appDF
      (natTypeStrong univs ([] : List SExpr))
      (natTypeStrong univs [SExpr.const ``Nat []])
      (natSuccStrong univs []) (natZeroStrong univs [])
      (natTypeStrong univs [])

theorem succT2ResultTypeStrong (univs : Nat) :
    letI : Params := natParams univs
    IsDefEqStrong ([] : List SExpr)
      (succT2ResultType univs) (succT2ResultType univs)
      (.sort (zeroT2U2 univs)) := by
  letI : Params := natParams univs
  simpa [succT2ResultType] using
    (zeroT2Motive_betaStrong univs ([] : List SExpr)
      (succT2MajorStrong univs)).hasType.1

theorem zeroT2SuccMinorStrong (univs : Nat) :
    letI : Params := natParams univs
    IsDefEqStrong ([] : List SExpr)
      (zeroT2SuccMinor univs) (zeroT2SuccMinor univs)
      (zeroT2SuccMinorType univs) := by
  letI : Params := natParams univs
  let NatS : SExpr := .const ``Nat []
  let Motive : SExpr := zeroT2Motive univs
  let G1 : List SExpr := [NatS]
  let Domain : SExpr := Motive.app (.bvar 0)
  let G2 : List SExpr := [Domain, NatS]
  let SuccN : SExpr := (SExpr.const ``Nat.succ []).app (.bvar 1)
  have hNat := natTypeStrong univs ([] : List SExpr)
  have hn : IsDefEqStrong G1 (.bvar 0) (.bvar 0) NatS := by
    have h := IsDefEqStrong.bvar
      (.zero : Lookup G1 0 NatS.lift) (natTypeStrong univs G1)
    simpa [G1, NatS, SExpr.lift, SExpr.lift'] using h
  have hDomainBeta : IsDefEqStrong G1 Domain
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U2 univs)) := by
    simpa [Domain, Motive] using
      zeroT2Motive_betaStrong univs G1 hn
  have hDomain : IsDefEqStrong G1 Domain Domain
      (.sort (zeroT2U2 univs)) := hDomainBeta.hasType.1
  have hnG2 : IsDefEqStrong G2 (.bvar 1) (.bvar 1) NatS := by
    have h := IsDefEqStrong.bvar
      (.succ (.zero : Lookup G1 0 NatS.lift)) (natTypeStrong univs G2)
    simpa [G2, Domain, G1, NatS, SExpr.lift, SExpr.lift'] using h
  have hSuccN : IsDefEqStrong G2 SuccN SuccN NatS := by
    simpa [SuccN, NatS, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.id] using
      IsDefEqStrong.appDF (natTypeStrong univs G2)
        (natTypeStrong univs (NatS :: G2))
        (natSuccStrong univs G2) hnG2 (natTypeStrong univs G2)
  have hCodBeta : IsDefEqStrong G2 (Motive.app SuccN)
      (.sort (zeroT2U1 univs)) (.sort (zeroT2U2 univs)) := by
    simpa [Motive] using
      zeroT2Motive_betaStrong univs G2 hSuccN
  have hCod : IsDefEqStrong G2 (Motive.app SuccN)
      (Motive.app SuccN) (.sort (zeroT2U2 univs)) := hCodBeta.hasType.1
  have hSort0 : IsDefEqStrong G2
      (.sort (zeroT2U0 univs)) (.sort (zeroT2U0 univs))
      (.sort (zeroT2U1 univs)) := by
    simpa [zeroT2U1] using
      (IsDefEqStrong.sort (Γ := G2) (l := zeroT2U0 univs))
  have hBody : IsDefEqStrong G2
      (.sort (zeroT2U0 univs)) (.sort (zeroT2U0 univs))
      (Motive.app SuccN) := hCodBeta.symm.defeqDF hSort0
  have hInnerType : IsDefEqStrong G1
      (.forallE Domain (Motive.app SuccN))
      (.forallE Domain (Motive.app SuccN))
      (.sort ((zeroT2U2 univs).imax (zeroT2U2 univs))) :=
    .forallEDF hDomain hCod hCod
  have hInner : IsDefEqStrong G1
      (.lam Domain (.sort (zeroT2U0 univs)))
      (.lam Domain (.sort (zeroT2U0 univs)))
      (.forallE Domain (Motive.app SuccN)) := by
    simpa [G2, Domain, G1] using
      IsDefEqStrong.lamDF hDomain hCod hCod hBody hBody
  have hOuterBody : IsDefEqStrong (NatS :: [])
      (.forallE Domain (Motive.app SuccN))
      (.forallE Domain (Motive.app SuccN))
      (.sort ((zeroT2U2 univs).imax (zeroT2U2 univs))) := by
    simpa [G1] using hInnerType
  simpa [zeroT2SuccMinor, zeroT2SuccMinorType, NatS, Motive,
    Domain, SuccN, G1] using
    IsDefEqStrong.lamDF hNat hOuterBody hOuterBody hInner hInner

theorem zeroT2SuccMinorTypeStrong (univs : Nat) :
    letI : Params := natParams univs
    let natSort : SLevel := SLevel.instV [] VLevel.zero.succ
    IsDefEqStrong ([] : List SExpr)
      (zeroT2SuccMinorType univs) (zeroT2SuccMinorType univs)
      (.sort (natSort.imax
        ((zeroT2U2 univs).imax (zeroT2U2 univs)))) := by
  letI : Params := natParams univs
  let NatS : SExpr := .const ``Nat []
  let Motive : SExpr := zeroT2Motive univs
  let G1 : List SExpr := [NatS]
  let Domain : SExpr := Motive.app (.bvar 0)
  let G2 : List SExpr := [Domain, NatS]
  let SuccN : SExpr := (SExpr.const ``Nat.succ []).app (.bvar 1)
  let natSort : SLevel := SLevel.instV [] VLevel.zero.succ
  have hNat : IsDefEqStrong ([] : List SExpr) NatS NatS
      (.sort natSort) := by
    have h := natTypeStrong univs ([] : List SExpr)
    change IsDefEqStrong ([] : List SExpr) NatS NatS
      (SExpr.mkInst [] InductiveFixtures.natType.type) at h
    rw [probeNatTypeTypeV_eq] at h
    simpa [NatS, natSort, SExpr.mkInst] using h
  have hn : IsDefEqStrong G1 (.bvar 0) (.bvar 0) NatS := by
    have h := IsDefEqStrong.bvar
      (.zero : Lookup G1 0 NatS.lift) (natTypeStrong univs G1)
    simpa [G1, NatS, SExpr.lift, SExpr.lift'] using h
  have hDomain : IsDefEqStrong G1 Domain Domain
      (.sort (zeroT2U2 univs)) := by
    simpa [Domain, Motive] using
      (zeroT2Motive_betaStrong univs G1 hn).hasType.1
  have hnG2 : IsDefEqStrong G2 (.bvar 1) (.bvar 1) NatS := by
    have h := IsDefEqStrong.bvar
      (.succ (.zero : Lookup G1 0 NatS.lift)) (natTypeStrong univs G2)
    simpa [G2, Domain, G1, NatS, SExpr.lift, SExpr.lift'] using h
  have hSuccN : IsDefEqStrong G2 SuccN SuccN NatS := by
    simpa [SuccN, NatS, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.id] using
      IsDefEqStrong.appDF (natTypeStrong univs G2)
        (natTypeStrong univs (NatS :: G2))
        (natSuccStrong univs G2) hnG2 (natTypeStrong univs G2)
  have hCod : IsDefEqStrong G2 (Motive.app SuccN)
      (Motive.app SuccN) (.sort (zeroT2U2 univs)) := by
    simpa [Motive] using
      (zeroT2Motive_betaStrong univs G2 hSuccN).hasType.1
  have hInner : IsDefEqStrong G1
      (.forallE Domain (Motive.app SuccN))
      (.forallE Domain (Motive.app SuccN))
      (.sort ((zeroT2U2 univs).imax (zeroT2U2 univs))) := by
    simpa [G2, Domain, G1] using
      IsDefEqStrong.forallEDF hDomain hCod hCod
  simpa [zeroT2SuccMinorType, NatS, Motive, Domain, SuccN, G1,
    natSort] using IsDefEqStrong.forallEDF hNat hInner hInner

def zeroT2MajorType (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact .forallE (.const ``Nat []) <|
    (zeroT2Motive univs).app (.bvar 0)

def zeroT2RecursorPrefix (univs : Nat) : @SExpr (natParams univs) := by
  letI : Params := natParams univs
  exact (((SExpr.const ``Nat.rec [zeroT2U2 univs]).app
    (zeroT2Motive univs)).app (zeroT2ZeroMinor univs)).app
      (zeroT2SuccMinor univs)

theorem zeroT2MajorTypeStrong (univs : Nat) :
    letI : Params := natParams univs
    let natSort : SLevel := SLevel.instV [] VLevel.zero.succ
    IsDefEqStrong ([] : List SExpr)
      (zeroT2MajorType univs) (zeroT2MajorType univs)
      (.sort (natSort.imax (zeroT2U2 univs))) := by
  letI : Params := natParams univs
  let NatS : SExpr := .const ``Nat []
  let Motive : SExpr := zeroT2Motive univs
  let natSort : SLevel := SLevel.instV [] VLevel.zero.succ
  have hNat : IsDefEqStrong ([] : List SExpr) NatS NatS
      (.sort natSort) := by
    have h := natTypeStrong univs ([] : List SExpr)
    change IsDefEqStrong ([] : List SExpr) NatS NatS
      (SExpr.mkInst [] InductiveFixtures.natType.type) at h
    rw [probeNatTypeTypeV_eq] at h
    simpa [NatS, natSort, SExpr.mkInst] using h
  have hMajor : IsDefEqStrong [NatS]
      (.bvar 0) (.bvar 0) NatS := by
    have h := IsDefEqStrong.bvar
      (.zero : Lookup [NatS] 0 NatS.lift) (natTypeStrong univs [NatS])
    simpa [NatS, SExpr.lift, SExpr.lift'] using h
  have hResult : IsDefEqStrong [NatS]
      (Motive.app (.bvar 0)) (Motive.app (.bvar 0))
      (.sort (zeroT2U2 univs)) := by
    simpa [Motive] using
      (zeroT2Motive_betaStrong univs [NatS] hMajor).hasType.1
  simpa [zeroT2MajorType, NatS, Motive, natSort] using
    IsDefEqStrong.forallEDF hNat hResult hResult

theorem zeroT2RecursorPrefixStrong (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    IsDefEqStrong ([] : List SExpr)
      (zeroT2RecursorPrefix univs)
      (zeroT2RecursorPrefix univs)
      (zeroT2MajorType univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  let level : SLevel := zeroT2U2 univs
  let NatS : SExpr := .const ``Nat []
  let MotiveTy : SExpr := .forallE NatS (.sort level)
  let GenericZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let GenericSucc : SExpr :=
    .forallE NatS <| .forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
      (SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let GenericTail : SExpr :=
    .forallE NatS ((SExpr.bvar 3).app (SExpr.bvar 0))
  let GenericRest : SExpr :=
    .forallE GenericZero (.forallE GenericSucc GenericTail)
  let Motive : SExpr := zeroT2Motive univs
  let ZeroTy : SExpr := zeroT2ResultType univs
  let SuccTy : SExpr := zeroT2SuccMinorType univs
  let MajorTail : SExpr := zeroT2MajorType univs
  let AfterSucc : SExpr := .forallE SuccTy MajorTail.lift
  let AfterZero : SExpr :=
    .forallE ZeroTy (.forallE SuccTy.lift MajorTail.lift.lift)
  let natSort : SLevel := SLevel.instV [] VLevel.zero.succ
  let motiveSort : SLevel := natSort.imax level.succ
  let innerSort : SLevel := level.imax level
  let succSort : SLevel := natSort.imax innerSort
  let majorSort : SLevel := natSort.imax level
  have hRec0 := natRecStrongOfZeroRuleType univs level
    (zeroT2RuleTypeStrong univs)
  rw [probeNatRecTypeV_eq] at hRec0
  have hRec : IsDefEqStrong ([] : List SExpr)
      (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
      (.forallE MotiveTy GenericRest) := by
    simpa [probeNatRecTypeV, SExpr.mkInst, probeInstVParamZero,
      MotiveTy, GenericRest, GenericZero, GenericSucc, GenericTail,
      NatS, level] using hRec0
  have natType (Γ : List SExpr) :
      IsDefEqStrong Γ NatS NatS (.sort natSort) := by
    have h := natTypeStrong univs Γ
    change IsDefEqStrong Γ NatS NatS
      (SExpr.mkInst [] InductiveFixtures.natType.type) at h
    rw [probeNatTypeTypeV_eq] at h
    simpa [NatS, natSort, SExpr.mkInst] using h
  have motiveType (Γ : List SExpr) :
      IsDefEqStrong Γ MotiveTy MotiveTy (.sort motiveSort) := by
    simpa [MotiveTy, motiveSort] using
      IsDefEqStrong.forallEDF (natType Γ)
        (IsDefEqStrong.sort (Γ := NatS :: Γ) (l := level))
        (IsDefEqStrong.sort (Γ := NatS :: Γ) (l := level))
  have hMotiveTy := motiveType ([] : List SExpr)
  let G1 : List SExpr := [MotiveTy]
  have hMotiveG1 : IsDefEqStrong G1
      (.bvar 0) (.bvar 0) MotiveTy := by
    have hLookup : Lookup G1 0 MotiveTy.lift := .zero
    have h := IsDefEqStrong.bvar hLookup (motiveType G1)
    simpa [G1, MotiveTy, NatS, SExpr.lift, SExpr.lift'] using h
  have hGenericZero : IsDefEqStrong G1 GenericZero GenericZero
      (.sort level) := by
    simpa [GenericZero, NatS, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natType G1) .sort hMotiveG1
        (natZeroStrong univs G1) .sort
  let G2 : List SExpr := GenericZero :: G1
  let G3 : List SExpr := NatS :: G2
  let RecDomain : SExpr := (SExpr.bvar 2).app (SExpr.bvar 0)
  have hMotiveG3 : IsDefEqStrong G3
      (.bvar 2) (.bvar 2) MotiveTy := by
    have hLookup : Lookup G3 2 MotiveTy.lift.lift.lift :=
      .succ (.succ .zero)
    have h := IsDefEqStrong.bvar hLookup (motiveType G3)
    simpa [G3, G2, G1, MotiveTy, NatS, SExpr.lift,
      SExpr.lift'] using h
  have hPredG3 : IsDefEqStrong G3 (.bvar 0) (.bvar 0) NatS := by
    have hLookup : Lookup G3 0 NatS.lift := .zero
    have h := IsDefEqStrong.bvar hLookup (natType G3)
    simpa [G3, G2, G1, NatS, SExpr.lift, SExpr.lift'] using h
  have hRecDomain : IsDefEqStrong G3 RecDomain RecDomain
      (.sort level) := by
    simpa [RecDomain, MotiveTy, NatS, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natType G3) .sort hMotiveG3 hPredG3 .sort
  let G4 : List SExpr := RecDomain :: G3
  let SuccN : SExpr :=
    (SExpr.const ``Nat.succ []).app (SExpr.bvar 1)
  let RecCod : SExpr := (SExpr.bvar 3).app SuccN
  have hMotiveG4 : IsDefEqStrong G4
      (.bvar 3) (.bvar 3) MotiveTy := by
    have hLookup : Lookup G4 3 MotiveTy.lift.lift.lift.lift :=
      .succ (.succ (.succ .zero))
    have h := IsDefEqStrong.bvar hLookup (motiveType G4)
    simpa [G4, G3, G2, G1, MotiveTy, NatS, SExpr.lift,
      SExpr.lift'] using h
  have hPredG4 : IsDefEqStrong G4 (.bvar 1) (.bvar 1) NatS := by
    have hLookup : Lookup G4 1 NatS.lift.lift := .succ .zero
    have h := IsDefEqStrong.bvar hLookup (natType G4)
    simpa [G4, G3, G2, G1, NatS, SExpr.lift, SExpr.lift'] using h
  have hSuccN : IsDefEqStrong G4 SuccN SuccN NatS := by
    simpa [SuccN, NatS, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natType G4) (natType (NatS :: G4))
        (natSuccStrong univs G4) hPredG4 (natType G4)
  have hRecCod : IsDefEqStrong G4 RecCod RecCod (.sort level) := by
    simpa [RecCod, MotiveTy, NatS, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natType G4) .sort hMotiveG4 hSuccN .sort
  have hInner : IsDefEqStrong G3
      (.forallE RecDomain RecCod) (.forallE RecDomain RecCod)
      (.sort innerSort) := by
    simpa [innerSort] using
      IsDefEqStrong.forallEDF hRecDomain hRecCod hRecCod
  have hGenericSucc : IsDefEqStrong G2 GenericSucc GenericSucc
      (.sort succSort) := by
    simpa [GenericSucc, RecDomain, RecCod, SuccN, G4, G3, succSort] using
      IsDefEqStrong.forallEDF (natType G2) hInner hInner
  let GTail : List SExpr := GenericSucc :: G2
  have hMotiveTail : IsDefEqStrong (NatS :: GTail)
      (.bvar 3) (.bvar 3) MotiveTy := by
    have hLookup : Lookup (NatS :: GTail) 3
        MotiveTy.lift.lift.lift.lift := .succ (.succ (.succ .zero))
    have h := IsDefEqStrong.bvar hLookup (motiveType (NatS :: GTail))
    simpa [GTail, G2, G1, MotiveTy, NatS, SExpr.lift,
      SExpr.lift'] using h
  have hMajorTailVar : IsDefEqStrong (NatS :: GTail)
      (.bvar 0) (.bvar 0) NatS := by
    have hLookup : Lookup (NatS :: GTail) 0 NatS.lift := .zero
    have h := IsDefEqStrong.bvar hLookup (natType (NatS :: GTail))
    simpa [NatS, SExpr.lift, SExpr.lift'] using h
  have hGenericResult : IsDefEqStrong (NatS :: GTail)
      ((SExpr.bvar 3).app (SExpr.bvar 0))
      ((SExpr.bvar 3).app (SExpr.bvar 0)) (.sort level) := by
    simpa [MotiveTy, NatS, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natType (NatS :: GTail)) .sort
        hMotiveTail hMajorTailVar .sort
  have hGenericTail : IsDefEqStrong GTail GenericTail GenericTail
      (.sort majorSort) := by
    simpa [GenericTail, GTail, majorSort] using
      IsDefEqStrong.forallEDF (natType GTail)
        hGenericResult hGenericResult
  have hGenericAfterSucc : IsDefEqStrong G2
      (.forallE GenericSucc GenericTail)
      (.forallE GenericSucc GenericTail)
      (.sort (succSort.imax majorSort)) :=
    .forallEDF hGenericSucc hGenericTail hGenericTail
  have hRest : IsDefEqStrong G1 GenericRest GenericRest
      (.sort (level.imax (succSort.imax majorSort))) := by
    simpa [GenericRest, G1] using
      IsDefEqStrong.forallEDF hGenericZero
        hGenericAfterSucc hGenericAfterSucc
  have hMotive : IsDefEqStrong ([] : List SExpr)
      Motive Motive MotiveTy := by
    simpa [Motive, MotiveTy, NatS, level] using
      zeroT2MotiveStrongAt univs ([] : List SExpr)
  have hZero : IsDefEqStrong ([] : List SExpr)
      (zeroT2ZeroMinor univs) (zeroT2ZeroMinor univs) ZeroTy := by
    simpa [ZeroTy] using zeroT2ZeroMinorStrong univs
  have hSucc : IsDefEqStrong ([] : List SExpr)
      (zeroT2SuccMinor univs) (zeroT2SuccMinor univs) SuccTy := by
    simpa [SuccTy] using zeroT2SuccMinorStrong univs
  have hZeroTy : IsDefEqStrong ([] : List SExpr)
      ZeroTy ZeroTy (.sort level) := by
    simpa [ZeroTy, level] using zeroT2ResultTypeStrong univs
  have hSuccTy : IsDefEqStrong ([] : List SExpr)
      SuccTy SuccTy (.sort succSort) := by
    simpa [SuccTy, succSort, innerSort, natSort, level] using
      zeroT2SuccMinorTypeStrong univs
  have hMajorTail : IsDefEqStrong ([] : List SExpr)
      MajorTail MajorTail (.sort majorSort) := by
    simpa [MajorTail, majorSort, natSort, level] using
      zeroT2MajorTypeStrong univs
  have hMajorTailS : IsDefEqStrong (SuccTy :: [])
      MajorTail.lift MajorTail.lift (.sort majorSort) := by
    simpa [MajorTail, SuccTy, SExpr.lift, ← SExpr.lift'_comp] using
      natStrongWeak univs (Ctx.Lift'.one (A := SuccTy)) hMajorTail
  have hAfterSucc : IsDefEqStrong ([] : List SExpr)
      AfterSucc AfterSucc (.sort (succSort.imax majorSort)) := by
    simpa [AfterSucc] using
      IsDefEqStrong.forallEDF hSuccTy hMajorTailS hMajorTailS
  have hSuccTyZ : IsDefEqStrong (ZeroTy :: [])
      SuccTy.lift SuccTy.lift (.sort succSort) := by
    simpa [SuccTy, ZeroTy, SExpr.lift, ← SExpr.lift'_comp] using
      natStrongWeak univs (Ctx.Lift'.one (A := ZeroTy)) hSuccTy
  let rhoZS : Lift := .skip (.skip .refl)
  have WZS : Ctx.Lift' rhoZS ([] : List SExpr)
      (SuccTy.lift :: ZeroTy :: []) := by
    exact .skip (.skip .refl)
  have hMajorTailZS : IsDefEqStrong (SuccTy.lift :: ZeroTy :: [])
      MajorTail.lift.lift MajorTail.lift.lift (.sort majorSort) := by
    simpa [rhoZS, MajorTail, SuccTy, ZeroTy, SExpr.lift,
      ← SExpr.lift'_comp] using natStrongWeak univs WZS hMajorTail
  have hAfterSuccZ : IsDefEqStrong (ZeroTy :: [])
      (.forallE SuccTy.lift MajorTail.lift.lift)
      (.forallE SuccTy.lift MajorTail.lift.lift)
      (.sort (succSort.imax majorSort)) :=
    .forallEDF hSuccTyZ hMajorTailZS hMajorTailZS
  have hAfterZero : IsDefEqStrong ([] : List SExpr)
      AfterZero AfterZero
      (.sort (level.imax (succSort.imax majorSort))) := by
    simpa [AfterZero] using
      IsDefEqStrong.forallEDF hZeroTy hAfterSuccZ hAfterSuccZ
  have hRecM0 := IsDefEqStrong.appDF
    hMotiveTy hRest hRec hMotive hAfterZero
  have hRecM : IsDefEqStrong ([] : List SExpr)
      ((SExpr.const ``Nat.rec [level]).app Motive)
      ((SExpr.const ``Nat.rec [level]).app Motive) AfterZero := by
    simpa [GenericRest, GenericZero, GenericSucc, GenericTail,
      AfterZero, ZeroTy, SuccTy, MajorTail, Motive, MotiveTy, NatS,
      zeroT2Motive, zeroT2ResultType, zeroT2SuccMinorType,
      zeroT2MajorType,
      SExpr.lift, SExpr.lift', SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.lift, Subst.id, probeCancelTwoLifts,
      probeCancelUnderOne, probeCancelUnderTwo] using hRecM0
  have hRecMZ0 := IsDefEqStrong.appDF
    hZeroTy hAfterSuccZ hRecM hZero hAfterSucc
  have hRecMZ : IsDefEqStrong ([] : List SExpr)
      (((SExpr.const ``Nat.rec [level]).app Motive).app
        (zeroT2ZeroMinor univs))
      (((SExpr.const ``Nat.rec [level]).app Motive).app
        (zeroT2ZeroMinor univs)) AfterSucc := by
    simpa [AfterZero, AfterSucc, ZeroTy, SuccTy, MajorTail,
      zeroT2Motive, zeroT2SuccMinorType, zeroT2MajorType,
      SExpr.lift, SExpr.lift', SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.lift, Subst.id] using hRecMZ0
  have hRecMZS0 := IsDefEqStrong.appDF
    hSuccTy hMajorTailS hRecMZ hSucc hMajorTail
  simpa [zeroT2RecursorPrefix, AfterSucc, MajorTail, SuccTy,
    Motive, level, zeroT2Motive, zeroT2SuccMinorType,
    zeroT2MajorType, SExpr.lift, SExpr.lift', SExpr.inst,
    SExpr.subst, Subst.one, Subst.cons, Subst.lift, Subst.id] using hRecMZS0

theorem zeroT2RedexStrong (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    IsDefEqStrong ([] : List SExpr)
      (zeroT2Redex univs) (zeroT2Redex univs)
      (zeroT2ResultType univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  let NatS : SExpr := .const ``Nat []
  let Motive : SExpr := zeroT2Motive univs
  have hNat : IsDefEqStrong ([] : List SExpr) NatS NatS
      (SExpr.mkInst [] InductiveFixtures.natType.type) :=
    natTypeStrong univs []
  rw [probeNatTypeTypeV_eq] at hNat
  have hMajorBody : IsDefEqStrong [NatS]
      (Motive.app (.bvar 0)) (Motive.app (.bvar 0))
      (.sort (zeroT2U2 univs)) := by
    have hVar : IsDefEqStrong [NatS] (.bvar 0) (.bvar 0) NatS := by
      have h := IsDefEqStrong.bvar
        (.zero : Lookup [NatS] 0 NatS.lift) (natTypeStrong univs [NatS])
      simpa [NatS, SExpr.lift, SExpr.lift'] using h
    simpa [Motive] using
      (zeroT2Motive_betaStrong univs [NatS] hVar).hasType.1
  have hMajor := natZeroStrong univs ([] : List SExpr)
  have hResult := zeroT2ResultTypeStrong univs
  have h := IsDefEqStrong.appDF hNat hMajorBody
    (zeroT2RecursorPrefixStrong univs) hMajor hResult
  simpa [zeroT2Redex, zeroT2RecursorPrefix,
    zeroT2MajorType, NatS, Motive, zeroT2Motive,
    zeroT2ResultType,
    SExpr.lift, SExpr.lift', SExpr.inst, SExpr.subst,
    Subst.one, Subst.cons, Subst.lift, Subst.id] using h

theorem succT2RedexStrong (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    IsDefEqStrong ([] : List SExpr)
      (succT2Redex univs) (succT2Redex univs)
      (succT2ResultType univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  let NatS : SExpr := .const ``Nat []
  let Motive : SExpr := zeroT2Motive univs
  have hNat : IsDefEqStrong ([] : List SExpr) NatS NatS
      (SExpr.mkInst [] InductiveFixtures.natType.type) :=
    natTypeStrong univs []
  rw [probeNatTypeTypeV_eq] at hNat
  have hMajorBody : IsDefEqStrong [NatS]
      (Motive.app (.bvar 0)) (Motive.app (.bvar 0))
      (.sort (zeroT2U2 univs)) := by
    have hVar : IsDefEqStrong [NatS] (.bvar 0) (.bvar 0) NatS := by
      have h := IsDefEqStrong.bvar
        (.zero : Lookup [NatS] 0 NatS.lift) (natTypeStrong univs [NatS])
      simpa [NatS, SExpr.lift, SExpr.lift'] using h
    simpa [Motive] using
      (zeroT2Motive_betaStrong univs [NatS] hVar).hasType.1
  have hMajor := succT2MajorStrong univs
  have hResult := succT2ResultTypeStrong univs
  have h := IsDefEqStrong.appDF hNat hMajorBody
    (zeroT2RecursorPrefixStrong univs) hMajor hResult
  simpa [succT2Redex, zeroT2RecursorPrefix,
    zeroT2MajorType, NatS, Motive, zeroT2Motive,
    succT2ResultType,
    SExpr.lift, SExpr.lift', SExpr.inst, SExpr.subst,
    Subst.one, Subst.cons, Subst.lift, Subst.id] using h

theorem zeroT2RedexStratified (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    ∃ depth, HasTypeStratifiedS ([] : List SExpr)
      (zeroT2Redex univs) (zeroT2ResultType univs) true depth := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  obtain ⟨depth, hleft, _⟩ :=
    (zeroT2RedexStrong univs).stratify
  exact ⟨depth, hleft⟩

theorem succT2RedexStratified (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    ∃ depth, HasTypeStratifiedS ([] : List SExpr)
      (succT2Redex univs) (succT2ResultType univs) true depth := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  obtain ⟨depth, hleft, _⟩ :=
    (succT2RedexStrong univs).stratify
  exact ⟨depth, hleft⟩

/-- The successor derivation exposes the constructor major and its literal
predecessor at two genuinely strict syntax depths.  The depths are those
obtained by inverting the actual stratified redex derivation; no common depth
is guessed or imposed with monotonicity. -/
theorem succT2StrictDepths (univs : Nat) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    ∃ (redexDepth majorDepth predDepth : Nat)
        (majorType predType : SExpr),
      HasTypeStratifiedS ([] : List SExpr)
        (succT2Redex univs) (succT2ResultType univs) true redexDepth ∧
      HasTypeStratifiedS ([] : List SExpr)
        (succT2Major univs) majorType true majorDepth ∧
      HasTypeStratifiedS ([] : List SExpr)
        (succT2Pred univs) predType true predDepth ∧
      predDepth < majorDepth ∧ majorDepth < redexDepth := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  obtain ⟨redexDepth, hRedex⟩ := succT2RedexStratified univs
  have hRedexApp : HasTypeStratifiedS ([] : List SExpr)
      ((zeroT2RecursorPrefix univs).app (succT2Major univs))
      (succT2ResultType univs) true redexDepth := by
    simpa [succT2Redex, zeroT2RecursorPrefix] using hRedex
  obtain ⟨majorType, _, _, _, _, _, _, hMajor, _⟩ := hRedexApp.app_inv
  have hMajorApp : HasTypeStratifiedS ([] : List SExpr)
      ((SExpr.const ``Nat.succ []).app (succT2Pred univs))
      majorType true (redexDepth - 1) := by
    simpa [succT2Major] using hMajor
  obtain ⟨predType, _, _, _, _, _, _, hPred, _⟩ := hMajorApp.app_inv
  have hRedexPos := hRedexApp.app_depth_pos
  have hMajorPos := hMajorApp.app_depth_pos
  refine ⟨redexDepth, redexDepth - 1, (redexDepth - 1) - 1,
    majorType, predType, hRedex, ?_, ?_, by omega, by omega⟩
  · simpa [succT2Major] using hMajor
  · simpa [succT2Pred] using hPred

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.zeroT2RecursorPrefixStrong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms zeroT2RecursorPrefixStrong

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.zeroT2RedexStrong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms zeroT2RedexStrong

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.succT2RedexStrong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms succT2RedexStrong

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.zeroT2RedexStratified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms zeroT2RedexStratified

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.succT2RedexStratified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms succT2RedexStratified

/--
info: 'Lean4Lean.SExpr.ParamsD0.Falsification.succT2StrictDepths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms succT2StrictDepths


/-- Premise-free evidence-rich self-typing of the literal zero redex. -/
theorem zeroRedexStrong (univs : Nat)
    (level : @SLevel (natParams univs)) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    IsDefEqStrong (zeroSourceContext univs level)
      (zeroRedex univs level) (zeroRedex univs level)
      (zeroResultType univs) := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  simpa [zeroSourceContext, zeroRedex, zeroResultType, zeroMotive,
    zeroMinorType, zeroSuccMinorType] using
    natZeroRuleBodyStrong univs (Gamma := []) level
      (zeroRuleTypeStrong univs level)

/-- The exact syntax derivation supplies its own depth.  No fixed numeric
depth is guessed or postulated. -/
theorem zeroRedexStratified (univs : Nat)
    (level : @SLevel (natParams univs)) :
    letI : Params := natParams univs
    letI : Params.Semantic := natSemantic univs
    ∃ depth, HasTypeStratifiedS (zeroSourceContext univs level)
      (zeroRedex univs level) (zeroResultType univs) true depth := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  obtain ⟨depth, hleft, _⟩ := (zeroRedexStrong univs level).stratify
  exact ⟨depth, hleft⟩

end Falsification
end ParamsD0
end SExpr
end Lean4Lean
