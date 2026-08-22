import Lean4Lean.Environment

/-!
The kernel rejects inductive declarations in which a datatype being declared occurs applied to
something other than the parameters and universe levels of the declaration (lean4#14582, the
follow-up to lean4#14576).

The front end already enforces this and normalizes the occurrences it accepts, so the declarations
below are assembled by hand and handed straight to `Environment.addInductive`. The cases mirror
`tests/elab/issue_14576_nonuniform.lean` upstream.
-/

namespace Lean4Lean.Tests.UniformIndOccs

open Lean Kernel

/-- Dependencies the fixtures below refer to: a two-element type, two parametric wrappers that
drop or keep their argument, and an identity on types. -/
inductive W : Type where | mk (p : Bool)
inductive L (α : Type) : Type where | mk
inductive L2 (α : Type) (β : Type) : Type where | mk (a : α)
def Ignore (_ : Type) : Type := Unit
def IdT (α : Type 1) : Type 1 := α

/-- Runs `addInductive` on a hand-built declaration and reports whether the uniformity check
fired. Any other kernel error is reported as such, so a case that fails downstream instead is not
mistaken for a success of this check. -/
def addInd (env : Kernel.Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) : Except String Unit :=
  match Lean4Lean.Environment.addInductive env lparams nparams types false false with
  | .ok _ => .ok ()
  | .error (.other msg) =>
    if "invalid occurrence of datatype".isPrefixOf msg then .error "nonuniform"
    else .error s!"other: {msg}"
  | .error _ => .error "other: a structured kernel exception"

/-- The occurrence check must reject `name`'s declaration. -/
def expectNonuniform (env : Kernel.Environment) (label : String) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) : Except String Unit :=
  match addInd env lparams nparams types with
  | .ok _ => .error s!"{label}: a non-uniform occurrence was accepted"
  | .error "nonuniform" => .ok ()
  | .error e => .error s!"{label}: expected the uniformity error, got {e}"

/-- `name`'s declaration must be accepted outright. -/
def expectAccepted (env : Kernel.Environment) (label : String) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) : Except String Unit :=
  match addInd env lparams nparams types with
  | .ok _ => .ok ()
  | .error e => .error s!"{label}: a well-formed declaration was rejected ({e})"

/-- The occurrence check must not fire for `name`'s declaration; it may still fail downstream. -/
def expectNotNonuniform (env : Kernel.Environment) (label : String) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) : Except String Unit :=
  match addInd env lparams nparams types with
  | .error "nonuniform" => .error s!"{label}: the uniformity check rejected a uniform occurrence"
  | _ => .ok ()

run_meta do
  let env := (← getEnv).toKernelEnv
  let mut checks : Array (Except String Unit) := #[]
  let ns := `Lean4Lean.Tests.UniformIndOccs
  let W := mkConst (ns ++ `W)
  let Wmkfalse := mkApp (mkConst (ns ++ `W.mk)) (mkConst ``false)
  let L := mkConst (ns ++ `L)
  let L2 := mkConst (ns ++ `L2)
  let Ignore := mkConst (ns ++ `Ignore)
  let IdT := mkConst (ns ++ `IdT)
  let ind name type ctorName ctorType : List InductiveType :=
    [{ name, type, ctors := [{ name := ctorName, type := ctorType }] }]

  -- The parametric arguments of a nested occurrence `I Ds is` are dropped from the auxiliary
  -- declaration the kernel generates, so a non-uniform occurrence inside `Ds` escaped checking.
  let E := mkConst `E
  checks := checks.push <| expectNonuniform env "nested" [] 1 <| ind `E
    (mkForall `w .default W (mkSort 1)) `E.mk
    (mkForall `w .default W <|
      mkForall `l .default (mkApp L (mkApp E Wmkfalse)) (mkApp E (mkBVar 1)))

  -- A non-uniform occurrence may also hide behind a redex in a phantom argument, where the
  -- positivity check never fires.
  let F := mkConst `F
  let redex := mkApp (mkLambda `g .default (mkForall `_ .default W (mkSort 1))
    (mkApp (mkBVar 0) Wmkfalse)) F
  checks := checks.push <| expectNonuniform env "phantom redex" [] 1 <| ind `F
    (mkForall `w .default W (mkSort 1)) `F.mk
    (mkForall `w .default W <|
      mkForall `l .default (mkApp2 L2 (mkApp F (mkBVar 0)) redex) (mkApp F (mkBVar 1)))

  -- The occurrence may also sit in an index of a dropped parameter.
  let G := mkConst `G
  checks := checks.push <| expectNonuniform env "index of dropped parameter" [] 1 <| ind `G
    (mkForall `w .default W (mkForall `i .default (mkSort 1) (mkSort 1))) `G.mk
    (mkForall `w .default W <|
      mkForall `l .default (mkApp L (mkApp2 G (mkBVar 0) (mkApp G Wmkfalse)))
        (mkApp2 G (mkBVar 1) (mkConst ``Nat)))

  -- An occurrence that a later `whnf` erases is rejected too: the field of `D.mk` reduces to
  -- `Unit`, so this declaration was accepted before lean4#14582.
  let D := mkConst `D
  checks := checks.push <| expectNonuniform env "erased by whnf" [] 1 <| ind `D
    (mkForall `p .default (mkSort 1) (mkSort 1)) `D.mk
    (mkForall `p .default (mkSort 1) <|
      mkForall `_ .default (mkApp Ignore (mkApp D (mkConst ``Nat))) (mkApp D (mkBVar 1)))

  -- The universe levels must be uniform as well; this too was accepted before lean4#14582.
  checks := checks.push <| expectNonuniform env "permuted universe levels" [`u, `v] 1 <| ind `U
    (mkForall `p .default (mkSort 1) (mkSort 1)) `U.mk
    (mkForall `p .default (mkSort 1) <|
      mkForall `_ .default (mkApp L (mkApp (mkConst `U [.param `v, .param `u]) (mkBVar 0)))
        (mkApp (mkConst `U [.param `u, .param `v]) (mkBVar 1)))

  -- A datatype without parameters is unconstrained by this check, so the occurrence of `H` in the
  -- index of the dropped parameter is accepted.
  let H := mkConst `H
  let HNat := mkApp H (mkConst ``Nat)
  checks := checks.push <| expectNotNonuniform env "no parameters" [] 0 <| ind `H
    (mkForall `i .default (mkSort 1) (mkSort 1)) `H.mk
    (mkForall `l .default (mkApp L (mkApp H HNat)) HNat)

  -- A constructor's parameter binder only has to be *definitionally equal* to the corresponding
  -- parameter of the type former, which the constructor check verifies. The occurrence check must
  -- therefore accept an occurrence applied to that binder, here `p : IdT Type` for `p : Type`.
  let V := mkConst `V
  checks := checks.push <| expectNotNonuniform env "defeq parameter binder" [] 1 <| ind `V
    (mkForall `p .default (mkSort 1) (mkSort 1)) `V.mk
    (mkForall `p .default (mkApp IdT (mkSort 1)) <|
      mkForall `l .default (mkApp L (mkApp V (mkBVar 0))) (mkApp V (mkBVar 1)))

  -- A constructor type whose leading binders are not the parameters is rejected downstream, so
  -- this check need not (and does not) recognize the situation: `C.mk` applies `C` to a
  -- `let`-bound variable, which looks like the parameter at that binder depth.
  let C := mkConst `C
  checks := checks.push <| expectNotNonuniform env "let-bound lookalike parameter" [] 1 <| ind `C
    (mkForall `p .default (mkSort 1) (mkSort 1)) `C.mk
    (.letE `x (mkSort 1) (mkConst ``Nat)
      (mkForall `p .default (mkSort 1) (mkApp C (mkBVar 1))) false)

  -- The parameter types of the datatypes in a mutual declaration only have to agree up to
  -- definitional equality, and the constructors of both take the parameter type of the *first*
  -- type former. Neither the occurrence check nor the recursor check may reject that
  -- (lean4#14808's `tests/elab/inductiveDefeqParams.lean`).
  let type1 := mkSort 1
  let idType := mkApp2 (mkConst ``id [.succ (.succ (.succ .zero))]) (mkSort 2) type1
  let Id1 := mkConst `Id1
  let Id2 := mkConst `Id2
  checks := checks.push <| expectAccepted env "defeq mutual parameters" [] 1
    [{ name := `Id1
       type := mkForall `a .default type1 (mkSort 1)
       ctors := [{
         name := `Id1.mk
         type := mkForall `a .default type1 <|
           mkForall `_ .default (mkApp Id2 (mkBVar 0)) (mkApp Id1 (mkBVar 1)) }] },
     { name := `Id2
       type := mkForall `a .default idType (mkSort 1)
       ctors := [{
         name := `Id2.mk
         type := mkForall `a .default type1 <|
           mkForall `_ .default (mkApp Id1 (mkBVar 0)) (mkApp Id2 (mkBVar 1)) }] }]

  for check in checks do
    if let .error msg := check then throwError msg

/-- Uniform occurrences are still accepted, including through a reducible wrapper and across a
mutual block. These go through the front end, so they exercise the check as `addDecl` runs it. -/
inductive Good (p : Type) where
  | mk : List (Good p) → Good p

inductive T (p : Type) where
  | mk : Ignore (T (id p)) → List (T p) → T p

mutual
  inductive A (p : Type) where | mk : List (B p) → A p
  inductive B (p : Type) where | mk : Array (A p) → B p
end

end Lean4Lean.Tests.UniformIndOccs
