/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.TypeChecker
import Lean4Lean.Environment.Basic

namespace Lean4Lean
namespace Environment
open Lean hiding Environment Exception
open Kernel TypeChecker

deriving instance ToExpr for LevelMVarId
deriving instance ToExpr for Level
deriving instance ToExpr for MVarId
deriving instance ToExpr for BinderInfo
deriving instance ToExpr for String.Pos.Raw
deriving instance ToExpr for Substring.Raw
deriving instance ToExpr for SourceInfo
deriving instance ToExpr for Syntax
deriving instance ToExpr for DataValue
deriving instance ToExpr for KVMap
deriving instance ToExpr for Expr

elab (name := microQq) "q(" e:term ")" : term =>
  return toExpr (← instantiateMVars (← Elab.Term.elabTerm e none))

structure Reflection where
  type : Expr
  ofTrue : Expr
  ofFalse : Expr
  toDec : Expr

def Reflection.defn₁ : Reflection where
  type := q(fun p b => ∀ {q : Prop}, ((b = true → p) → (¬b = true → ¬p) → q) → q)
  ofTrue := q(fun p (H : ∀ {q : Prop}, ((true = true → p) → (¬true = true → ¬p) → q) → q) =>
    H fun h _ => h rfl)
  ofFalse := q(fun p (H : ∀ {q : Prop}, ((false = true → p) → (¬false = true → ¬p) → q) → q) =>
    H fun _ h => h Bool.noConfusion)
  toDec := q(fun p b (H : ∀ {q : Prop}, ((b = true → p) → (¬b = true → ¬p) → q) → q) =>
    if h : b = true then isTrue (H fun h' _ => h' h) else isFalse (H fun _ h' => h' h))

def Reflection.defn₂ : Reflection where
  type := q(fun p b => ∀ {q : Prop}, ((b = true → p) → (b = false → ¬p) → q) → q)
  ofTrue := q(fun p (H : ∀ {q : Prop}, ((true = true → p) → (true = false → ¬p) → q) → q) =>
    H fun h _ => h rfl)
  ofFalse := q(fun p (H : ∀ {q : Prop}, ((false = true → p) → (false = false → ¬p) → q) → q) =>
    H fun _ h => h rfl)
  toDec := q(fun p b (H : ∀ {q : Prop}, ((b = true → p) → (b = false → ¬p) → q) → q) =>
    b.casesOn (motive := fun b' => b = b' → Decidable p)
      (fun h => isFalse (H fun _ h' => h' h)) (fun h => isTrue (H fun h' _ => h' h)) rfl)

def Reflection.check (r : Reflection) (fail : ∀ {α}, M α) : M Unit := do
  unless ← isDefEq (← checkType r.type) q(Prop → Bool → Prop) do fail

inductive ConditionImpl where
  | bool
  | reflectNatNat (asBool : Expr) (reflect : Reflection) (proof : Expr)

structure Condition where
  prop : Expr
  dec : Expr
  impl : ConditionImpl

def Condition.natLE : Condition where
  prop := q(@LE.le Nat _)
  dec := q(Nat.decLe)
  impl := .reflectNatNat
    (asBool := q(Nat.ble))
    (reflect := .defn₁)
    (proof := q(fun n m {q : Prop} (H : _ → _ → q) =>
      H (@Nat.le_of_ble_eq_true n m) (@Nat.not_le_of_not_ble_eq_true n m)))

def Condition.natEq : Condition where
  prop := q(@Eq Nat)
  dec := q(Nat.decEq)
  impl := .reflectNatNat
    (asBool := q(Nat.beq))
    (reflect := .defn₂)
    (proof := q(fun n m {q : Prop} (H : _ → _ → q) =>
      H (@Nat.eq_of_beq_eq_true n m) (@Nat.ne_of_beq_eq_false n m)))

def Condition.bool : Condition where
  prop := q(fun x : Bool => x = true)
  dec := q(fun x => Bool.decEq x true)
  impl := .bool

def Reflection.ite (r : Reflection) : Expr :=
  .lam0 q(Prop) <| .lam0 q(Bool) <| .lam0 (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
    .lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) (.bvar 3)
      (mkApp3 r.toDec (.bvar 3) (.bvar 2) (.bvar 1))

def Reflection.natDITE (r : Reflection) : Expr :=
  .lam0 q(Prop) <| .lam0 q(Bool) <| .lam0 (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
    mkApp2 q(@dite Nat) (.bvar 2) (mkApp3 r.toDec (.bvar 2) (.bvar 1) (.bvar 0))

def Reflection.checkITE (r : Reflection) (fail : ∀ {α}, M α) : M Unit := do
  unless ← isDefEq (← checkType r.ite) (.arrow q(Prop) <| .arrow q(Bool) <|
    .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) q(∀ α : Type, α → α → α)) do fail
  let trueLhs := .lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
    mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)
  let trueRhs := .lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
    .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1
  unless ← isDefEq trueLhs trueRhs do fail
  let falseLhs := .lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
    mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)
  let falseRhs := .lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
    .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0
  unless ← isDefEq falseLhs falseRhs do fail

def Reflection.checkNatDITE (r : Reflection) (fail : ∀ {α}, M α) : M Unit := do
  unless ← isDefEq (← checkType q(Not)) q(Prop → Prop) do fail
  unless ← isDefEq (← checkType r.natDITE) (.arrow q(Prop) <| .arrow q(Bool) <|
    .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
    .arrow (.arrow (.bvar 2) q(Nat)) <| .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) <|
    q(Nat)) do fail
  unless ← isDefEq (← checkType r.ofTrue) (.arrow q(Prop) <|
    .arrow (mkApp2 r.type (.bvar 0) q(true)) (.bvar 1)) do fail
  unless ← isDefEq (← checkType r.ofFalse) (.arrow q(Prop) <|
    .arrow (mkApp2 r.type (.bvar 0) q(false)) (mkApp q(Not) (.bvar 1))) do fail
  let close (truth : Expr) (body : Expr) :=
    .lam0 q(Prop) <|
    .lam0 (.arrow (.bvar 0) q(Nat)) <|
    .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
    .lam0 (mkApp2 r.type (.bvar 2) truth) body
  let trueLhs := close q(true) <|
    mkApp5 r.natDITE (.bvar 3) q(true) (.bvar 0) (.bvar 2) (.bvar 1)
  let trueRhs := close q(true) <|
    mkApp (.bvar 2) (mkApp2 r.ofTrue (.bvar 3) (.bvar 0))
  unless ← isDefEq trueLhs trueRhs do fail
  let falseLhs := close q(false) <|
    mkApp5 r.natDITE (.bvar 3) q(false) (.bvar 0) (.bvar 2) (.bvar 1)
  let falseRhs := close q(false) <|
    mkApp (.bvar 1) (mkApp2 r.ofFalse (.bvar 3) (.bvar 0))
  unless ← isDefEq falseLhs falseRhs do fail

def Condition.check (cond : Condition) (fail : ∀ {α}, M α)
    (ite := false) (dite := false) : M Unit := do
  _ ← checkType cond.dec
  match cond.impl with
  | .reflectNatNat asBool reflect proof =>
    unless ← isDefEq (← inferType cond.prop) q(Nat → Nat → Prop) do fail
    reflect.check fail
    if ite then reflect.checkITE fail
    if dite then reflect.checkNatDITE fail
    let y := .bvar 0; let x := .bvar 1
    let e := .lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 reflect.toDec
      (mkApp2 cond.prop x y) (mkApp2 asBool x y) (mkApp2 proof x y)
    _ ← checkType e
    let decideFn := .lam0 q(Nat) <| .lam0 q(Nat) <|
      mkApp5 q(@_root_.ite.{1}) q(Bool)
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 cond.dec (.bvar 1) (.bvar 0)) q(true) q(false)
    unless ← isDefEq (← inferType decideFn) q(Nat → Nat → Bool) do fail
    unless ← isDefEq (← inferType asBool) q(Nat → Nat → Bool) do fail
    unless ← isProp (← inferType proof) do fail
    unless ← isDefEq e cond.dec do fail
  | .bool =>
    unless ← isDefEq (← inferType cond.prop) q(Bool → Prop) do fail
    let b := .bvar 0
    if ite then
      let natITE := .lam0 q(Bool) <|
        mkApp2 q(@_root_.ite Nat) (mkApp cond.prop b) (mkApp cond.dec b)
      unless ← isDefEq (← checkType natITE) q(Bool → Nat → Nat → Nat) do fail
      unless ← isDefEq (mkApp natITE q(true)) q(fun a _ : Nat => a) do fail
      unless ← isDefEq (mkApp natITE q(false)) q(fun _ a : Nat => a) do fail
    if dite then throw <| .other "unsupported"

def Condition.natLEReflectProof : Expr :=
  q(fun n m {q : Prop} (H : _ → _ → q) =>
    H (@Nat.le_of_ble_eq_true n m) (@Nat.not_le_of_not_ble_eq_true n m))

def Condition.natLEReflectedFn : Expr :=
  .lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 Reflection.defn₁.toDec
    (mkApp2 Condition.natLE.prop (.bvar 1) (.bvar 0))
    (mkApp2 q(Nat.ble) (.bvar 1) (.bvar 0))
    (mkApp2 Condition.natLEReflectProof (.bvar 1) (.bvar 0))

def Condition.natLEDecideFn : Expr :=
  .lam0 q(Nat) <| .lam0 q(Nat) <| mkApp5 q(@_root_.ite.{1}) q(Bool)
    (mkApp2 Condition.natLE.prop (.bvar 1) (.bvar 0))
    (mkApp2 Condition.natLE.dec (.bvar 1) (.bvar 0)) q(true) q(false)

/-- Expressions whose translations are retained by the verified Nat-≤
primitive-condition checker. The ordinary condition checker validates their
types or equations; this explicit pass exposes the translations to the
conservation proof without fixing their target representation. -/
def Condition.natLEEvidenceExpressions : List Expr :=
  let r := Reflection.defn₁
  let iteTy := .arrow q(Prop) <| .arrow q(Bool) <|
    .arrow (mkApp2 r.type (.bvar 1) (.bvar 0))
      q(∀ α : Type, α → α → α)
  let iteTrueL := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
      mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)
  let iteTrueR := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
      .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1
  let iteFalseL := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
      mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)
  let iteFalseR := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
      .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0
  let diteTy := .arrow q(Prop) <| .arrow q(Bool) <|
    .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
    .arrow (.arrow (.bvar 2) q(Nat)) <|
    .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) q(Nat)
  let ofTrueTy := .arrow q(Prop) <|
    .arrow (mkApp2 r.type (.bvar 0) q(true)) (.bvar 1)
  let ofFalseTy := .arrow q(Prop) <|
    .arrow (mkApp2 r.type (.bvar 0) q(false)) (mkApp q(Not) (.bvar 1))
  let close (truth : Expr) (body : Expr) :=
    .lam0 q(Prop) <|
    .lam0 (.arrow (.bvar 0) q(Nat)) <|
    .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
    .lam0 (mkApp2 r.type (.bvar 2) truth) body
  let diteTrueL := close q(true) <|
    mkApp5 r.natDITE (.bvar 3) q(true) (.bvar 0) (.bvar 2) (.bvar 1)
  let diteTrueR := close q(true) <|
    mkApp (.bvar 2) (mkApp2 r.ofTrue (.bvar 3) (.bvar 0))
  let diteFalseL := close q(false) <|
    mkApp5 r.natDITE (.bvar 3) q(false) (.bvar 0) (.bvar 2) (.bvar 1)
  let diteFalseR := close q(false) <|
    mkApp (.bvar 1) (mkApp2 r.ofFalse (.bvar 3) (.bvar 0))
  [Condition.natLE.dec, Condition.natLE.prop, q(Nat → Nat → Prop),
    r.type, q(Prop → Bool → Prop), r.ite, iteTy,
    iteTrueL, iteTrueR, iteFalseL, iteFalseR,
    q(Not), q(Prop → Prop), r.natDITE, diteTy,
    r.ofTrue, ofTrueTy, r.ofFalse, ofFalseTy,
    diteTrueL, diteTrueR, diteFalseL, diteFalseR,
    Condition.natLEReflectedFn, Condition.natLEDecideFn,
    q(Nat → Nat → Bool), q(Nat.ble), Condition.natLEReflectProof]

def checkExprTypes : List Expr → M Unit
  | [] => pure ()
  | e :: es => do
    _ ← checkType e
    checkExprTypes es

def Condition.natLE.checkForPrimitive
    (fail : ∀ {α}, M α) : M Unit := do
  checkExprTypes Condition.natLEEvidenceExpressions
  Condition.natLE.check fail (ite := true) (dite := true)

protected def Condition.ite (cond : Condition) (α : Expr) (args : Array Expr) (t e : Expr) : Expr :=
  mkApp5 q(@ite.{1}) α (mkAppN cond.prop args) (mkAppN cond.dec args) t e

protected def Condition.dite (cond : Condition) (args: Array Expr) (t e : Expr) : Expr :=
  mkApp4 q(@dite Nat) (mkAppN cond.prop args) (mkAppN cond.dec args)
    (.lam0 (mkAppN cond.prop args) t)
    (.lam0 (mkApp q(Not) (mkAppN cond.prop args)) e)

/-- Use the selector whose equations were checked by `Condition.check`.
For reflected Nat conditions this retains the Boolean reflection witness. -/
protected def Condition.reflectedITE (cond : Condition) (α : Expr)
    (args : Array Expr) (t e : Expr) : Expr :=
  match cond.impl with
  | .reflectNatNat asBool reflect proof =>
    mkApp6 reflect.ite (mkAppN cond.prop args) (mkAppN asBool args)
      (mkAppN proof args) α t e
  | .bool => cond.ite α args t e

/-- Dependent counterpart of `Condition.reflectedITE`. -/
protected def Condition.reflectedDITE (cond : Condition) (args : Array Expr)
    (t e : Expr) : Expr :=
  match cond.impl with
  | .reflectNatNat asBool reflect proof =>
    mkApp5 reflect.natDITE (mkAppN cond.prop args) (mkAppN asBool args)
      (mkAppN proof args)
      (.lam0 (mkAppN cond.prop args) t)
      (.lam0 (mkApp q(Not) (mkAppN cond.prop args)) e)
  | .bool => cond.dite args t e

protected def Condition.decide (cond : Condition) (args : Array Expr) : Expr :=
  cond.ite q(Bool) args q(true) q(false)

def unfoldWellFounded (e : Expr) (fvs : Array Expr) (eq_def : Expr) (fail : ∀ {α}, M α) : M Expr := do
  let .app (.app _ lhs) rhs := eq_def.getForallBody.instantiateRev fvs | fail
  let orig := lhs.getAppFn
  let rhs := rhs.replace fun e' => if e' == orig then some e else none
  let .app e1 wfn ← whnf (mkAppN e fvs) | fail
  e1.withApp fun accRec args => do
  let #[α,r,_,_,n] := args | fail
  let .const ``Acc.rec [_, u] := accRec | fail
  let .app wf _ := wfn | fail
  let L := .lam0 α <| .lam0 (mkApp2 r (.bvar 0) n) (mkApp wf (.bvar 1))
  let wfn' := mkApp4 (.const ``Acc.intro [u]) α r n L
  let p ← inferType wfn
  unless ← isProp p do fail
  unless ← isDefEq p (← checkType wfn') do fail
  _ ← checkType rhs
  unless ← isDefEq (e1.app wfn') rhs do fail
  return (← getLCtx).mkLambda fvs rhs

def lambdaTelescope (e : Expr) (k : Array Expr → Expr → M α) : M α := loop #[] e where
  loop fvars
  | .lam x dom body bi =>
    let d := dom.instantiateRev fvars
    withLocalDecl x bi d fun fv => do
      let fvars := fvars.push fv
      loop fvars body
  | e => k fvars (e.instantiateRev fvars)

def forallTelescope (e : Expr) (k : Array Expr → Expr → M α) : M α := loop #[] e where
  loop fvars
  | .forallE x dom body bi =>
    let d := dom.instantiateRev fvars
    withLocalDecl x bi d fun fv => do
      let fvars := fvars.push fv
      loop fvars body
  | e => k fvars (e.instantiateRev fvars)

def unfoldNatWellFounded (e : Expr) (fvs : Array Expr) (eq_def : Expr) (fail : ∀ {α}, M α) : M Expr := do
  let succ := mkApp q(Nat.succ)
  let defeq1 a b := isDefEq (.arrow q(Nat) a) (.arrow q(Nat) b)
  let x := .bvar 0
  let .app (.app _ lhs) rhs := eq_def.getForallBody.instantiateRev fvs | fail
  let orig := lhs.getAppFn
  let rhs := rhs.replace fun e' => if e' == orig then some e else none
  let e1 ← whnfCore (mkAppN e fvs) -- get _unary
  let e1 ← unfoldDefinition e1 -- get fix
  (← whnfCore e1).withApp fun fix args => do
  let .const ``WellFounded.Nat.fix [_, _] := fix | fail
  let #[α,motive,f,F,a₀] := args | fail
  let fixFn := mkAppN fix #[α,motive,f,F]
  withLocalDecl `a .default (← inferType a₀) fun a => do
  -- prove |- fix α motive f F a ≡ go α motive f F (eager (f a)) a [proof]
  let e1 ← unfoldDefinition (.app fixFn a) -- get fix.go
  let e1 ← whnfCore e1
  e1.withApp fun fixGo args => do
    let #[α',motive',f',F',fuel,a',_] := args | fail
    unless (α, motive, f, F, a) == (α', motive', f', F', a') do fail
    let .app eager n := fuel | fail
    unless ← isDefEq n (succ (.app f a)) do fail
    -- prove |- eager n = if beq n n = true then n else n
    unless (← getEnv).contains ``Nat.beq do fail
    let c := Condition.bool; c.check (fail) (ite := true)
    unless ← defeq1 (mkApp eager x) (c.ite q(Nat) #[mkApp2 (.const ``Nat.beq []) x x] x x) do fail
    -- prove |- go α motive f F (succ t) x hfuel ≡ F x fun y hy => go α motive f F t y [proof]
    let go' ← unfoldDefinition fixGo -- get fix
    lambdaTelescope go' fun fvs go' => do
    let #[_,_,_,F,t] := fvs | fail
    let .app natRec t' := go' | fail
    unless !natRec.containsFVar t.fvarId! && t == t' do fail
    _ ← checkType (succ t)
    let gor ← whnfCore (.app natRec (succ t))
    lambdaTelescope gor fun fvs gor => do
    let #[x,_] := fvs | fail
    let .app Fx ih := gor | fail
    unless .app F x == Fx do fail
    lambdaTelescope ih fun fvs ih => do
    let #[y,_] := fvs | fail
    let .app ih _ := ih | fail
    unless ih == .app (.app natRec t) y do fail
  -- prove |- rhs ≡ F x fun y _ => fix α motive f F y
  let .forallE _ dom _ _ ← inferType (.app F a₀) | fail
  let ih' ← forallTelescope dom fun fvs _ => do
    let #[y,_] := fvs | fail
    return (← getLCtx).mkLambda fvs (.app fixFn y)
  have rhs' := mkApp2 F a₀ ih'
  _ ← checkType rhs'
  unless ← isDefEq rhs rhs' do fail
  return (← getLCtx).mkLambda fvs rhs

/-- Validate the closed type and defining equations for the elementary
`Nat.add` primitive. Keeping this branch separate gives its verification
certificate a bounded executable surface instead of forcing it to unfold the
entire primitive dispatcher. -/
def checkNatAddPrimitive (env : Environment) (v : DefinitionVal)
    (fail : ∀ {α}, M α) : M Unit := do
  unless env.contains ``Nat && v.levelParams.isEmpty do fail
  unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
  let add := mkApp2 v.value
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let x := .bvar 0
  let y := .bvar 1
  let defeq1 a b := isDefEq (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  let defeq2 a b := defeq1 (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  unless ← defeq1 (add x zero) x do fail
  unless ← defeq2 (add y (succ x)) (succ (add y x)) do fail

/-- Validate the closed type and defining equations for the elementary
`Nat.pred` primitive. The successor equation is closed with a lambda so the
checker tests the intended pointwise equation. -/
def checkNatPredPrimitive (env : Environment) (v : DefinitionVal)
    (fail : ∀ {α}, M α) : M Unit := do
  unless env.contains ``Nat && v.levelParams.isEmpty do fail
  unless ← isDefEq v.type q(Nat → Nat) do fail
  let pred := mkApp v.value
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let x := .bvar 0
  unless ← isDefEq (pred zero) zero do fail
  unless ← isDefEq
    (.lam0 q(Nat) <| pred (succ x))
    (.lam0 q(Nat) x) do fail

/-- Validate the closed type and defining equations for the elementary
`Nat.sub` primitive. -/
def checkNatSubPrimitive (env : Environment) (v : DefinitionVal)
    (fail : ∀ {α}, M α) : M Unit := do
  unless env.contains ``Nat.pred && v.levelParams.isEmpty do fail
  unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
  let sub := mkApp2 v.value
  let pred := mkApp q(Nat.pred)
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let x := .bvar 0
  let y := .bvar 1
  let defeq1 a b := isDefEq (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  let defeq2 a b := defeq1 (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  unless ← defeq1 (sub x zero) x do fail
  unless ← defeq2 (sub y (succ x)) (pred (sub y x)) do fail

/-- Validate the closed type and defining equations for the elementary
`Nat.mul` primitive. -/
def checkNatMulPrimitive (env : Environment) (v : DefinitionVal)
    (fail : ∀ {α}, M α) : M Unit := do
  unless env.contains ``Nat.add && v.levelParams.isEmpty do fail
  unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
  let mul := mkApp2 v.value
  let add := mkApp2 q(Nat.add)
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let x := .bvar 0
  let y := .bvar 1
  let defeq1 a b := isDefEq (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  let defeq2 a b := defeq1 (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  unless ← defeq1 (mul x zero) zero do fail
  unless ← defeq2 (mul y (succ x)) (add (mul y x) y) do fail

/-- Validate the closed type and defining equations for the elementary
`Nat.pow` primitive. -/
def checkNatPowPrimitive (env : Environment) (v : DefinitionVal)
    (fail : ∀ {α}, M α) : M Unit := do
  unless env.contains ``Nat.mul && v.levelParams.isEmpty do fail
  unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
  let pow := mkApp2 v.value
  let mul := mkApp2 q(Nat.mul)
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let one := succ zero
  let x := .bvar 0
  let y := .bvar 1
  let defeq1 a b := isDefEq (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  let defeq2 a b := defeq1 (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  unless ← defeq1 (pow x zero) one do fail
  unless ← defeq2 (pow y (succ x)) (mul (pow y x) y) do fail

/-- Validate the closed type and four constructor equations for `Nat.beq`. -/
def checkNatBEqPrimitive (env : Environment) (v : DefinitionVal)
    (fail : ∀ {α}, M α) : M Unit := do
  unless env.contains ``Nat && env.contains ``Bool &&
      v.levelParams.isEmpty do fail
  unless ← isDefEq v.type q(Nat → Nat → Bool) do fail
  let beq := mkApp2 v.value
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let x := .bvar 0
  let y := .bvar 1
  let defeq1 a b := isDefEq (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  let defeq2 a b := defeq1 (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  unless ← isDefEq (beq zero zero) q(true) do fail
  unless ← defeq1 (beq zero (succ x)) q(false) do fail
  unless ← defeq1 (beq (succ x) zero) q(false) do fail
  unless ← defeq2 (beq (succ y) (succ x)) (beq y x) do fail

/-- Validate the closed type and four constructor equations for `Nat.ble`. -/
def checkNatBLEPrimitive (env : Environment) (v : DefinitionVal)
    (fail : ∀ {α}, M α) : M Unit := do
  unless env.contains ``Nat && env.contains ``Bool &&
      v.levelParams.isEmpty do fail
  unless ← isDefEq v.type q(Nat → Nat → Bool) do fail
  let ble := mkApp2 v.value
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let x := .bvar 0
  let y := .bvar 1
  let defeq1 a b := isDefEq (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  let defeq2 a b := defeq1 (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  unless ← isDefEq (ble zero zero) q(true) do fail
  unless ← defeq1 (ble zero (succ x)) q(true) do fail
  unless ← defeq1 (ble (succ x) zero) q(false) do fail
  unless ← defeq2 (ble (succ y) (succ x)) (ble y x) do fail

/-- Validate the closed type and two recursive equations for `Nat.shiftLeft`. -/
def checkNatShiftLeftPrimitive (env : Environment) (v : DefinitionVal)
    (fail : ∀ {α}, M α) : M Unit := do
  unless env.contains ``Nat.mul && v.levelParams.isEmpty do fail
  unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
  let shl := mkApp2 v.value
  let mul := mkApp2 q(Nat.mul)
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let two := succ (succ zero)
  let x := .bvar 0
  let y := .bvar 1
  let defeq1 a b := isDefEq (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  let defeq2 a b := defeq1 (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  unless ← defeq1 (shl x zero) x do fail
  unless ← defeq2 (shl x (succ y)) (shl (mul two x) y) do fail

/-- Validate the closed type and two recursive equations for `Nat.shiftRight`. -/
def checkNatShiftRightPrimitive (env : Environment) (v : DefinitionVal)
    (fail : ∀ {α}, M α) : M Unit := do
  unless env.contains ``Nat.div && v.levelParams.isEmpty do fail
  unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
  let shr := mkApp2 v.value
  let div := mkApp2 q(Nat.div)
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let two := succ (succ zero)
  let x := .bvar 0
  let y := .bvar 1
  let defeq1 a b := isDefEq (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  let defeq2 a b := defeq1 (.lam0 q(Nat) a) (.lam0 q(Nat) b)
  unless ← defeq1 (shr x zero) x do fail
  unless ← defeq2 (shr x (succ y)) (div (shr x y) two) do fail

def natModTopEquation (modFn : Expr) : Expr × Expr :=
  let succ := mkApp q(Nat.succ)
  let mod := mkApp2 modFn
  let go := mkApp5 q(Nat.modCore.go)
  let c := Condition.natLE
  let x := .bvar 1
  let y := .bvar 0
  let sx := succ x
  let lhs := .lam0 q(Nat) <| .lam0 q(Nat) <| mod sx y
  let rhs := .lam0 q(Nat) <| .lam0 q(Nat) <|
    c.reflectedITE q(Nat) #[y, sx]
      (c.reflectedDITE #[q(Nat.succ Nat.zero), y]
        (go (.bvar 1) (.bvar 0) (succ (succ (.bvar 2)))
          (succ (.bvar 2))
          (mkApp q(Nat.lt_succ_self) (succ (.bvar 2))))
        (succ (.bvar 2))) sx
  (lhs, rhs)

def natModGoEquation : Expr × Expr :=
  let succ := mkApp q(Nat.succ)
  let sub := mkApp2 q(Nat.sub)
  let le := mkApp2 q(@LE.le Nat _)
  let go := mkApp5 q(Nat.modCore.go)
  let c := Condition.natLE
  let y := .bvar 4
  let hy := .bvar 3
  let fuel := .bvar 2
  let x := .bvar 1
  let h := .bvar 0
  let close body := .lam0 q(Nat) <|
    .lam0 (le q(Nat.succ Nat.zero) (.bvar 0)) <|
    .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 (le (succ (.bvar 0)) (succ (.bvar 1))) body
  let lhs := close <| go y hy (succ fuel) x h
  let rhs := close <| c.reflectedDITE #[y, x]
    (go (.bvar 5) (.bvar 4) (.bvar 3)
      (sub (.bvar 2) (.bvar 5))
      (mkApp6 q(@Nat.div_rec_fuel_lemma)
        (.bvar 2) (.bvar 5) (.bvar 3) (.bvar 4)
        (.bvar 0) (.bvar 1)))
    (.bvar 2)
  (lhs, rhs)

/-- Structural loose-bvar lifting for primitive certificate source terms.

Using a reducible builder here keeps the executable Nat.div certificate and
its verification independent of the opaque kernel implementation of
`Lean.Expr.liftLooseBVars`. -/
def primitiveLiftLooseBVars (e : @& Expr) (s d : @& Nat) : Expr :=
  match e with
  | .bvar i => .bvar (if i < s then i else i + d)
  | .mdata m e => .mdata m (primitiveLiftLooseBVars e s d)
  | .proj n i e => .proj n i (primitiveLiftLooseBVars e s d)
  | .app f a => .app (primitiveLiftLooseBVars f s d)
      (primitiveLiftLooseBVars a s d)
  | .lam n t b bi => .lam n (primitiveLiftLooseBVars t s d)
      (primitiveLiftLooseBVars b (s + 1) d) bi
  | .forallE n t b bi => .forallE n (primitiveLiftLooseBVars t s d)
      (primitiveLiftLooseBVars b (s + 1) d) bi
  | .letE n t v b bi => .letE n (primitiveLiftLooseBVars t s d)
      (primitiveLiftLooseBVars v s d) (primitiveLiftLooseBVars b (s + 1) d) bi
  | e@(.const ..)
  | e@(.sort _)
  | e@(.fvar _)
  | e@(.mvar _)
  | e@(.lit _) => e

def natDivTopRhs (x y : Expr) : Expr :=
  let succ := mkApp q(Nat.succ)
  let go := mkApp5 q(Nat.div.go)
  let c := Condition.natLE
  let x' := primitiveLiftLooseBVars x 0 1
  let y' := primitiveLiftLooseBVars y 0 1
  c.reflectedDITE #[q(Nat.succ Nat.zero), y]
    (go y' (.bvar 0) (succ x') x'
      (mkApp q(Nat.lt_succ_self) x')) q(Nat.zero)

def natDivTopEquation (divFn : Expr) : Expr × Expr :=
  let div := mkApp2 divFn
  let x := .bvar 1
  let y := .bvar 0
  let lhs := .lam0 q(Nat) <| .lam0 q(Nat) <| div x y
  let rhs := .lam0 q(Nat) <| .lam0 q(Nat) <| natDivTopRhs x y
  (lhs, rhs)

def natDivGoLhsBody (y hy fuel x h : Expr) : Expr :=
  let succ := mkApp q(Nat.succ)
  let go := mkApp5 q(Nat.div.go)
  go y hy (succ fuel) x h

def natDivGoRhsBody (y hy fuel x h : Expr) : Expr :=
  let succ := mkApp q(Nat.succ)
  let sub := mkApp2 q(Nat.sub)
  let go := mkApp5 q(Nat.div.go)
  let c := Condition.natLE
  c.reflectedDITE #[y, x]
    (succ (go (primitiveLiftLooseBVars y 0 1)
      (primitiveLiftLooseBVars hy 0 1)
      (primitiveLiftLooseBVars fuel 0 1)
      (sub (primitiveLiftLooseBVars x 0 1)
        (primitiveLiftLooseBVars y 0 1))
      (mkApp6 q(@Nat.div_rec_fuel_lemma)
        (primitiveLiftLooseBVars x 0 1)
        (primitiveLiftLooseBVars y 0 1)
        (primitiveLiftLooseBVars fuel 0 1)
        (primitiveLiftLooseBVars hy 0 1)
        (.bvar 0) (primitiveLiftLooseBVars h 0 1)))) q(Nat.zero)

def natDivGoEquation : Expr × Expr :=
  let succ := mkApp q(Nat.succ)
  let le := mkApp2 q(@LE.le Nat _)
  let y := .bvar 4
  let hy := .bvar 3
  let fuel := .bvar 2
  let x := .bvar 1
  let h := .bvar 0
  let close body := .lam0 q(Nat) <|
    .lam0 (le q(Nat.succ Nat.zero) (.bvar 0)) <|
    .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 (le (succ (.bvar 0)) (succ (.bvar 1))) body
  let lhs := close <| natDivGoLhsBody y hy fuel x h
  let rhs := close <| natDivGoRhsBody y hy fuel x h
  (lhs, rhs)

/-- Validate the closed top-level and fuel-step equations for `Nat.mod`. -/
def checkNatModPrimitive (env : Environment) (v : DefinitionVal)
    (fail : ∀ {α}, M α) : M Unit := do
  unless env.contains ``Nat && env.contains ``Nat.sub && env.contains ``Bool &&
      env.contains ``Nat.ble && v.levelParams.isEmpty do fail
  _ ← checkType q(Nat → Nat → Nat)
  unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
  let zero := q(Nat.zero)
  let x := .bvar 0
  let mod := mkApp2 v.value
  let zeroL := .lam0 q(Nat) <| mod zero x
  let zeroR := .lam0 q(Nat) zero
  _ ← checkType zeroL
  _ ← checkType zeroR
  unless ← isDefEq zeroL zeroR do fail
  _ ← checkType q(Nat → Nat → Prop)
  unless ← isDefEq (← checkType q(@LE.le Nat _))
    q(Nat → Nat → Prop) do fail
  _ ← checkType q(∀ y, Nat.succ Nat.zero ≤ y →
    ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat)
  unless ← isDefEq (← checkType q(Nat.modCore.go))
    q(∀ y, Nat.succ Nat.zero ≤ y →
      ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) do fail
  Condition.natLE.checkForPrimitive fail
  let (topL, topR) := natModTopEquation v.value
  _ ← checkType topL
  _ ← checkType topR
  unless ← isDefEq topL topR do fail
  let (goL, goR) := natModGoEquation
  _ ← checkType goL
  _ ← checkType goR
  unless ← isDefEq goL goR do fail

/-- Validate the closed top-level and fuel-step equations for `Nat.div`. -/
def checkNatDivPrimitive (env : Environment) (v : DefinitionVal)
    (fail : ∀ {α}, M α) : M Unit := do
  unless env.contains ``Nat && env.contains ``Nat.sub && env.contains ``Bool &&
      env.contains ``Nat.ble && v.levelParams.isEmpty do fail
  _ ← checkType q(Nat → Nat → Nat)
  unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
  Condition.natLE.checkForPrimitive fail
  _ ← checkType q(Nat → Nat → Prop)
  unless ← isDefEq (← checkType q(@LE.le Nat _))
    q(Nat → Nat → Prop) do fail
  _ ← checkType q(∀ y, Nat.succ Nat.zero ≤ y →
    ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat)
  unless ← isDefEq (← checkType q(Nat.div.go))
    q(∀ y, Nat.succ Nat.zero ≤ y →
      ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) do fail
  let (topL, topR) := natDivTopEquation v.value
  _ ← checkType topL
  _ ← checkType topR
  unless ← isDefEq topL topR do fail
  let (goL, goR) := natDivGoEquation
  _ ← checkType goL
  _ ← checkType goR
  unless ← isDefEq goL goR do fail

def checkPrimitiveDefCore (v : DefinitionVal) : M Bool := do
  let fail {α} : M α := throw <| .other s!"invalid form for primitive def {v.name}"
  let tru := q(true)
  let fal := q(false)
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let add := mkApp2 q(Nat.add)
  let mod := mkApp2 q(Nat.mod)
  let div := mkApp2 q(Nat.div)
  let one := succ zero
  let two := succ one
  let defeq1 a b := isDefEq (.arrow q(Nat) a) (.arrow q(Nat) b)
  let x := .bvar 0
  let env ← getEnv
  match v.name with
  | ``Nat.add =>
    checkNatAddPrimitive env v fail
  | ``Nat.pred =>
    checkNatPredPrimitive env v fail
  | ``Nat.sub =>
    checkNatSubPrimitive env v fail
  | ``Nat.mul =>
    checkNatMulPrimitive env v fail
  | ``Nat.pow =>
    checkNatPowPrimitive env v fail
  | ``Nat.mod =>
    checkNatModPrimitive env v fail
  | ``Nat.div =>
    checkNatDivPrimitive env v fail
  | ``Nat.gcd =>
    unless env.contains ``Nat.mod && v.levelParams.isEmpty do fail
    -- gcd : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    withLocalDecl `m .default q(Nat) fun m => do
    withLocalDecl `n .default q(Nat) fun n => do
    let gcd' ← unfoldNatWellFounded v.value #[m, n] q(type_of% Nat.gcd.eq_def) fail
    let gcd' := mkApp2 gcd'
    let gcd := mkApp2 v.value
    unless ← isDefEq (gcd' zero m) m do fail
    unless ← isDefEq (gcd' (succ n) m) (gcd (mod m (succ n)) (succ n)) do fail
  | ``Nat.beq =>
    checkNatBEqPrimitive env v fail
  | ``Nat.ble =>
    checkNatBLEPrimitive env v fail
  | ``Nat.bitwise =>
    unless env.contains ``Nat && env.contains ``Bool && v.levelParams.isEmpty do fail
    -- bitwise : Nat → Nat → Nat
    unless ← isDefEq v.type q((Bool → Bool → Bool) → Nat → Nat → Nat) do fail
    withLocalDecl `f .default q(Bool → Bool → Bool) fun f => do
    withLocalDecl `n .default q(Nat) fun n => do
    withLocalDecl `m .default q(Nat) fun m => do
    let bitwise' ← unfoldNatWellFounded v.value #[f, n, m] q(type_of% Nat.bitwise.eq_def) fail
    let bitwise := mkApp3 v.value
    let c := Condition.natEq; c.check fail (ite := true)
    let bc := Condition.bool; bc.check fail (ite := true)
    let e :=
      c.ite q(Nat) #[n, zero] (bc.ite q(Nat) #[mkApp2 f q(false) q(true)] m zero) <|
      c.ite q(Nat) #[m, zero] (bc.ite q(Nat) #[mkApp2 f q(true) q(false)] n zero) <|
      let n' := div n two
      let m' := div m two
      let b₁ := c.decide #[mod n two, one]
      let b₂ := c.decide #[mod m two, one]
      let r := bitwise f n' m'
      bc.ite q(Nat) #[mkApp2 f b₁ b₂] (add (add r r) one) (add r r)
    _ ← checkType e
    unless ← isDefEq (mkApp3 bitwise' f n m) e do fail
  | ``Nat.land =>
    unless env.contains ``Nat.bitwise && v.levelParams.isEmpty do fail
    -- land : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let .app (.const ``Nat.bitwise []) and := v.value | fail
    let and := mkApp2 and
    unless ← defeq1 (and fal x) fal do fail
    unless ← defeq1 (and tru x) x do fail
  | ``Nat.lor =>
    unless env.contains ``Nat.bitwise && v.levelParams.isEmpty do fail
    -- lor : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let .app (.const ``Nat.bitwise []) or := v.value | fail
    let or := mkApp2 or
    unless ← defeq1 (or fal x) x do fail
    unless ← defeq1 (or tru x) tru do fail
  | ``Nat.xor =>
    unless env.contains ``Nat.bitwise && v.levelParams.isEmpty do fail
    -- xor : Nat → Nat → Nat
    unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
    let .app (.const ``Nat.bitwise []) xor := v.value | fail
    let xor := mkApp2 xor
    unless ← isDefEq (xor fal fal) fal do fail
    unless ← isDefEq (xor tru fal) tru do fail
    unless ← isDefEq (xor fal tru) tru do fail
    unless ← isDefEq (xor tru tru) fal do fail
  | ``Nat.shiftLeft =>
    checkNatShiftLeftPrimitive env v fail
  | ``Nat.shiftRight =>
    checkNatShiftRightPrimitive env v fail
  | ``Char.ofNat =>
    unless env.contains ``Nat && v.levelParams.isEmpty do fail
    -- Char : Type. Use checked inference here: unlike inference-only
    -- `ensureType`, this also enforces the declaration's safety boundary.
    _ ← ensureSort (← checkType q(Char)) q(Char)
    -- @Char.ofNat : Nat → Char
    unless ← isDefEq v.type q(Nat → Char) do fail
  | ``String.ofList =>
    unless v.levelParams.isEmpty do fail
    -- Char : Type
    _ ← ensureType q(Char)
    -- List Char : Type
    _ ← ensureType q(List Char)
    -- @List.nil.{0} Char : List Char
    unless ← isDefEq (← checkType q(List.nil (α := Char))) q(List Char) do fail
    -- @List.cons.{0} Char : Char → List Char → List Char
    unless ← isDefEq (← checkType q(List.cons (α := Char))) q(Char → List Char → List Char) do fail
    -- String.ofList : List Char → String
    unless ← isDefEq v.type q(List Char → String) do fail
  | _ => return false
  return true

def checkPrimitiveDef (v : DefinitionVal) : M Bool := do
  unless v.safety == .safe do return false
  checkPrimitiveDefCore v

def checkPrimitiveInductive (_env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Except Exception Bool := do
  unless !isUnsafe && lparams.isEmpty && nparams == 0 do return false
  let [type] := types | return false
  unless type.type == .sort (.succ .zero) do return false
  let fail {α} : Except Exception α :=
    throw <| .other s!"invalid form for primitive inductive {type.name}"
  match type.name with
  | ``Bool =>
    let [⟨``Bool.false, .const ``Bool []⟩, ⟨``Bool.true, .const ``Bool []⟩] := type.ctors | fail
  | ``Nat =>
    let [
      ⟨``Nat.zero, .const ``Nat []⟩,
      ⟨``Nat.succ, .forallE _ (.const ``Nat []) (.const ``Nat []) _⟩
    ] := type.ctors | fail
  | _ => return false
  return true

-- Self-test to ensure that the primitives check at compile time
run_meta
  let env ← Lean.getEnv
  for c in Environment.primitives do
    match env.find? c with
    | some (.defnInfo v) =>
      let (.true, _) ← Elab.Term.TermElabM.run (checkPrimitiveDef v)
        | throwError "{v.name}"
    | some (.inductInfo _) | some (.ctorInfo _) => pure ()
    | r => throwError "unexpected primitive: {r.map (·.name)}"
