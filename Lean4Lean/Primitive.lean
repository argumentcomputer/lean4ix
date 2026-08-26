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

/-- The closed Boolean selector used by well-founded primitive certificates.
Naming this expression lets the executable checker and its verification pin
the same selector equations without depending on local binder identities. -/
def Condition.boolNatITE (cond : Condition) : Expr :=
  .lam0 q(Bool) <| mkApp2 q(@_root_.ite Nat)
    (mkApp cond.prop (.bvar 0))
    (mkApp cond.dec (.bvar 0))

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

def Condition.natEqReflectProof : Expr :=
  q(fun n m {q : Prop} (H : _ → _ → q) =>
    H (@Nat.eq_of_beq_eq_true n m) (@Nat.ne_of_beq_eq_false n m))

def Condition.natEqReflectedFn : Expr :=
  .lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 Reflection.defn₂.toDec
    (mkApp2 Condition.natEq.prop (.bvar 1) (.bvar 0))
    (mkApp2 q(Nat.beq) (.bvar 1) (.bvar 0))
    (mkApp2 Condition.natEqReflectProof (.bvar 1) (.bvar 0))

def Condition.natEqDecideFn : Expr :=
  .lam0 q(Nat) <| .lam0 q(Nat) <| mkApp5 q(@_root_.ite.{1}) q(Bool)
    (mkApp2 Condition.natEq.prop (.bvar 1) (.bvar 0))
    (mkApp2 Condition.natEq.dec (.bvar 1) (.bvar 0)) q(true) q(false)

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

def Condition.natEqEvidenceExpressions : List Expr :=
  let r := Reflection.defn₂
  let iteTy := .arrow q(Prop) <| .arrow q(Bool) <|
    .arrow (mkApp2 r.type (.bvar 1) (.bvar 0))
      q(∀ α : Type, α → α → α)
  let trueL := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
      mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)
  let trueR := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
      .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1
  let falseL := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
      mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)
  let falseR := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
      .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0
  [Condition.natEq.dec, Condition.natEq.prop, q(Nat → Nat → Prop),
    r.type, q(Prop → Bool → Prop), r.ite, iteTy,
    trueL, trueR, falseL, falseR,
    Condition.natEqReflectedFn, Condition.natEqDecideFn,
    q(Nat → Nat → Bool), q(Nat.beq), Condition.natEqReflectProof]

def Condition.boolEvidenceExpressions : List Expr :=
  let ite := Condition.bool.boolNatITE
  [Condition.bool.dec, Condition.bool.prop, q(Bool → Prop),
    ite, q(Bool → Nat → Nat → Nat),
    mkApp ite q(true),
    .lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1,
    mkApp ite q(false),
    .lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0]

def checkExprTypes : List Expr → M Unit
  | [] => pure ()
  | e :: es => do
    _ ← checkType e
    checkExprTypes es

def Condition.natLE.checkForPrimitive
    (fail : ∀ {α}, M α) : M Unit := do
  checkExprTypes Condition.natLEEvidenceExpressions
  Condition.natLE.check fail (ite := true) (dite := true)

def Condition.natEq.checkForPrimitive
    (fail : ∀ {α}, M α) : M Unit := do
  checkExprTypes Condition.natEqEvidenceExpressions
  Condition.natEq.check fail (ite := true)

def Condition.bool.checkForPrimitive
    (fail : ∀ {α}, M α) : M Unit := do
  checkExprTypes Condition.boolEvidenceExpressions
  Condition.bool.check fail (ite := true)

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

def withLambda (e : Expr) (fail : ∀ {α}, M α)
    (k : Expr → Expr → M α) : M α :=
  match e with
  | .lam name dom body bi =>
    withLocalDecl name bi dom fun fv => k fv (body.instantiate1 fv)
  | _ => fail

def withForall (e : Expr) (fail : ∀ {α}, M α)
    (k : Expr → Expr → M α) : M α :=
  match e with
  | .forallE name dom body bi =>
    withLocalDecl name bi dom fun fv => k fv (body.instantiate1 fv)
  | _ => fail

/-- Transparent expression alpha-equivalence for checked certificate shapes.
Unlike the opaque runtime `Expr.eqv`, this relation has a proof-relevant model
counterpart in the verification layer. -/
def exprShapeEq : Expr → Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar i, .fvar j => i == j
  | .mvar i, .mvar j => i == j
  | .sort u, .sort v => u == v
  | .const n us, .const n' us' => n == n' && us == us'
  | .app f a, .app f' a' => exprShapeEq f f' && exprShapeEq a a'
  | .lam _ ty body _, .lam _ ty' body' _ =>
    exprShapeEq ty ty' && exprShapeEq body body'
  | .forallE _ ty body _, .forallE _ ty' body' _ =>
    exprShapeEq ty ty' && exprShapeEq body body'
  | .letE _ ty val body _, .letE _ ty' val' body' _ =>
    exprShapeEq ty ty' && exprShapeEq val val' && exprShapeEq body body'
  | .lit l, .lit l' => l == l'
  | .mdata _ e, .mdata _ e' => exprShapeEq e e'
  | .proj s i e, .proj s' i' e' =>
    s == s' && i == i' && exprShapeEq e e'
  | _, _ => false

/-- Structural loose-binder range used at the executable certificate
boundary. Unlike `Expr.hasLooseBVars`, this does not trust the packed cached
range stored in expression metadata. -/
def exprLooseBVarRange : Expr → Nat
  | .bvar i => i + 1
  | .const ..
  | .sort _
  | .fvar _
  | .mvar _
  | .lit _ => 0
  | .mdata _ e
  | .proj _ _ e => exprLooseBVarRange e
  | .app f a => max (exprLooseBVarRange f) (exprLooseBVarRange a)
  | .lam _ ty body _
  | .forallE _ ty body _ =>
    max (exprLooseBVarRange ty) (exprLooseBVarRange body - 1)
  | .letE _ ty val body _ =>
    max (max (exprLooseBVarRange ty) (exprLooseBVarRange val))
      (exprLooseBVarRange body - 1)

/-- Closed evidence recovered from a compiled `WellFounded.Nat.fix`.
`stateFn` is the compiler-selected packing function for the public arguments;
retaining it is what keeps the certificate generic in `PSigma`, `Prod`, or
any other definitionally valid state representation. -/
structure NatWellFoundedCoreResult where
  equation : Expr
  fixFn : Expr
  fixGo : Expr
  goFn : Expr
  measure : Expr
  functional : Expr
  state : Expr
  stateFn : Expr
  callLhs : Expr
  callRhs : Expr
  entryLhs : Expr
  entryRhs : Expr
  topLhs : Expr
  topRhs : Expr
  eagerFn : Expr
  eagerLhs : Expr
  eagerRhs : Expr
  boolTrueLhs : Expr
  boolTrueRhs : Expr
  boolFalseLhs : Expr
  boolFalseRhs : Expr
  stepLhs : Expr
  stepRhs : Expr
  specStepLhs : Expr
  specStepRhs : Expr

def unfoldNatWellFoundedCore (e : Expr) (fvs : Array Expr)
    (eq_def : Expr) (fail : ∀ {α}, M α) : M NatWellFoundedCoreResult := do
  let succ := mkApp q(Nat.succ)
  let x : Expr := .bvar 0
  let .app (.app _ lhs) rhs := eq_def.getForallBody.instantiateRev fvs
    | fail
  let orig := lhs.getAppFn
  let rhs := rhs.replace fun e' => if e' == orig then some e else none
  let e1 ← whnfCore (mkAppN e fvs)
  let e1 ← unfoldDefinition e1
  (← whnfCore e1).withApp fun fix args => do
  let .const ``WellFounded.Nat.fix [_, _] := fix | fail
  let #[α, motive, f, F, a₀] := args | fail
  let fixFn := mkAppN fix #[α, motive, f, F]
  let stateFn := (← getLCtx).mkLambda fvs a₀
  let call ← unfoldDefinition (.app fixFn a₀)
  let call ← whnfCore call
  let fixGo₀ ← call.withApp fun fixGo args => do
    let #[α', motive', f', F', fuel, a', _] := args | fail
    unless (α, motive, f, F, a₀) == (α', motive', f', F', a') do fail
    let .app _ _ := fuel | fail
    return fixGo
  let callLhs := (← getLCtx).mkLambda fvs (mkAppN e fvs)
  let callRhs := (← getLCtx).mkLambda fvs call
  unless ← isDefEq callLhs callRhs do fail
  let goFn := (← getLCtx).mkLambda fvs (mkAppN fixGo₀ #[α, motive, f, F])
  let entryLhs := (← getLCtx).mkLambda fvs (mkAppN e fvs)
  let entryRhs := (← getLCtx).mkLambda fvs (mkAppN fix args)
  unless ← isDefEq entryLhs entryRhs do fail
  withLocalDecl `a .default (← inferType a₀) fun a => do
  let e1 ← unfoldDefinition (.app fixFn a)
  let e1 ← whnfCore e1
  let topLhs := (← getLCtx).mkLambda (fvs.push a) (.app fixFn a)
  let topRhs := (← getLCtx).mkLambda (fvs.push a) e1
  unless ← isDefEq topLhs topRhs do fail
  let (fixGo, eagerFn, eagerLhs, eagerRhs, boolTrueLhs, boolTrueRhs,
      boolFalseLhs, boolFalseRhs, stepLhs, stepRhs) ←
    e1.withApp fun fixGo args => do
    let #[α', motive', f', F', fuel, a', _] := args | fail
    unless (α, motive, f, F, a) == (α', motive', f', F', a') do fail
    unless fixGo == fixGo₀ do fail
    let .app eager n := fuel | fail
    unless ← isDefEq n (succ (.app f a)) do fail
    unless (← getEnv).contains ``Nat.beq do fail
    let c := Condition.bool
    c.check fail (ite := true)
    let boolTrueLhs := mkApp c.boolNatITE q(true)
    let boolTrueRhs := .lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1
    let boolFalseLhs := mkApp c.boolNatITE q(false)
    let boolFalseRhs := .lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0
    unless ← isDefEq boolTrueLhs boolTrueRhs do fail
    unless ← isDefEq boolFalseLhs boolFalseRhs do fail
    let eagerLhs := .lam0 q(Nat) (mkApp eager x)
    let eagerRhs := .lam0 q(Nat)
      (mkApp3 c.boolNatITE (mkApp2 (.const ``Nat.beq []) x x) x x)
    unless ← isDefEq eagerLhs eagerRhs do fail
    let go' ← unfoldDefinition fixGo
    withLambda go' fail fun αv go' =>
    withLambda go' fail fun motivev go' =>
    withLambda go' fail fun fv go' =>
    withLambda go' fail fun F go' =>
    withLambda go' fail fun t go' => do
    let .app natRec t' := go' | fail
    unless !natRec.containsFVar t.fvarId! && t == t' do fail
    _ ← checkType (succ t)
    let gor ← whnfCore (.app natRec (succ t))
    let stepLhs := (← getLCtx).mkLambda #[αv, motivev, fv, F, t]
      (mkAppN fixGo #[αv, motivev, fv, F, succ t])
    let goPred := mkAppN fixGo #[αv, motivev, fv, F, t]
    let gor' := gor.replace fun e' =>
      if e' == .app natRec t then some goPred else none
    let stepRhs := (← getLCtx).mkLambda #[αv, motivev, fv, F, t] gor'
    unless ← isDefEq stepLhs stepRhs do fail
    withLambda gor fail fun x gor =>
    withLambda gor fail fun _ gor => do
    let .app Fx ih := gor | fail
    unless .app F x == Fx do fail
    withLambda ih fail fun y ih =>
    withLambda ih fail fun _ ih => do
    let .app ih _ := ih | fail
    unless ih == .app (.app natRec t) y do fail
    return (fixGo, eager, eagerLhs, eagerRhs, boolTrueLhs, boolTrueRhs,
      boolFalseLhs, boolFalseRhs, stepLhs, stepRhs)
  let specStepLhs ← whnfCore (mkAppN stepLhs #[α, motive, f, F])
  let specStepRhs ← whnfCore (mkAppN stepRhs #[α, motive, f, F])
  let specStepLhs := (← getLCtx).mkLambda fvs specStepLhs
  let specStepRhs := (← getLCtx).mkLambda fvs specStepRhs
  unless ← isDefEq specStepLhs specStepRhs do fail
  let .forallE _ dom _ _ ← inferType (.app F a₀) | fail
  let ih' ← withForall dom fail fun y dom =>
    withForall dom fail fun h _ => do
    return (← getLCtx).mkLambda #[y, h] (.app fixFn y)
  have rhs' := mkApp2 F a₀ ih'
  _ ← checkType rhs'
  unless ← isDefEq rhs rhs' do fail
  return {
    equation := (← getLCtx).mkLambda fvs rhs
    fixFn
    fixGo
    goFn
    measure := f
    functional := F
    state := a₀
    stateFn
    callLhs
    callRhs
    entryLhs
    entryRhs
    topLhs
    topRhs
    eagerFn
    eagerLhs
    eagerRhs
    boolTrueLhs
    boolTrueRhs
    boolFalseLhs
    boolFalseRhs
    stepLhs
    stepRhs
    specStepLhs
    specStepRhs }

@[irreducible] def checkNatWellFoundedEquation
    (lhs rhs : Expr) : M Unit := do
  let fail {α} : M α :=
    throw <| .other "invalid well-founded recursion certificate"
  unless !lhs.hasFVar && !lhs.hasMVar &&
      !rhs.hasFVar && !rhs.hasMVar do fail
  _ ← checkType lhs
  _ ← checkType rhs
  unless ← isDefEq lhs rhs do fail

def NatWellFoundedCoreResult.expectedEagerLhs
    (r : NatWellFoundedCoreResult) : Expr :=
  let x : Expr := .bvar 0
  .lam0 q(Nat) <| mkApp r.eagerFn x

def NatWellFoundedCoreResult.expectedEagerRhs
    (_r : NatWellFoundedCoreResult) : Expr :=
  let x : Expr := .bvar 0
  .lam0 q(Nat) <| mkApp3 Condition.bool.boolNatITE
    (mkApp2 (.const ``Nat.beq []) x x) x x

def NatWellFoundedCoreResult.expectedBoolTrueLhs
    (_r : NatWellFoundedCoreResult) : Expr :=
  mkApp Condition.bool.boolNatITE q(true)

def NatWellFoundedCoreResult.expectedBoolTrueRhs
    (_r : NatWellFoundedCoreResult) : Expr :=
  .lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1

def NatWellFoundedCoreResult.expectedBoolFalseLhs
    (_r : NatWellFoundedCoreResult) : Expr :=
  mkApp Condition.bool.boolNatITE q(false)

def NatWellFoundedCoreResult.expectedBoolFalseRhs
    (_r : NatWellFoundedCoreResult) : Expr :=
  .lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0

def NatWellFoundedCoreResult.auxShape
    (r : NatWellFoundedCoreResult) : Bool :=
  exprShapeEq r.eagerLhs r.expectedEagerLhs &&
  exprShapeEq r.eagerRhs r.expectedEagerRhs &&
  exprShapeEq r.boolTrueLhs r.expectedBoolTrueLhs &&
  exprShapeEq r.boolTrueRhs r.expectedBoolTrueRhs &&
  exprShapeEq r.boolFalseLhs r.expectedBoolFalseLhs &&
  exprShapeEq r.boolFalseRhs r.expectedBoolFalseRhs &&
  exprShapeEq r.eagerFn q(WellFounded.Nat.eager) &&
  exprLooseBVarRange r.goFn == 0 && exprLooseBVarRange r.stateFn == 0

@[irreducible] def checkNatWellFoundedCertificate
    (r : NatWellFoundedCoreResult) : M Unit := do
  unless r.auxShape do
    throw <| .other "invalid well-founded recursion auxiliary certificate"
  checkNatWellFoundedEquation r.callLhs r.callRhs
  checkNatWellFoundedEquation r.entryLhs r.entryRhs
  checkNatWellFoundedEquation r.topLhs r.topRhs
  checkNatWellFoundedEquation r.eagerLhs r.eagerRhs
  checkNatWellFoundedEquation r.boolTrueLhs r.boolTrueRhs
  checkNatWellFoundedEquation r.boolFalseLhs r.boolFalseRhs
  checkNatWellFoundedEquation r.stepLhs r.stepRhs
  checkNatWellFoundedEquation r.specStepLhs r.specStepRhs

/-- Close the equation theorem's telescope and replace its original function
head by the candidate implementation. -/
def natWellFoundedEquation (e : Expr) : Expr → Option Expr
  | .forallE name dom body bi =>
    (natWellFoundedEquation e body).map fun body => .lam name dom body bi
  | .app (.app _ lhs) rhs =>
    some <| rhs.replace fun e' =>
      if e' == lhs.getAppFn then some e else none
  | _ => none

/-- The closed branch equation checked for a candidate implementation of
`Nat.bitwise`. -/
def natBitwiseEquation (bitwise : Expr) : Expr :=
  let f := .bvar 2
  let n := .bvar 1
  let m := .bvar 0
  let zero := q(Nat.zero)
  let one := mkApp q(Nat.succ) zero
  let two := mkApp q(Nat.succ) one
  let add := mkApp2 q(Nat.add)
  let mod := mkApp2 q(Nat.mod)
  let div := mkApp2 q(Nat.div)
  let bitwise := mkApp3 bitwise
  let c := Condition.natEq
  let bc := Condition.bool
  let body :=
    c.ite q(Nat) #[n, zero]
      (bc.ite q(Nat) #[mkApp2 f q(false) q(true)] m zero) <|
    c.ite q(Nat) #[m, zero]
      (bc.ite q(Nat) #[mkApp2 f q(true) q(false)] n zero) <|
    let n' := div n two
    let m' := div m two
    let b₁ := c.decide #[mod n two, one]
    let b₂ := c.decide #[mod m two, one]
    let r := bitwise f n' m'
    bc.ite q(Nat) #[mkApp2 f b₁ b₂]
      (add (add r r) one) (add r r)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) body

def natBitwiseZeroEquation (equation : Expr) : Expr × Expr :=
  let f := .bvar 1
  let b := .bvar 0
  let zero := q(Nat.zero)
  let close body := .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) body
  (close <| mkApp3 equation f zero b,
    close <| mkApp3 Condition.bool.boolNatITE
      (mkApp2 f q(false) q(true)) b zero)

def natBitwiseZeroRightEquation (equation : Expr) : Expr × Expr :=
  let f := .bvar 1
  let zero := q(Nat.zero)
  let a := mkApp q(Nat.succ) (.bvar 0)
  let close body := .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) body
  (close <| mkApp3 equation f a zero,
    close <| mkApp3 Condition.bool.boolNatITE
      (mkApp2 f q(true) q(false)) a zero)

def natBitwiseSuccEquation (equation bitwise : Expr) : Expr × Expr :=
  let f := .bvar 2
  let a := mkApp q(Nat.succ) (.bvar 1)
  let b := mkApp q(Nat.succ) (.bvar 0)
  let zero := q(Nat.zero)
  let one := mkApp q(Nat.succ) zero
  let two := mkApp q(Nat.succ) one
  let add := mkApp2 q(Nat.add)
  let mod := mkApp2 q(Nat.mod)
  let div := mkApp2 q(Nat.div)
  let c := Condition.natEq
  let n' := div a two
  let m' := div b two
  let b₁ := c.decide #[mod a two, one]
  let b₂ := c.decide #[mod b two, one]
  let r := mkApp3 bitwise f n' m'
  let close body := .lam0 q(Bool → Bool → Bool) <|
    .lam0 q(Nat) <| .lam0 q(Nat) body
  (close <| mkApp3 equation f a b,
    close <| mkApp3 Condition.bool.boolNatITE (mkApp2 f b₁ b₂)
      (add (add r r) one) (add r r))

/-- Transactionally discover a compiled fixpoint and then independently
check every closed equation retained in its certificate. -/
def unfoldNatWellFoundedCert (e : Expr) (fvs : Array Expr)
    (eq_def : Expr) (fail : ∀ {α}, M α) : M NatWellFoundedCoreResult := do
  let some equation := natWellFoundedEquation e eq_def | fail
  let cert ← M.sandbox (unfoldNatWellFoundedCore e fvs eq_def fail)
  unless cert.equation == equation do
    throw <| .other "invalid well-founded recursion equation"
  checkNatWellFoundedCertificate cert
  return cert

/-- Compatibility projection for the still equation-only bitwise branch. -/
def unfoldNatWellFounded (e : Expr) (fvs : Array Expr)
    (eq_def : Expr) (fail : ∀ {α}, M α) : M Expr := do
  let some equation := natWellFoundedEquation e eq_def | fail
  _ ← unfoldNatWellFoundedCert e fvs eq_def fail
  return equation

def unfoldNatWellFoundedNat2Cert (e eq_def : Expr)
    (fail : ∀ {α}, M α) : M NatWellFoundedCoreResult := do
  let some equation := natWellFoundedEquation e eq_def | fail
  let cert ← withLocalDecl `m .default q(Nat) fun m =>
    withLocalDecl `n .default q(Nat) fun n =>
      M.sandbox (unfoldNatWellFoundedCore e #[m, n] eq_def fail)
  unless cert.equation == equation do
    throw <| .other "invalid well-founded recursion equation"
  checkNatWellFoundedCertificate cert
  return cert

def unfoldNatWellFoundedBoolNat2Cert (e eq_def : Expr)
    (fail : ∀ {α}, M α) : M NatWellFoundedCoreResult := do
  let some equation := natWellFoundedEquation e eq_def | fail
  let cert ← withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
    withLocalDecl `n .default q(Nat) fun n =>
      withLocalDecl `m .default q(Nat) fun m =>
        M.sandbox (unfoldNatWellFoundedCore e #[f, n, m] eq_def fail)
  unless cert.equation == equation do
    throw <| .other "invalid well-founded recursion equation"
  checkNatWellFoundedCertificate cert
  return cert

/-- GCD specialization of a generic fixpoint certificate. The packed state is
always reconstructed by applying `core.stateFn`; no concrete pair encoding is
part of the accepted boundary. -/
structure NatGcdFixCertificate where
  core : NatWellFoundedCoreResult
  topLhs : Expr
  topRhs : Expr
  topProof : Expr
  zeroLhs : Expr
  zeroRhs : Expr
  zeroProofType : Expr
  succLhs : Expr
  succRhs : Expr
  succProofType : Expr
  succProof : Expr

def NatGcdFixCertificate.stateExpr (r : NatGcdFixCertificate)
    (a b : Expr) : Expr :=
  mkApp2 r.core.stateFn a b

private def natGcdCall (gcd : Expr) : Expr :=
  .lam0 q(Nat) <| .lam0 q(Nat) <|
    mkApp2 gcd (.bvar 1) (.bvar 0)

def NatGcdFixCertificate.expectedTopLhs
    (_r : NatGcdFixCertificate) (gcd : Expr) : Expr :=
  natGcdCall gcd

def NatGcdFixCertificate.expectedTopRhs
    (r : NatGcdFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  .lam0 q(Nat) <| .lam0 q(Nat) <| mkAppN r.core.goFn
    #[zero, zero, mkApp q(WellFounded.Nat.eager) (succ (.bvar 1)),
      r.stateExpr (.bvar 1) (.bvar 0), r.topProof]

def NatGcdFixCertificate.expectedZeroLhs
    (r : NatGcdFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let go := mkApp2 r.core.goFn zero zero
  .lam0 q(Nat) <| .lam0 q(Nat) <| .lam0 r.zeroProofType <|
    mkAppN go #[succ (.bvar 2), r.stateExpr zero (.bvar 1), .bvar 0]

def NatGcdFixCertificate.expectedZeroRhs
    (r : NatGcdFixCertificate) : Expr :=
  .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 r.zeroProofType <| .bvar 1

def NatGcdFixCertificate.expectedSuccLhs
    (r : NatGcdFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let go := mkApp2 r.core.goFn zero zero
  let sa := succ (.bvar 2)
  .lam0 q(Nat) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 r.succProofType <| mkAppN go
      #[succ (.bvar 3), r.stateExpr sa (.bvar 1), .bvar 0]

def NatGcdFixCertificate.expectedSuccRhs
    (r : NatGcdFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let go := mkApp2 r.core.goFn zero zero
  let sa := succ (.bvar 2)
  .lam0 q(Nat) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 r.succProofType <| mkAppN go #[.bvar 3,
      r.stateExpr (mkApp2 q(Nat.mod) (.bvar 1) sa) sa, r.succProof]

def NatGcdFixCertificate.shape
    (r : NatGcdFixCertificate) (gcd : Expr) : Bool :=
  exprShapeEq r.topLhs (r.expectedTopLhs gcd) &&
  exprShapeEq r.topRhs r.expectedTopRhs &&
  exprShapeEq r.zeroLhs r.expectedZeroLhs &&
  exprShapeEq r.zeroRhs r.expectedZeroRhs &&
  exprShapeEq r.succLhs r.expectedSuccLhs &&
  exprShapeEq r.succRhs r.expectedSuccRhs

def specializeNatGcdFixCertificate (core : NatWellFoundedCoreResult)
    (_fail : ∀ {α}, M α) : M NatGcdFixCertificate := do
  let reject {α} (message : String) : M α :=
    throw <| .other s!"invalid Nat.gcd specialization: {message}"
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let stateExpr a b := mkApp2 core.stateFn a b
  let go := mkApp2 core.goFn zero zero
  let topRhs ← withLambda core.callRhs
      (reject "top equation lacks its first lambda") fun m body =>
    withLambda body (reject "top equation lacks its second lambda") fun n body => do
      let args := body.getAppArgs
      unless body.getAppFn == core.fixGo && args.size == 7 do
        reject "top equation does not call the retained fixpoint"
      let .app eager _ := args[4]!
        | reject "top equation has malformed eager fuel"
      return (← getLCtx).mkLambda #[m, n]
        (mkAppN go #[mkApp eager (succ m), stateExpr m n, args[6]!])
  let topLhs := core.callLhs
  let (zeroLhs, zeroRhs) ← withLocalDecl `fuel .default q(Nat) fun fuel =>
    withLocalDecl `b .default q(Nat) fun b => do
      let stepR := mkApp3 core.specStepRhs zero zero fuel
      let state := stateExpr zero b
      let lhsFn := mkApp2 go (succ fuel) state
      let .forallE _ hpTy _ _ ← inferType lhsFn
        | reject "zero call has no proof binder"
      withLocalDecl `hp .default hpTy fun hp => do
        let lhs := mkApp lhsFn hp
        _ ← whnfCore (mkApp (mkApp stepR state) hp)
        return ((← getLCtx).mkLambda #[fuel, b, hp] lhs,
          (← getLCtx).mkLambda #[fuel, b, hp] b)
  let (succLhs, succRhs) ← withLocalDecl `fuel .default q(Nat) fun fuel =>
    withLocalDecl `a .default q(Nat) fun a =>
      withLocalDecl `b .default q(Nat) fun b => do
        let sa := succ a
        let stepR := mkApp3 core.specStepRhs zero zero fuel
        let state := stateExpr sa b
        let lhsFn := mkApp2 go (succ fuel) state
        let .forallE _ hpTy _ _ ← inferType lhsFn
          | reject "successor call has no proof binder"
        withLocalDecl `hp .default hpTy fun hp => do
          let lhs := mkApp lhsFn hp
          let rhs ← whnfCore (mkApp (mkApp stepR state) hp)
          let rhs ← unfoldDefinition rhs
          let rhs ← whnfCore rhs
          let rhs ← unfoldDefinition rhs
          let rhs ← whnfCore rhs
          let rhs ← if rhs.getAppFn == core.fixGo then
            pure rhs
          else
            rhs.withApp fun decCases args => do
              let .const ``Decidable.casesOn _ := decCases
                | throw <| .other
                    s!"invalid Nat.gcd specialization: successor branch head is {decCases} in {rhs}"
              unless args.size == 5 do
                reject "successor Decidable.casesOn has the wrong arity"
              let isFalse := args[3]!
              whnfCore (mkApp isFalse (mkApp q(Nat.succ_ne_zero) a))
          let args := rhs.getAppArgs
          unless rhs.getAppFn == core.fixGo && args.size == 7 do
            throw <| .other s!"invalid gcd recursive call: {rhs}"
          let recState := stateExpr (mkApp2 q(Nat.mod) b sa) sa
          let rhs := mkAppN go #[fuel, recState, args[6]!]
          return ((← getLCtx).mkLambda #[fuel, a, b, hp] lhs,
            (← getLCtx).mkLambda #[fuel, a, b, hp] rhs)
  let .lam _ _ (.lam _ _ topBody _) _ := topRhs
    | reject "closed top equation has the wrong shape"
  let topProof := topBody.getAppArgs[4]!
  let .lam _ _ (.lam _ _ (.lam _ zeroProofType _ _) _) _ := zeroLhs
    | reject "closed zero equation has the wrong shape"
  let .lam _ _ (.lam _ _ (.lam _ _ (.lam _ succProofType _ _) _) _) _ :=
    succLhs | reject "closed successor LHS has the wrong shape"
  let .lam _ _ (.lam _ _ (.lam _ _ (.lam _ _ succBody _) _) _) _ :=
    succRhs | reject "closed successor RHS has the wrong shape"
  let succProof := succBody.getAppArgs[4]!
  return {
    core
    topLhs
    topRhs
    topProof
    zeroLhs
    zeroRhs
    zeroProofType
    succLhs
    succRhs
    succProofType
    succProof }

def checkNatGcdFixCertificate (core : NatWellFoundedCoreResult)
    (gcd : Expr) (fail : ∀ {α}, M α) : M NatGcdFixCertificate := do
  let cert ← M.sandbox (specializeNatGcdFixCertificate core fail)
  unless cert.shape gcd do
    throw <| .other "invalid Nat.gcd well-founded recursion certificate"
  checkNatWellFoundedCertificate cert.core
  checkNatWellFoundedEquation cert.topLhs cert.topRhs
  checkNatWellFoundedEquation cert.zeroLhs cert.zeroRhs
  checkNatWellFoundedEquation cert.succLhs cert.succRhs
  return cert

/-- Bitwise specialization of a generic well-founded certificate. The
compiler-selected state representation is retained through `core.stateFn`;
the accepted boundary does not require `PSigma` (or any other pair type). -/
structure NatBitwiseFixCertificate where
  core : NatWellFoundedCoreResult
  callFn : Expr
  topLhs : Expr
  topRhs : Expr
  topProof : Expr
  zeroLhs : Expr
  zeroRhs : Expr
  zeroProofType : Expr
  zeroRightLhs : Expr
  zeroRightRhs : Expr
  zeroRightProofType : Expr
  succLhs : Expr
  succRhs : Expr
  succProofType : Expr
  succProof : Expr

def NatBitwiseFixCertificate.stateExpr (r : NatBitwiseFixCertificate)
    (f a b : Expr) : Expr :=
  mkAppN r.core.stateFn #[f, a, b]

private def natBitwiseCall (bitwise : Expr) : Expr :=
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    mkApp3 bitwise (.bvar 2) (.bvar 1) (.bvar 0)

def NatBitwiseFixCertificate.expectedTopLhs
    (_r : NatBitwiseFixCertificate) (bitwise : Expr) : Expr :=
  natBitwiseCall bitwise

def NatBitwiseFixCertificate.expectedTopRhs
    (r : NatBitwiseFixCertificate) : Expr :=
  let succ := mkApp q(Nat.succ)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    mkAppN r.callFn #[.bvar 2,
      mkApp q(WellFounded.Nat.eager) (succ (.bvar 1)),
      .bvar 1, .bvar 0, r.topProof]

def NatBitwiseFixCertificate.expectedZeroLhs
    (r : NatBitwiseFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 r.zeroProofType <| mkAppN r.callFn
      #[.bvar 3, succ (.bvar 2), zero, .bvar 1, .bvar 0]

def NatBitwiseFixCertificate.expectedZeroRhs
    (r : NatBitwiseFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 r.zeroProofType <| mkApp3 Condition.bool.boolNatITE
      (mkApp2 (.bvar 3) q(false) q(true)) (.bvar 1) zero

def NatBitwiseFixCertificate.expectedZeroRightLhs
    (r : NatBitwiseFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 r.zeroRightProofType <| mkAppN r.callFn
      #[.bvar 3, succ (.bvar 2), succ (.bvar 1), zero, .bvar 0]

def NatBitwiseFixCertificate.expectedZeroRightRhs
    (r : NatBitwiseFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 r.zeroRightProofType <| mkApp3 Condition.bool.boolNatITE
      (mkApp2 (.bvar 3) q(true) q(false)) (succ (.bvar 1)) zero

def NatBitwiseFixCertificate.expectedSuccLhs
    (r : NatBitwiseFixCertificate) : Expr :=
  let succ := mkApp q(Nat.succ)
  let sa := succ (.bvar 2)
  let sb := succ (.bvar 1)
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 q(Nat) <| .lam0 r.succProofType <| mkAppN r.callFn
      #[.bvar 4, succ (.bvar 3), sa, sb, .bvar 0]

def NatBitwiseFixCertificate.expectedSuccRhs
    (r : NatBitwiseFixCertificate) : Expr :=
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let one := succ zero
  let two := succ one
  let add := mkApp2 q(Nat.add)
  let div := mkApp2 q(Nat.div)
  let mod := mkApp2 q(Nat.mod)
  let sa := succ (.bvar 2)
  let sb := succ (.bvar 1)
  let bit₁ := Condition.natEq.decide #[mod sa two, one]
  let bit₂ := Condition.natEq.decide #[mod sb two, one]
  let recursiveCall := mkAppN r.callFn #[.bvar 4, .bvar 3,
    div sa two, div sb two, r.succProof]
  .lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <| .lam0 q(Nat) <|
    .lam0 q(Nat) <| .lam0 r.succProofType <|
      mkApp3 Condition.bool.boolNatITE (mkApp2 (.bvar 4) bit₁ bit₂)
        (add (add recursiveCall recursiveCall) one)
        (add recursiveCall recursiveCall)

def NatBitwiseFixCertificate.shape
    (r : NatBitwiseFixCertificate) (bitwise : Expr) : Bool :=
  exprShapeEq r.topLhs (r.expectedTopLhs bitwise) &&
  exprShapeEq r.topRhs r.expectedTopRhs &&
  exprShapeEq r.zeroLhs r.expectedZeroLhs &&
  exprShapeEq r.zeroRhs r.expectedZeroRhs &&
  exprShapeEq r.zeroRightLhs r.expectedZeroRightLhs &&
  exprShapeEq r.zeroRightRhs r.expectedZeroRightRhs &&
  exprShapeEq r.succLhs r.expectedSuccLhs &&
  exprShapeEq r.succRhs r.expectedSuccRhs &&
  exprLooseBVarRange r.callFn == 0 &&
  !r.callFn.hasFVar && !r.callFn.hasMVar

def specializeNatBitwiseFixCertificate (core : NatWellFoundedCoreResult)
    (_fail : ∀ {α}, M α) : M NatBitwiseFixCertificate := do
  let reject {α} (message : String) : M α :=
    throw <| .other s!"invalid Nat.bitwise specialization: {message}"
  let zero := q(Nat.zero)
  let succ := mkApp q(Nat.succ)
  let stateExpr f a b := mkAppN core.stateFn #[f, a, b]
  let callFn ← withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
    withLocalDecl `fuel .default q(Nat) fun fuel =>
      withLocalDecl `a .default q(Nat) fun a =>
        withLocalDecl `b .default q(Nat) fun b => do
          let go := mkAppN core.goFn #[f, a, b]
          let lhsFn := mkApp2 go fuel (stateExpr f a b)
          let .forallE _ hpTy _ _ ← inferType lhsFn
            | reject "generic call has no proof binder"
          withLocalDecl `hp .default hpTy fun hp =>
            return (← getLCtx).mkLambda #[f, fuel, a, b, hp]
              (mkApp lhsFn hp)
  let topRhs ← withLambda core.callRhs
      (reject "top equation lacks its operation lambda") fun f body =>
    withLambda body
        (reject "top equation lacks its first Nat lambda") fun n body =>
      withLambda body
          (reject "top equation lacks its second Nat lambda") fun m body => do
        let args := body.getAppArgs
        unless body.getAppFn == core.fixGo && args.size == 7 do
          reject "top equation does not call the retained fixpoint"
        let .app eager _ := args[4]!
          | reject "top equation has malformed eager fuel"
        return (← getLCtx).mkLambda #[f, n, m]
          (mkAppN callFn #[f, mkApp eager (succ n), n, m, args[6]!])
  let .lam _ _ (.lam _ _ (.lam _ _ topBody _) _) _ := topRhs
    | reject "closed top equation has the wrong shape"
  let topProof := topBody.getAppArgs[4]!
  let (zeroLhs, zeroRhs) ←
    withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
      withLocalDecl `fuel .default q(Nat) fun fuel =>
        withLocalDecl `b .default q(Nat) fun b => do
          let lhsFn := mkAppN callFn #[f, succ fuel, zero, b]
          let .forallE _ hpTy _ _ ← inferType lhsFn
            | reject "zero call has no proof binder"
          withLocalDecl `hp .default hpTy fun hp =>
            return ((← getLCtx).mkLambda #[f, fuel, b, hp] (mkApp lhsFn hp),
              (← getLCtx).mkLambda #[f, fuel, b, hp] <|
                mkApp3 Condition.bool.boolNatITE
                  (mkApp2 f q(false) q(true)) b zero)
  let (zeroRightLhs, zeroRightRhs) ←
    withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
      withLocalDecl `fuel .default q(Nat) fun fuel =>
        withLocalDecl `a .default q(Nat) fun a => do
          let sa := succ a
          let lhsFn := mkAppN callFn #[f, succ fuel, sa, zero]
          let .forallE _ hpTy _ _ ← inferType lhsFn
            | reject "right-zero call has no proof binder"
          withLocalDecl `hp .default hpTy fun hp =>
            return ((← getLCtx).mkLambda #[f, fuel, a, hp] (mkApp lhsFn hp),
              (← getLCtx).mkLambda #[f, fuel, a, hp] <|
                mkApp3 Condition.bool.boolNatITE
                  (mkApp2 f q(true) q(false)) sa zero)
  let (succLhs, succRhs) ←
    withLocalDecl `f .default q(Bool → Bool → Bool) fun f =>
      withLocalDecl `fuel .default q(Nat) fun fuel =>
        withLocalDecl `a .default q(Nat) fun a =>
          withLocalDecl `b .default q(Nat) fun b => do
            let sa := succ a
            let sb := succ b
            let state := stateExpr f sa sb
            let lhsFn := mkAppN callFn #[f, succ fuel, sa, sb]
            let .forallE _ hpTy _ _ ← inferType lhsFn
              | reject "successor call has no proof binder"
            withLocalDecl `hp .default hpTy fun hp => do
              let lhs := mkApp lhsFn hp
              let mut rhs := mkApp2
                (mkAppN core.specStepRhs #[f, sa, sb, fuel]) state hp
              rhs ← whnfCore rhs
              rhs ← unfoldDefinition rhs
              rhs ← whnfCore rhs
              rhs ← unfoldDefinition rhs
              rhs ← whnfCore rhs
              rhs ← rhs.withApp fun decCases args => do
                let .const ``Decidable.casesOn _ := decCases
                  | reject "first successor split is not Decidable.casesOn"
                unless args.size == 5 do
                  reject "first successor split has the wrong arity"
                whnfCore (mkApp args[3]! (mkApp q(Nat.succ_ne_zero) a))
              rhs ← whnfCore rhs
              rhs ← unfoldDefinition rhs
              rhs ← whnfCore rhs
              rhs ← rhs.withApp fun decCases args => do
                let .const ``Decidable.casesOn _ := decCases
                  | reject "second successor split is not Decidable.casesOn"
                unless args.size == 5 do
                  reject "second successor split has the wrong arity"
                whnfCore (mkApp args[3]! (mkApp q(Nat.succ_ne_zero) b))
              rhs ← whnfCore rhs
              rhs ← unfoldDefinition rhs
              rhs ← whnfCore rhs
              let some recThunk := rhs.find? fun e =>
                  let args := e.getAppArgs
                  args.size == 2 && e.getAppFn.isLambda &&
                    (e.getAppFn.find? fun e' =>
                      e'.getAppFn == core.fixGo).isSome
                | reject "missing recursive-call thunk"
              let recCall ← whnfCore recThunk
              let recArgs := recCall.getAppArgs
              unless recCall.getAppFn == core.fixGo && recArgs.size == 7 do
                reject "recursive-call thunk does not expose the fixpoint"
              let one := succ zero
              let two := succ one
              let add := mkApp2 q(Nat.add)
              let div := mkApp2 q(Nat.div)
              let mod := mkApp2 q(Nat.mod)
              let recState := stateExpr f (div sa two) (div sb two)
              unless ← isDefEq recArgs[5]! recState do
                reject "recursive call uses the wrong packed state"
              let recProof := recArgs[6]!
              let bit₁ := Condition.natEq.decide #[mod sa two, one]
              let bit₂ := Condition.natEq.decide #[mod sb two, one]
              let recursiveCall := mkAppN callFn #[f, fuel,
                div sa two, div sb two, recProof]
              let canonicalRhs := mkApp3 Condition.bool.boolNatITE
                (mkApp2 f bit₁ bit₂)
                (add (add recursiveCall recursiveCall) one)
                (add recursiveCall recursiveCall)
              return ((← getLCtx).mkLambda #[f, fuel, a, b, hp] lhs,
                (← getLCtx).mkLambda #[f, fuel, a, b, hp] canonicalRhs)
  let .lam _ _ (.lam _ _ (.lam _ _ (.lam _ zeroProofType _ _) _) _) _ :=
    zeroLhs
    | reject "closed zero LHS has the wrong shape"
  let .lam _ _ (.lam _ _ (.lam _ _
      (.lam _ zeroRightProofType _ _) _) _) _ :=
    zeroRightLhs | reject "closed right-zero LHS has the wrong shape"
  let .lam _ _ (.lam _ _ (.lam _ _ (.lam _ _
      (.lam _ succProofType _ _) _) _) _) _ :=
    succLhs | reject "closed successor LHS has the wrong shape"
  let some succCall := succRhs.find? fun e =>
      e.getAppFn == callFn && e.getAppArgs.size == 5
    | reject "closed successor RHS lacks its recursive call"
  let succProof := succCall.getAppArgs[4]!
  return {
    core
    callFn
    topLhs := core.callLhs
    topRhs
    topProof
    zeroLhs
    zeroRhs
    zeroProofType
    zeroRightLhs
    zeroRightRhs
    zeroRightProofType
    succLhs
    succRhs
    succProofType
    succProof }

def checkNatBitwiseFixCertificate (core : NatWellFoundedCoreResult)
    (bitwise : Expr) (fail : ∀ {α}, M α) : M NatBitwiseFixCertificate := do
  let cert ← M.sandbox (specializeNatBitwiseFixCertificate core fail)
  unless cert.shape bitwise do
    throw <| .other "invalid Nat.bitwise well-founded recursion certificate"
  _ ← checkType cert.callFn
  checkNatWellFoundedCertificate cert.core
  checkNatWellFoundedEquation cert.topLhs cert.topRhs
  checkNatWellFoundedEquation cert.zeroLhs cert.zeroRhs
  checkNatWellFoundedEquation cert.zeroRightLhs cert.zeroRightRhs
  checkNatWellFoundedEquation cert.succLhs cert.succRhs
  return cert

/-- Expose one definitional reduction step under a lambda. This preserves the
legacy GCD zero-case acceptance check alongside the stronger certificate. -/
def reduceNatWellFoundedLam1 (e : Expr)
    (fail : ∀ {α}, M α) : M Expr :=
  withLambda e fail fun fv body => do
    let body ← whnfCore body
    let body ← unfoldDefinition body
    let body ← whnfCore body
    let body ← unfoldDefinition body
    let body ← whnfCore body
    return (← getLCtx).mkLambda #[fv] body

def reduceNatWellFoundedLam2 (e : Expr)
    (fail : ∀ {α}, M α) : M Expr :=
  withLambda e fail fun fv body => do
    let body ← reduceNatWellFoundedLam1 body fail
    return (← getLCtx).mkLambda #[fv] body

@[irreducible] def checkNatBitwiseZero
    (bitwise : Expr) (fail : ∀ {α}, M α) : M Unit := do
  let (lhs, rhs) := natBitwiseZeroEquation bitwise
  let lhs ← reduceNatWellFoundedLam2 lhs fail
  unless ← isDefEq lhs rhs do fail

/-- Dynamic expressions whose translations are retained by the verified
`Nat.bitwise` certificate. -/
def natBitwiseEvidenceExpressions (bitwise equation : Expr) : List Expr :=
  let body := natBitwiseEquation bitwise
  [equation, body,
    (natBitwiseZeroEquation body).1,
    (natBitwiseZeroEquation body).2,
    (natBitwiseZeroRightEquation body).1,
    (natBitwiseZeroRightEquation body).2,
    (natBitwiseSuccEquation body bitwise).1,
    (natBitwiseSuccEquation body bitwise).2,
    (natBitwiseZeroEquation bitwise).1,
    (natBitwiseZeroEquation bitwise).2]

/-- Validate `Nat.gcd` while retaining a generic-state, independently checked
well-founded certificate. -/
def checkNatGcdPrimitive (env : Environment) (v : DefinitionVal)
    (fail : ∀ {α}, M α) : M NatGcdFixCertificate := do
  let reject {α} (message : String) : M α :=
    throw <| .other s!"invalid Nat.gcd certificate: {message}"
  unless env.contains ``Nat.mod && env.contains ``Nat.beq &&
      v.levelParams.isEmpty do fail
  unless ← isDefEq v.type q(Nat → Nat → Nat) do fail
  let some gcd' := natWellFoundedEquation v.value
    q(type_of% Nat.gcd.eq_def) | reject "malformed public equation"
  unless !gcd'.hasFVar && !gcd'.hasMVar do
    reject "public equation is not closed"
  let gcdCore ← unfoldNatWellFoundedNat2Cert v.value
    q(type_of% Nat.gcd.eq_def) (reject "generic fixpoint discovery failed")
  let cert ← checkNatGcdFixCertificate gcdCore v.value
    (reject "GCD fixpoint specialization failed")
  _ ← M.sandbox do
    unless ← isDefEq (← checkType gcd') q(Nat → Nat → Nat) do
      reject "public equation has the wrong type"
    let zero := q(Nat.zero)
    let succ := mkApp q(Nat.succ)
    let mod := mkApp2 q(Nat.mod)
    let gcd' := mkApp2 gcd'
    let gcd := mkApp2 v.value
    let x := .bvar 0
    let y := .bvar 1
    let defeq1 a b := isDefEq (.lam0 q(Nat) a) (.lam0 q(Nat) b)
    let defeq2 a b := defeq1 (.lam0 q(Nat) a) (.lam0 q(Nat) b)
    unless ← defeq1 (gcd' zero x) x do
      reject "public zero equation failed"
    unless ← defeq2
      (gcd' (succ y) x)
      (gcd (mod x (succ y)) (succ y)) do
      reject "public successor equation failed"
    let gz₁ ← reduceNatWellFoundedLam1
      (.lam0 q(Nat) <| gcd zero (.bvar 0))
      (reject "direct zero reduction failed")
    unless ← isDefEq gz₁ (.lam0 q(Nat) <| .bvar 0) do
      reject "direct zero result failed"
  return cert

/-- Validate `Nat.bitwise` and retain a generic-state, independently checked
well-founded certificate for the verification layer. -/
def checkNatBitwisePrimitive (env : Environment) (v : DefinitionVal)
    (fail : ∀ {α}, M α) : M NatBitwiseFixCertificate := do
  let reject {α} (message : String) : M α :=
    throw <| .other s!"invalid Nat.bitwise certificate: {message}"
  unless env.contains ``Nat && env.contains ``Bool &&
      env.contains ``Nat.beq && env.contains ``Nat.add &&
      env.contains ``Nat.mod && env.contains ``Nat.div &&
      v.levelParams.isEmpty do fail
  unless ← isDefEq v.type
      q((Bool → Bool → Bool) → Nat → Nat → Nat) do fail
  let some bitwise' := natWellFoundedEquation v.value
    q(type_of% Nat.bitwise.eq_def) | reject "malformed public equation"
  let evidence := natBitwiseEvidenceExpressions v.value bitwise'
  unless evidence.all fun e =>
      exprLooseBVarRange e == 0 && !e.hasFVar && !e.hasMVar do
    reject "semantic evidence is not closed"
  checkExprTypes evidence
  let bitwiseCore ← unfoldNatWellFoundedBoolNat2Cert v.value
    q(type_of% Nat.bitwise.eq_def)
    (reject "generic fixpoint discovery failed")
  let cert ← checkNatBitwiseFixCertificate bitwiseCore v.value
    (reject "bitwise fixpoint specialization failed")
  _ ← M.sandbox do
    unless ← isDefEq (← inferType bitwise')
        q((Bool → Bool → Bool) → Nat → Nat → Nat) do
      reject "public equation has the wrong type"
    Condition.natEq.checkForPrimitive
      (reject "Nat equality condition check failed")
    Condition.bool.checkForPrimitive
      (reject "Boolean condition check failed")
    let e := natBitwiseEquation v.value
    unless ← isDefEq bitwise' e do
      reject "public branch equation failed"
    let (z₁, z₂) := natBitwiseZeroEquation e
    unless ← isDefEq z₁ z₂ do reject "left-zero equation failed"
    let (zr₁, zr₂) := natBitwiseZeroRightEquation e
    unless ← isDefEq zr₁ zr₂ do reject "right-zero equation failed"
    let (s₁, s₂) := natBitwiseSuccEquation e v.value
    unless ← isDefEq s₁ s₂ do reject "successor equation failed"
    checkNatBitwiseZero v.value (reject "direct zero reduction failed")
  return cert

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

def primitiveGuard (p : Bool) (fail : M Unit) : M Unit :=
  if p then pure () else fail

def getRequiredConstant (env : Environment) (name : Name)
    (fail : M ConstantInfo) : M ConstantInfo :=
  match env.find? name with
  | some ci => pure ci
  | none => fail

/-- Validate the finite prelude boundary used by `String.ofList`. Every
referenced constant is pinned for universe arity and, on the safe path, for
safety before its checked type is compared with the canonical shape. -/
def checkStringOfListPrimitive (env : Environment)
    (v : DefinitionVal) : M Unit := do
  let fail {α} : M α :=
    throw <| .other s!"invalid form for primitive def {v.name}"
  primitiveGuard v.levelParams.isEmpty fail
  let charInfo ← getRequiredConstant env ``Char fail
  let listInfo ← getRequiredConstant env ``List fail
  let nilInfo ← getRequiredConstant env ``List.nil fail
  let consInfo ← getRequiredConstant env ``List.cons fail
  let stringInfo ← getRequiredConstant env ``String fail
  primitiveGuard charInfo.levelParams.isEmpty fail
  primitiveGuard (listInfo.levelParams.length == 1) fail
  primitiveGuard (nilInfo.levelParams.length == 1) fail
  primitiveGuard (consInfo.levelParams.length == 1) fail
  primitiveGuard stringInfo.levelParams.isEmpty fail
  primitiveGuard (v.safety != .safe ||
    (!charInfo.isUnsafe && !charInfo.isPartial)) fail
  primitiveGuard (v.safety != .safe ||
    (!listInfo.isUnsafe && !listInfo.isPartial)) fail
  primitiveGuard (v.safety != .safe ||
    (!nilInfo.isUnsafe && !nilInfo.isPartial)) fail
  primitiveGuard (v.safety != .safe ||
    (!consInfo.isUnsafe && !consInfo.isPartial)) fail
  primitiveGuard (v.safety != .safe ||
    (!stringInfo.isUnsafe && !stringInfo.isPartial)) fail
  -- Char : Type
  unless ← isDefEq (← checkType q(Char)) q(Type) do fail
  -- List.{0} : Type → Type
  unless ← isDefEq (← checkType q(List.{0})) q(Type → Type) do fail
  -- List Char : Type
  unless ← isDefEq (← checkType q(List Char)) q(Type) do fail
  -- @List.nil.{0} : (α : Type) → List α
  unless ← isDefEq (← checkType q(@List.nil.{0}))
    q((α : Type) → List α) do fail
  -- @List.nil.{0} Char : List Char
  unless ← isDefEq (← checkType q(List.nil (α := Char)))
    q(List Char) do fail
  -- @List.cons.{0} : (α : Type) → α → List α → List α
  unless ← isDefEq (← checkType q(@List.cons.{0}))
    q((α : Type) → α → List α → List α) do fail
  -- @List.cons.{0} Char : Char → List Char → List Char
  unless ← isDefEq (← checkType q(List.cons (α := Char)))
    q(Char → List Char → List Char) do fail
  -- String : Type
  unless ← isDefEq (← checkType q(String)) q(Type) do fail
  -- String.ofList : List Char → String
  unless ← isDefEq v.type q(List Char → String) do fail

def checkPrimitiveDefCore (v : DefinitionVal) : M Bool := do
  let fail {α} : M α := throw <| .other s!"invalid form for primitive def {v.name}"
  let tru := q(true)
  let fal := q(false)
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
    _ ← checkNatGcdPrimitive env v fail
  | ``Nat.beq =>
    checkNatBEqPrimitive env v fail
  | ``Nat.ble =>
    checkNatBLEPrimitive env v fail
  | ``Nat.bitwise =>
    _ ← checkNatBitwisePrimitive env v fail
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
    checkStringOfListPrimitive env v
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
