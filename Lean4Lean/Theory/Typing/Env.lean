/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.NestedInductive

namespace Lean4Lean

def VDefVal.WF (env : VEnv) (ci : VDefVal) : Prop := env.HasType ci.uvars [] ci.value ci.type

/-- Add a block of constants, without their defining equations. -/
def VEnv.addConsts (env : VEnv) (cis : List VDefVal) : Option VEnv :=
  cis.foldlM (fun env ci => env.addConst ci.name ci.toVConstant) env

/-- Add the defining equations of a block, after all of its constants. -/
def VEnv.addDefEqs (env : VEnv) (cis : List VDefVal) : VEnv :=
  cis.foldl (fun env ci => env.addDefEq ci.toDefEq) env

inductive VDecl.WF : VEnv → VDecl → VEnv → Prop where
  | axiom :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.axiom ci) env'
  | def :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.def ci) (env'.addDefEq ci.toDefEq)
  | mutualDef :
    (∀ ci ∈ cis, ci.toVConstant.WF env) →
    env.addConsts cis = some env' →
    (∀ ci ∈ cis, ci.WF env') →
    VDecl.WF env (.mutualDef cis) (env'.addDefEqs cis)
  | opaque :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.opaque ci) env'
  | example :
    ci.WF env →
    VDecl.WF env (.example ci) env
  | quot :
    env.QuotReady →
    env.addQuot = some env' →
    VDecl.WF env .quot env'
  | induct {gen : decl.GenerationChecked} :
    gen.WF env →
    env.addInductGeneration gen = some env' →
    VDecl.WF env (.induct decl) env'
  | inductBlock {gen : decl.BlockGenerationChecked} :
    gen.WF env blockEnv →
    env.addInductBlockGeneration gen = some env' →
    VDecl.WF env (.induct decl) env'
  | inductNested {nested : decl.NestedBlockChecked} :
    nested.WF env →
    env.addInductNested nested = some env' →
    VDecl.WF env (.induct decl) env'

inductive VEnv.WF' : List VDecl → VEnv → Prop where
  | empty : VEnv.WF' [] .empty
  | decl {env} : VDecl.WF env d env' → env.WF' ds → env'.WF' (d::ds)
  /-- A checked structure-eta descriptor is an environment capability, not a
  source declaration.  Keep it in the environment history without inventing
  a `VDecl`; its subject-reduction certificate is exactly the premise used by
  `Ordered.structEta`. -/
  | structEta {env : VEnv} {rule : VStructEta} : rule.WF env → env.WF' ds →
      (env.addStructEta rule).WF' ds

def VEnv.WF (env : VEnv) : Prop := ∃ ds, VEnv.WF' ds env

/-- Placement of an exact constructor header relative to its completed
inductive declaration.

The usual public case has already reached the declaration output.  Internal
kernel staging may instead sit between the declaration input and output: in
that case the current environment must contain the declaration's literal
constructor constant.  This admits the family/constructor prefix used while
Lean synthesizes recursors, but still excludes definition aliases and merely
constructor-shaped types. -/
def VEnv.ConstructorHeadPlacement (env before after : VEnv)
    (constructor : VConstVal) : Prop :=
  after ≤ env ∨
    before ≤ env ∧
      env.constants constructor.name = some constructor.toVConstant

/-- A constant head classified by a genuine completed inductive declaration
or by its exact producer-owned constructor-staging prefix. -/
def VEnv.ConstructorHead (env : VEnv) (name : Name) : Prop :=
  ∃ (source : VInductDecl) (before after : VEnv)
      (constructor : VConstVal),
    before.WF ∧
      VDecl.WF before (.induct source) after ∧
      constructor ∈ source.blockConstructorConstants ∧
      constructor.name = name ∧
      env.ConstructorHeadPlacement before after constructor

/-- A completed or exactly staged inductive constructor together with the
shared parameter count of the transaction which installs it.

This is the metadata-sensitive form of `ConstructorHead`.  Keeping the count
attached to the same completed declaration avoids quantifying over unrelated
structure views: typed head inversion is the single place which must align
this retained count with a selected view. -/
def VEnv.ConstructorHeadArity (env : VEnv) (name : Name)
    (numParams : Nat) : Prop :=
  ∃ (source : VInductDecl) (before after : VEnv)
      (constructor : VConstVal),
    before.WF ∧
      VDecl.WF before (.induct source) after ∧
      source.nparams = numParams ∧
      constructor ∈ source.blockConstructorConstants ∧
      constructor.name = name ∧
      env.ConstructorHeadPlacement before after constructor

namespace VEnv.ConstructorHeadPlacement

/-- Exact constructor placement persists under Theory-environment
extension, both after completion and inside a producer-owned staging prefix. -/
theorem mono {env env' before after : VEnv} {constructor : VConstVal}
    (self : env.ConstructorHeadPlacement before after constructor)
    (henv : env ≤ env') :
    env'.ConstructorHeadPlacement before after constructor := by
  rcases self with completed | ⟨started, present⟩
  · exact .inl (completed.trans henv)
  · exact .inr ⟨started.trans henv, henv.constants present⟩

end VEnv.ConstructorHeadPlacement

namespace VEnv.ConstructorHead

/-- Constructor-head classification persists under Theory-environment
extension. -/
theorem mono {env env' : VEnv} (self : env.ConstructorHead name)
    (henv : env ≤ env') : env'.ConstructorHead name := by
  rcases self with
    ⟨source, before, after, constructor, hbefore, hdecl, hconstructor,
      hname, hplacement⟩
  exact ⟨source, before, after, constructor, hbefore, hdecl,
    hconstructor, hname, hplacement.mono henv⟩

end VEnv.ConstructorHead

namespace VEnv.ConstructorHeadArity

/-- Forget only the retained parameter count. -/
theorem toConstructorHead
    (self : _root_.Lean4Lean.VEnv.ConstructorHeadArity env name numParams) :
    _root_.Lean4Lean.VEnv.ConstructorHead env name := by
  rcases self with
    ⟨source, before, after, constructor, hbefore, hdecl, _hnparams,
      hconstructor, hname, hplacement⟩
  exact ⟨source, before, after, constructor, hbefore, hdecl,
    hconstructor, hname, hplacement⟩

/-- Constructor-head arity classification persists under Theory-environment
extension. -/
theorem mono {env env' : VEnv}
    (self : _root_.Lean4Lean.VEnv.ConstructorHeadArity env name numParams)
    (henv : env ≤ env') :
    _root_.Lean4Lean.VEnv.ConstructorHeadArity env' name numParams := by
  rcases self with
    ⟨source, before, after, constructor, hbefore, hdecl, hnparams,
      hconstructor, hname, hplacement⟩
  exact ⟨source, before, after, constructor, hbefore, hdecl, hnparams,
    hconstructor, hname, hplacement.mono henv⟩

end VEnv.ConstructorHeadArity

/- A normalized inductive history entry carries only the standard Theory
logical baseline; in particular it cannot import Verify's implementation
axioms into `VEnv.WF`. -/
/--
info: 'Lean4Lean.VDecl.WF.induct' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VDecl.WF.induct
