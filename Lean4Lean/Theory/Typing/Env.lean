import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive

namespace Lean4Lean

def VDefVal.WF (env : VEnv) (ci : VDefVal) : Prop := env.HasType ci.uvars [] ci.value ci.type

inductive VDecl.WF : VEnv → VDecl → VEnv → Prop where
  | axiom :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.axiom ci) env'
  | def :
    ci.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    VDecl.WF env (.def ci) (env'.addDefEq ci.toDefEq)
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

inductive VEnv.WF' : List VDecl → VEnv → Prop where
  | empty : VEnv.WF' [] .empty
  | decl {env} : VDecl.WF env d env' → env.WF' ds → env'.WF' (d::ds)

def VEnv.WF (env : VEnv) : Prop := ∃ ds, VEnv.WF' ds env

/- A normalized inductive history entry carries only the standard Theory
logical baseline; in particular it cannot import Verify's implementation
axioms into `VEnv.WF`. -/
/--
info: 'Lean4Lean.VDecl.WF.induct' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VDecl.WF.induct
