/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean.Expr
import Lean.LocalContext
import Lean.Util.InstantiateLevelParams
import Lean.Declaration

namespace Lean
namespace Expr

/-- Beta-reduces an application `(fun x₁ ... xₙ => b) a₁ ... aₙ aₙ₊₁ ... aₘ` in the two cases where
no substitution is needed: to `b aₙ₊₁ ... aₘ` when `b` has no loose bound variables, and to
`aᵢ aₙ₊₁ ... aₘ` when `b` is the bound variable `xᵢ`. In any other case `e` is returned unchanged —
this is what makes it cheap. -/
def cheapBetaReduce (e : Expr) : Expr := Id.run do
  if !e.isApp then return e
  let fn := e.getAppFn
  if !fn.isLambda then return e
  let args := e.getAppArgs
  let rec cont i fn :=
    if !fn.hasLooseBVars then
      -- Do not let a possibly corrupt packed loose-bvar cache suppress a
      -- substitution. On cache-correct terms this range instantiation is the
      -- identity and retains the runtime fast path.
      mkAppRange (fn.instantiateRevRange 0 i args) i args.size args
    else if let .bvar n := fn then
      assert! n < i
      mkAppRange args[i - n - 1]! i args.size args
    else
      e
  let rec loop i fn :=
    if i < args.size then
      match fn with
      | .lam _ _ body .. => loop (i + 1) body
      | _ => cont i fn
    else cont i fn
  return loop 0 fn

end Expr

/-!
## Kernel-compatible universe substitution

Lean's public `mkLevelMax'` and `mkLevelIMax'` helpers do not currently use
the same cheap normalizations as the C++ kernel. Because universe
substitution feeds expression hashes and the type checker's unfold cache, the
kernel-facing paths below use explicit copies of the C++ rules. These wrappers
can disappear when Lean's public helpers and kernel constructors coincide.
-/

/-- `Lean.mkLevelMaxCore` without its extra explicit-level subsumption rule,
matching the C++ kernel's `mk_max`. -/
@[inline] def mkLevelMaxCoreCpp (u v : Level) (elseK : Unit → Level) : Level :=
  let subsumes : Level → Level → Bool := fun u v =>
    match u with
    | .max u₁ u₂ => v == u₁ || v == u₂
    | _ => false
  if u == v then u
  else if u.isZero then v
  else if v.isZero then u
  else if subsumes u v then u
  else if subsumes v u then v
  else if u.getLevelOffset == v.getLevelOffset then
    if u.getOffset ≥ v.getOffset then u else v
  else
    elseK ()

/-- Cheap level maximum using the C++ kernel's normalization rules. -/
def mkLevelMaxCpp (u v : Level) : Level :=
  mkLevelMaxCoreCpp u v fun _ => mkLevelMax u v

/-- `Lean.mkLevelIMaxCore` with the C++ kernel's `imax 1 u = u` rule. -/
@[inline] def mkLevelIMaxCoreCpp (u v : Level) (elseK : Unit → Level) : Level :=
  if v.isNeverZero then mkLevelMaxCpp u v
  else if v.isZero then v
  else if u.isZero || u == .succ .zero then v
  else if u == v then u
  else elseK ()

/-- Cheap impredicative maximum using the C++ kernel's normalization rules. -/
def mkLevelIMaxCpp (u v : Level) : Level :=
  mkLevelIMaxCoreCpp u v fun _ => mkLevelIMax u v

/-- `Level.substParams` using the C++ kernel's level constructors. -/
@[specialize] def Level.substParamsCpp (u : Level) (s : Name → Option Level) : Level :=
  go u
where
  go (u : Level) : Level :=
    match u with
    | .zero => u
    | .succ v => if u.hasParam then .succ (go v) else u
    | .max v₁ v₂ => if u.hasParam then mkLevelMaxCpp (go v₁) (go v₂) else u
    | .imax v₁ v₂ => if u.hasParam then mkLevelIMaxCpp (go v₁) (go v₂) else u
    | .param n => (s n).getD u
    | u => u

/-- `Expr.instantiateLevelParamsCore` using `Level.substParamsCpp`. -/
@[specialize] def Expr.instantiateLevelParamsCoreCpp
    (s : Name → Option Level) (e : Expr) : Expr :=
  e.replace replaceFn
where
  @[specialize] replaceFn (e : Expr) : Option Expr :=
    if !e.hasLevelParam then e
    else match e with
    | .const _ us => e.updateConst! (us.map fun u => u.substParamsCpp s)
    | .sort u => e.updateSort! (u.substParamsCpp s)
    | _ => none

/-- `Expr.instantiateLevelParams` using the C++ kernel's level constructors. -/
def Expr.instantiateLevelParamsCpp
    (e : Expr) (paramNames : List Name) (levels : List Level) : Expr :=
  if paramNames.isEmpty || levels.isEmpty then e
  else
    let rec go : List Name → List Level → Name → Option Level
      | p :: ps, u :: us, p' => if p == p' then some u else go ps us p'
      | _, _, _ => none
    e.instantiateLevelParamsCoreCpp (go paramNames levels)

/-- Instantiate a declaration type with the C++ kernel's level constructors. -/
def ConstantInfo.instantiateTypeLevelParamsCpp
    (info : ConstantInfo) (levels : List Level) : Expr :=
  info.type.instantiateLevelParamsCpp info.levelParams levels

/-- Instantiate a declaration value with the C++ kernel's level constructors. -/
def ConstantInfo.instantiateValueLevelParams!Cpp
    (info : ConstantInfo) (levels : List Level) : Expr :=
  info.value?.get!.instantiateLevelParamsCpp info.levelParams levels
