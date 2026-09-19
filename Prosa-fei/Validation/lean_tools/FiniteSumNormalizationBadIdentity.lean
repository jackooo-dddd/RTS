import Validation.lean_tools.FiniteSumNormalizationGuards

open Lean Elab Command Meta

namespace Prosa.Validation.FiniteSumNormalizationNegative

def projectNatIcoSumWithBadIdentity? (e : Expr) : Option Expr := do
  guard <| e.getAppFn.isConstOf ``Finset.sum
  let args := e.getAppArgs
  guard <| args.size == 5
  guard <| args[0]!.isConstOf ``Nat
  guard <| args[1]!.isConstOf ``Nat
  let interval := args[3]!
  guard <| interval.getAppFn.isConstOf ``Finset.Ico
  let intervalArgs := interval.getAppArgs
  guard <| intervalArgs.size == 5
  guard <| intervalArgs[0]!.isConstOf ``Nat
  let lower := intervalArgs[3]!
  let upper := intervalArgs[4]!
  let function := args[4]!
  let one := mkApp (.const ``Nat.succ []) (.const ``Nat.zero [])
  let length := mkApp2 (.const ``Nat.sub []) upper lower
  let range := mkApp3 (.const ``List.range' []) lower length one
  let mapped := mkApp4 (.const ``List.map [.zero, .zero])
    (.const ``Nat []) (.const ``Nat []) function range
  -- Deliberately wrong: a sum fold must start at zero, not one.
  return mkApp5 (.const ``List.foldr [.zero, .zero])
    (.const ``Nat []) (.const ``Nat []) (.const ``Nat.add []) one mapped

partial def badProject (e : Expr) : MetaM Expr := do
  if let some projected := projectNatIcoSumWithBadIdentity? e then
    return projected
  match e with
  | .app f a => return e.updateApp! (← badProject f) (← badProject a)
  | .lam _ d b _ => return e.updateLambdaE! (← badProject d) (← badProject b)
  | .forallE _ d b _ => return e.updateForallE! (← badProject d) (← badProject b)
  | .letE _ t v b _ =>
      return e.updateLetE! (← badProject t) (← badProject v) (← badProject b)
  | .mdata _ b => return e.updateMData! (← badProject b)
  | .proj _ _ b => return e.updateProj! (← badProject b)
  | _ => return e

run_cmd liftTermElabM do
  let env ← getEnv
  let some (.thmInfo info) := env.find? ``Prosa.Util.Sum.sum_le_summation_range
    | throwError "missing target theorem"
  let bad ← Meta.reduceAll (← badProject info.type)
  unless ← Meta.isDefEq info.type bad do
    throwError "EXPECTED_REJECTION: bad fold identity is not definitionally equal"
  let guardType ← Meta.mkEq info.type bad
  let guardValue ← Meta.mkEqRefl info.type
  addDecl <| .thmDecl {
    name := "Prosa.Validation.FiniteSumNormalizationNegative.bad_guard".toName
    levelParams := []
    type := guardType
    value := guardValue
  }

end Prosa.Validation.FiniteSumNormalizationNegative
