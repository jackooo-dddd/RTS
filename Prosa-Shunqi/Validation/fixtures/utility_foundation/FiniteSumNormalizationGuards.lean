import Prosa.Util.Sum

open Lean Elab Command Meta

namespace Prosa.Validation.FiniteSumNormalization

def projectNatIcoSum? (e : Expr) : Option Expr := do
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
  return mkApp5 (.const ``List.foldr [.zero, .zero])
    (.const ``Nat []) (.const ``Nat []) (.const ``Nat.add [])
    (.const ``Nat.zero []) mapped

partial def projectSums (e : Expr) : MetaM Expr := do
  if let some projected := projectNatIcoSum? e then
    return projected
  match e with
  | .app f a => return e.updateApp! (← projectSums f) (← projectSums a)
  | .lam _ d b _ => return e.updateLambdaE! (← projectSums d) (← projectSums b)
  | .forallE _ d b _ => return e.updateForallE! (← projectSums d) (← projectSums b)
  | .letE _ t v b _ =>
      return e.updateLetE! (← projectSums t) (← projectSums v)
        (← projectSums b)
  | .mdata _ b => return e.updateMData! (← projectSums b)
  | .proj _ _ b => return e.updateProj! (← projectSums b)
  | _ => return e

def normalizedTargetType (target : Name) : MetaM Expr := do
  let env ← getEnv
  let some (.thmInfo info) := env.find? target
    | throwError "normalization target is not a theorem: {target}"
  projectSums info.type

def addNormalizationGuard (target guard : Name) : MetaM Unit := do
  let env ← getEnv
  let some (.thmInfo info) := env.find? target
    | throwError "normalization target is not a theorem: {target}"
  let normalized ← normalizedTargetType target
  unless ← Meta.isDefEq info.type normalized do
    logInfo m!"NORMALIZATION_MISMATCH target={target} original={info.type} normalized={normalized}"
    throwError "normalization is not definitionally equal: {target}"
  let guardType ← Meta.mkEq info.type normalized
  let guardValue ← Meta.mkEqRefl info.type
  addDecl <| .thmDecl {
    name := guard
    levelParams := []
    type := guardType
    value := guardValue
  }
  logInfo m!"KERNEL_NORMALIZATION_GUARD target={target} guard={guard} original_hash={hash info.type} normalized_hash={hash normalized} proof=Eq.refl"

run_cmd liftTermElabM do
  addNormalizationGuard ``Prosa.Util.Sum.big_nat_eq0
    "Prosa.Validation.FiniteSumNormalization.big_nat_eq0_guard".toName
  addNormalizationGuard ``Prosa.Util.Sum.sum_of_ones
    "Prosa.Validation.FiniteSumNormalization.sum_of_ones_guard".toName
  addNormalizationGuard ``Prosa.Util.Sum.sum_le_summation_range
    "Prosa.Validation.FiniteSumNormalization.sum_le_summation_range_guard".toName
  addNormalizationGuard ``Prosa.Util.Sum.big_sum_eq_in_eq_sized_intervals
    "Prosa.Validation.FiniteSumNormalization.big_sum_eq_in_eq_sized_intervals_guard".toName
  addNormalizationGuard ``Prosa.Util.Sum.pigeonhole_on_interval
    "Prosa.Validation.FiniteSumNormalization.pigeonhole_on_interval_guard".toName
  addNormalizationGuard ``Prosa.Util.Sum.sum_ge_2_nat
    "Prosa.Validation.FiniteSumNormalization.sum_ge_2_nat_guard".toName

#check big_nat_eq0_guard
#check sum_of_ones_guard
#check sum_le_summation_range_guard
#check big_sum_eq_in_eq_sized_intervals_guard
#check pigeonhole_on_interval_guard
#check sum_ge_2_nat_guard
#print axioms big_nat_eq0_guard
#print axioms sum_of_ones_guard
#print axioms sum_le_summation_range_guard
#print axioms big_sum_eq_in_eq_sized_intervals_guard
#print axioms pigeonhole_on_interval_guard
#print axioms sum_ge_2_nat_guard

end Prosa.Validation.FiniteSumNormalization
