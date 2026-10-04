import Prosa.Classic.Util.Sum

/-!
Export root for `classic/util/sum.v` (classic family), with kernel normalization guards for the
six statements whose types contain a half-open `Finset.Ico` sum over `Nat`, plain or filtered
(`(Finset.Ico m n).filter p`).  During export those sums are projected (exporter
`projectNatIcoSum?`, `normalization.subexpression_heads = ["Finset.sum"]`) to
`List.foldr Nat.add 0 (List.map f r)` with `r = List.range' m (n - m) 1`, filtered by
`decide (p i)` with the same instance when the sum is filtered; the projection below is the same
function, and each guard `original = projected` is checked by the Lean kernel as `Eq.refl`
before the export uses it (as for the accepted v0.6 `FactsServiceOfJobsComputationInterface`).
-/

open Lean Elab Command Meta

namespace Prosa.Validation.ClassicSumInterface

private def projectNatIcoSum? (e : Expr) : Option Expr := do
  guard <| e.getAppFn.isConstOf ``Finset.sum
  let args := e.getAppArgs
  guard <| args.size == 5
  guard <| args[0]!.isConstOf ``Nat
  guard <| args[1]!.isConstOf ``Nat
  let (interval, filt?) :=
    if args[3]!.getAppFn.isConstOf ``Finset.filter && args[3]!.getAppArgs.size == 4 then
      (args[3]!.getAppArgs[3]!, some (args[3]!.getAppArgs[1]!, args[3]!.getAppArgs[2]!))
    else (args[3]!, none)
  guard <| interval.getAppFn.isConstOf ``Finset.Ico
  let intervalArgs := interval.getAppArgs
  guard <| intervalArgs.size == 5
  guard <| intervalArgs[0]!.isConstOf ``Nat
  let lower := intervalArgs[3]!
  let upper := intervalArgs[4]!
  let function := args[4]!
  let one := mkApp (.const ``Nat.succ []) (.const ``Nat.zero [])
  let length := mkApp2 (.const ``Nat.sub []) upper lower
  let range0 := mkApp3 (.const ``List.range' []) lower length one
  let range := match filt? with
    | none => range0
    | some (p, dec) =>
        let decideFn := Expr.lam `i (.const ``Nat [])
          (mkApp2 (.const ``Decidable.decide []) (.app (p.liftLooseBVars 0 1) (.bvar 0))
            (.app (dec.liftLooseBVars 0 1) (.bvar 0))) .default
        mkApp3 (.const ``List.filter [.zero]) (.const ``Nat []) decideFn range0
  let mapped := mkApp4 (.const ``List.map [.zero, .zero])
    (.const ``Nat []) (.const ``Nat []) function range
  return mkApp5 (.const ``List.foldr [.zero, .zero])
    (.const ``Nat []) (.const ``Nat []) (.const ``Nat.add [])
    (.const ``Nat.zero []) mapped

private partial def projectSums (e : Expr) : MetaM Expr := do
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

private def addNormalizationGuard (target guard : Name) : MetaM Unit := do
  let env ← getEnv
  let some (.thmInfo info) := env.find? target
    | throwError "normalization target is not a theorem: {target}"
  let normalized ← projectSums info.type
  unless ← Meta.isDefEq info.type normalized do
    logInfo m!"NORMALIZATION_MISMATCH target={target} original={info.type} normalized={normalized}"
    throwError "normalization is not definitionally equal: {target}"
  let guardType ← Meta.mkEq info.type normalized
  let guardValue ← Meta.mkEqRefl info.type
  addDecl <| .thmDecl {
    name := guard
    levelParams := info.levelParams
    type := guardType
    value := guardValue
  }
  logInfo m!"KERNEL_NORMALIZATION_GUARD target={target} guard={guard} original_hash={hash info.type} normalized_hash={hash normalized} proof=Eq.refl"

run_cmd liftTermElabM do
  addNormalizationGuard ``Prosa.Classic.Util.Sum.sum_diff
    "Prosa.Validation.ClassicSumInterface.sum_diff_guard".toName
  addNormalizationGuard ``Prosa.Classic.Util.Sum.extend_sum
    "Prosa.Validation.ClassicSumInterface.extend_sum_guard".toName
  addNormalizationGuard ``Prosa.Classic.Util.Sum.leq_sum_nat
    "Prosa.Validation.ClassicSumInterface.leq_sum_nat_guard".toName
  addNormalizationGuard ``Prosa.Classic.Util.Sum.leq_sum1_smaller_range
    "Prosa.Validation.ClassicSumInterface.leq_sum1_smaller_range_guard".toName
  addNormalizationGuard ``Prosa.Classic.Util.Sum.sum_le_summation_range
    "Prosa.Validation.ClassicSumInterface.sum_le_summation_range_guard".toName
  addNormalizationGuard ``Prosa.Classic.Util.Sum.telescoping_sum
    "Prosa.Validation.ClassicSumInterface.telescoping_sum_guard".toName

#print axioms sum_diff_guard
#print axioms extend_sum_guard
#print axioms leq_sum_nat_guard
#print axioms leq_sum1_smaller_range_guard
#print axioms sum_le_summation_range_guard
#print axioms telescoping_sum_guard

end Prosa.Validation.ClassicSumInterface
