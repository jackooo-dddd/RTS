import Prosa.Analysis.Facts.Model.ServiceOfJobs
import Validation.fixtures.translation_order.BusyIntervalClassicalComputationInterface
import Validation.fixtures.translation_order.WorkloadComputationInterface
import Validation.fixtures.translation_order.ServiceOfJobsComputationInterface

/-!
Export root for `analysis/facts/model/service_of_jobs.v`: the 22 statements
together with the accepted busy-interval export root (preemption-parameter /
Service closure), the accepted workload export root and the accepted
service-of-jobs export root, kernel-checked constructor equations for
`List.any`, and kernel normalization guards for the two statements whose
types contain a half-open `Finset.Ico` sum (projected during export to the
same `List.foldr` form as the accepted interval sums, only after the `rfl`
guard below is checked).
-/

open Lean Elab Command Meta

namespace Prosa.Validation.FactsServiceOfJobsInterface

universe u

theorem production_any_nil {X : Type u} (p : X → Bool) : ([] : List X).any p = false := rfl

theorem production_any_cons {X : Type u} (p : X → Bool) (x : X) (xs : List X) :
    (x :: xs).any p = (p x || xs.any p) := rfl

private def projectNatIcoSum? (e : Expr) : Option Expr := do
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
  addNormalizationGuard
    ``Prosa.Analysis.Facts.Model.ServiceOfJobs.service_of_jobs_sum_over_time_interval
    "Prosa.Validation.FactsServiceOfJobsInterface.service_of_jobs_sum_over_time_interval_guard".toName
  addNormalizationGuard
    ``Prosa.Analysis.Facts.Model.ServiceOfJobs.cumulative_pred_served_eq_service
    "Prosa.Validation.FactsServiceOfJobsInterface.cumulative_pred_served_eq_service_guard".toName

#check service_of_jobs_sum_over_time_interval_guard
#check cumulative_pred_served_eq_service_guard
#print axioms service_of_jobs_sum_over_time_interval_guard
#print axioms cumulative_pred_served_eq_service_guard

end Prosa.Validation.FactsServiceOfJobsInterface
