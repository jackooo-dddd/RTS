import Prosa.Util.Sum

open scoped BigOperators

theorem check_sum_le_projected_type :
    ∀ (f : Nat → Nat) (t Δ : Nat),
      List.foldr Nat.add 0
          (List.map f (List.range' t ((t + Δ) - t) 1)) < Δ →
      ∃ x, t ≤ x ∧ x < t + Δ ∧ f x = 0 :=
  Prosa.Util.Sum.sum_le_summation_range

open Lean Elab Command

partial def inspectFinsetSum (e : Expr) : CommandElabM Unit := do
  if e.getAppFn.constName? == some ``Finset.sum then
    logInfo m!"FINSET_SUM_ARGS {e.getAppArgs.size}"
    for h : i in [:e.getAppArgs.size] do
      logInfo m!"ARG {i}: {repr e.getAppArgs[i]}"
  match e with
  | .app f a => inspectFinsetSum f; inspectFinsetSum a
  | .lam _ d b _ | .forallE _ d b _ => inspectFinsetSum d; inspectFinsetSum b
  | .letE _ t v b _ => inspectFinsetSum t; inspectFinsetSum v; inspectFinsetSum b
  | .mdata _ b | .proj _ _ b => inspectFinsetSum b
  | _ => pure ()

run_cmd do
  let env ← getEnv
  let some (.thmInfo info) := env.find? `Prosa.Util.Sum.sum_le_summation_range
    | throwError "missing theorem"
  inspectFinsetSum info.type
