import Prosa.Classic.Model.Suspension

/-!
Validation-only interface for `classic/model/suspension.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicSuspensionInterface

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Suspension.Suspension

universe u

def total_suspension_proj {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    (next_suspension : job_suspension Job) (j : Job) : Nat :=
  List.foldr Nat.add Nat.zero
    (List.map (fun t => next_suspension j t) (List.range' 0 (Nat.sub (job_cost j) 0) (Nat.succ Nat.zero)))

theorem total_suspension_proj_guard : @total_suspension = @total_suspension_proj := rfl

end Prosa.Validation.ClassicSuspensionInterface
