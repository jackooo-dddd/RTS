import Prosa.Analysis.Definitions.BusyInterval.EdfPiBound
import Validation.fixtures.translation_order.TaskPreemptionParametersComputationInterface
import Validation.fixtures.translation_order.RequestBoundFunctionComputationInterface

/-!
Export root for `analysis/definitions/busy_interval/edf_pi_bound.v`: the
production declaration, the accepted task-preemption-parameters and
request-bound-function export roots, and kernel-checked constructor equations
for the conditional maximum `bigMaxListCond` (as in the accepted EDF
blocking-bound root).  Every equation is proved in Lean and exported with its
proof.
-/

namespace Prosa.Validation.EdfPiBoundInterface

open Prosa.Util.Minmax

universe u

theorem production_bigMaxListCond_nil {X : Type u} (P : X → Bool) (F : X → Nat) :
    bigMaxListCond [] P F = 0 := rfl

theorem production_bigMaxListCond_cons_true {X : Type u} (P : X → Bool) (F : X → Nat)
    (x : X) (xs : List X) (h : P x = true) :
    bigMaxListCond (x :: xs) P F = Nat.max (F x) (bigMaxListCond xs P F) := by
  simp [bigMaxListCond, h]

theorem production_bigMaxListCond_cons_false {X : Type u} (P : X → Bool) (F : X → Nat)
    (x : X) (xs : List X) (h : P x = false) :
    bigMaxListCond (x :: xs) P F = bigMaxListCond xs P F := by
  simp [bigMaxListCond, h]

end Prosa.Validation.EdfPiBoundInterface
