import Prosa.Analysis.Definitions.Workload.EdfAthepBound
import Validation.fixtures.translation_order.RequestBoundFunctionComputationInterface

/-!
Export root for `analysis/definitions/workload/edf_athep_bound.v`: the
production declaration, the accepted request-bound-function export root
(including its kernel-checked `sumSeq`/`sumFiltered` constructor equations),
and kernel-checked case equations for `min` on `Nat`.  Every equation is
proved in Lean and exported with its proof.
-/

namespace Prosa.Validation.EdfAthepBoundInterface

theorem production_min_of_le (a b : Nat) (h : a ≤ b) : min a b = a := Nat.min_eq_left h

theorem production_min_of_ge (a b : Nat) (h : b ≤ a) : min a b = b := Nat.min_eq_right h

end Prosa.Validation.EdfAthepBoundInterface
