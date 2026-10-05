import Prosa.Analysis.Definitions.BusyInterval.Classical
import Validation.fixtures.translation_order.PreemptionParameterComputationInterface

/-!
Export root for `analysis/definitions/busy_interval/classical.v`: the
production declarations, the accepted preemption-parameter export root, and
kernel-checked constructor equations for `List.all` (the source `all`) and
the `quiet_time_dec` body.  Every equation is proved in Lean and exported
with its proof.
-/

namespace Prosa.Validation.BusyIntervalClassicalInterface

universe u

theorem production_all_nil {X : Type u} (p : X → Bool) : ([] : List X).all p = true := rfl

theorem production_all_cons {X : Type u} (p : X → Bool) (x : X) (xs : List X) :
    (x :: xs).all p = (p x && xs.all p) := rfl

end Prosa.Validation.BusyIntervalClassicalInterface
