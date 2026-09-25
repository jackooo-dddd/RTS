import Prosa.Model.Schedule.Scheduled
import Validation.fixtures.translation_order.BigcatComputationInterface
import Validation.fixtures.translation_order.ScheduleComputationInterface

namespace Prosa.Validation.ScheduledInterface

universe u

/-- Actual compiled `List.head?` constructor equations used by the
source `ohead` correspondence. -/
theorem production_head_nil {T : Type u} :
    ([] : List T).head? = none := rfl

theorem production_head_cons {T : Type u} (x : T) (xs : List T) :
    (x :: xs).head? = some x := rfl

/-- Actual compiled `List.isEmpty` constructor equations used by the
source Boolean empty-list equality correspondence. -/
theorem production_isEmpty_nil {T : Type u} :
    ([] : List T).isEmpty = true := rfl

theorem production_isEmpty_cons {T : Type u} (x : T) (xs : List T) :
    (x :: xs).isEmpty = false := rfl

end Prosa.Validation.ScheduledInterface
