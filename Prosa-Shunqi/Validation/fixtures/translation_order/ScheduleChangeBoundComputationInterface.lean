import Prosa.Analysis.Facts.Model.Overheads.ScheduleChangeBound
import Validation.fixtures.translation_order.PriorityBumpFactsComputationInterface
import Validation.fixtures.translation_order.ScheduleChangeComputationInterface
import Validation.fixtures.translation_order.FactsArrivalCurvesComputationInterface

/-!
Export root for `analysis/facts/model/overheads/schedule_change_bound.v`: the three statements together with
the accepted overheads priority-bump facts export root (with its validation-only universe witnesses), the accepted
schedule-change definitions root and the accepted arrival-curve facts root, plus Lean's function extensionality
exported with its proof (for the certificate's cover of task types quantified inside a statement).
-/

namespace Prosa.Validation.ScheduleChangeBoundInterface

universe u v

/-- Function extensionality, exported with its proof (Lean's `funext`, proved from `Quot.sound`);
used by the certificate's cover of task types quantified inside a statement. -/
theorem production_funext {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : ∀ x, f x = g x) : f = g :=
  funext h

end Prosa.Validation.ScheduleChangeBoundInterface
