import Prosa.Analysis.Facts.Priority.Fifo
import Validation.fixtures.translation_order.BusyIntervalServiceInversionComputationInterface

/-!
Export root for `analysis/facts/priority/fifo.v`: the twelve statements together with the accepted
busy-interval service-inversion export root and the accepted FIFO export root, plus Lean's function
extensionality exported with its proof (for the certificate's cover of task types quantified inside a
statement).
-/

namespace Prosa.Validation.FactsPriorityFifoInterface

universe u v

/-- Function extensionality, exported with its proof (Lean's `funext`, proved from `Quot.sound`);
used by the certificate's cover of task types quantified inside a statement. -/
theorem production_funext {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : ∀ x, f x = g x) : f = g :=
  funext h

end Prosa.Validation.FactsPriorityFifoInterface
