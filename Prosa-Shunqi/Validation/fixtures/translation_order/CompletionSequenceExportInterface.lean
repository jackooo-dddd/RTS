import Prosa.Analysis.Definitions.CompletionSequence
import Validation.fixtures.translation_order.ServiceComputationInterface
import Validation.fixtures.translation_order.ArrivalSequenceComputationInterface

/-!
The root binds the exact compiled production `completion_sequence` constant
to the previously kernel-guarded Service computation projections and the
previously checked ArrivalSequence/Bigcat computation equations. No
production definition or theorem is changed by this validation-only module.
-/
