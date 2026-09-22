import Prosa.Behavior.Arrival_sequence
import Validation.fixtures.translation_order.BigcatComputationInterface

/-!
This validation-only module deliberately adds no model declaration.  It puts
the actual compiled Arrival Sequence definitions and the already kernel-checked
List/`bigCat` computation equations in one export environment so that the Rocq
certificate can reason about the production bodies without unfolding the
entire Mathlib implementation.
-/

