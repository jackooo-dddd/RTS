import Prosa.Analysis.Definitions.Sbf.Pred
import Validation.fixtures.translation_order.SupplyComputationInterface
import Validation.fixtures.translation_order.ArrivalSequenceComputationInterface

-- Source-compatible lower-level supply projection remains proof-bodied;
-- the four new definitions are exported from this compiled target body.
-- The theorem is exported at its exact compiled type without its proof body.
-- The accepted ArrivalSequence computation interface permits the same
-- artifact to replay its already certified arrives_in correspondence.
