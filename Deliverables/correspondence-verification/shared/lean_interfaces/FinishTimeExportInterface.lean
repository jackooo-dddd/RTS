import Prosa.Analysis.Definitions.FinishTime
import Validation.fixtures.translation_order.ServiceComputationInterface

-- The exporter reads the compiled environment of this wrapper.  The
-- production target declarations remain in Prosa.Analysis.Definitions.FinishTime.
#check @Prosa.Analysis.Definitions.FinishTime.finish_time
#check @Prosa.Analysis.Definitions.FinishTime.response_time
#check @Nat.find_spec
#check @Nat.find_min'
