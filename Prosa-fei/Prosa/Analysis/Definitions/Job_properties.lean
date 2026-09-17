-- Translated from: ../rt-proofs/analysis/definitions/job_properties.v
import Prosa.Behavior.All

namespace Prosa.Analysis.Definitions.Job_properties

open Prosa.Behavior.Time Prosa.Behavior.Job

section PropertiesOfJob

variable {Job : JobType}
variable [JobCost Job]
variable (j : Job)

/-- The job cost must be positive. -/
def job_cost_positive : Prop := job_cost j > 0

end PropertiesOfJob

end Prosa.Analysis.Definitions.Job_properties
