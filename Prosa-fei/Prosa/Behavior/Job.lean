-- Translated from: ../rt-proofs/behavior/job.v
import Prosa.Behavior.Time

namespace Prosa.Behavior.Job

open Prosa.Behavior.Time

/-- A job type is any type with decidable equality. -/
abbrev JobType := Type

/-- Unit of work: the unit of service received or needed. -/
abbrev work := Nat

/-- Generic parameter relating jobs to a discrete cost. -/
class JobCost (Job : JobType) where
  job_cost : Job → work

export JobCost (job_cost)

/-- Generic parameter for job arrival time. -/
class JobArrival (Job : JobType) where
  job_arrival : Job → instant

export JobArrival (job_arrival)

/-- Generic parameter relating jobs to an absolute deadline. -/
class JobDeadline (Job : JobType) where
  job_deadline : Job → instant

export JobDeadline (job_deadline)

end Prosa.Behavior.Job
