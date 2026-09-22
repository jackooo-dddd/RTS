-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: behavior/job.v

import Prosa.Util.All
import Prosa.Behavior.Time

namespace Prosa.Behavior.Job

open Prosa.Behavior.Time

universe u

/-!
The source `JobType := eqType` bundles a carrier with decidable Boolean
equality.  The approved Lean representation exposes the carrier as a type and
carries its `DecidableEq` evidence at every declaration boundary where a
source `JobType` is in scope.
-/

/-- Carrier of a source MathComp `eqType`; equality evidence is explicit at
each consuming boundary. -/
abbrev JobType := Type u

/-- Unit of processor work or service. -/
abbrev work := Nat

/-- A job's execution cost. -/
class JobCost (Job : JobType) [DecidableEq Job] where
  job_cost : Job → work

export JobCost (job_cost)

/-- A job's arrival instant. -/
class JobArrival (Job : JobType) [DecidableEq Job] where
  job_arrival : Job → instant

export JobArrival (job_arrival)

/-- A job's absolute deadline. -/
class JobDeadline (Job : JobType) [DecidableEq Job] where
  job_deadline : Job → instant

export JobDeadline (job_deadline)

end Prosa.Behavior.Job
