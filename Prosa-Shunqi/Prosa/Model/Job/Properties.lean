-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/job/properties.v

import Prosa.Behavior.All

namespace Prosa.Model.Job.Properties

open Prosa.Behavior.Job
open Prosa.Behavior.Arrival_sequence

universe u

variable {Job : JobType} [DecidableEq Job] [JobCost Job]

/-- The cost of a job is strictly positive. -/
def job_cost_positive (j : Job) : Bool :=
  decide (job_cost j > 0)

/-- Every job in an arrival sequence has strictly positive cost. -/
def arrivals_have_positive_job_costs (arr_seq : arrival_sequence Job) : Prop :=
  ∀ j, arrives_in arr_seq j → job_cost_positive j = true

end Prosa.Model.Job.Properties
