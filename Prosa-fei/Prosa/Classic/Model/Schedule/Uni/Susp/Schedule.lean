-- Translated from: ../rt-proofs/classic/model/schedule/uni/susp/schedule.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Susp.Schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Model.Suspension

section Definitions

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (next_suspension : job_suspension Job)
variable (sched : schedule Job)

section BackloggedJob

variable (j : Job)

/-- A job is backlogged at time t iff it is pending and neither scheduled nor suspended. -/
def backlogged (t : Time) : Prop :=
  pending job_arrival job_cost sched j t ∧
  ¬ (scheduled_at sched j t = true) ∧
  ¬ suspended_at job_arrival job_cost next_suspension sched j t

end BackloggedJob

end Definitions

end Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
