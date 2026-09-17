-- Translated from: ../rt-proofs/classic/model/schedule/uni/susp/valid_schedule.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform

namespace Prosa.Classic.Model.Schedule.Uni.Susp.Valid_schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Suspension

section DefiningValidSchedule

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_task : Job → Task)
variable (arr_seq : arrival_sequence Job)
variable (higher_eq_priority : JLDP_policy Job)
variable (job_suspension_duration : job_suspension Job)
variable (job_cost : Job → Time)
variable (sched_susp : schedule Job)

def valid_suspension_aware_schedule :=
  jobs_come_from_arrival_sequence sched_susp arr_seq ∧
  jobs_must_arrive_to_execute job_arrival sched_susp ∧
  completed_jobs_dont_execute job_cost sched_susp ∧
  work_conserving job_arrival job_cost job_suspension_duration arr_seq sched_susp ∧
  respects_JLDP_policy job_arrival job_cost job_suspension_duration arr_seq sched_susp higher_eq_priority ∧
  respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp

end DefiningValidSchedule

end Prosa.Classic.Model.Schedule.Uni.Susp.Valid_schedule
