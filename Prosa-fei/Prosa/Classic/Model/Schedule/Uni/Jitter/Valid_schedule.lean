-- Translated from: ../rt-proofs/classic/model/schedule/uni/jitter/valid_schedule.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Platform

namespace Prosa.Classic.Model.Schedule.Uni.Jitter.Valid_schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
open Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Priority

namespace ValidJitterAwareSchedule

section DefiningValidSchedule

  variable {Task : Type _} [DecidableEq Task]
  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_task : Job → Task)

  variable (arr_seq : arrival_sequence Job)

  variable (higher_eq_priority : JLDP_policy Job)

  variable (job_cost : Job → Time)
  variable (job_jitter : Job → Time)

  variable (sched : schedule Job)

  def valid_jitter_aware_schedule : Prop :=
    jobs_come_from_arrival_sequence sched arr_seq ∧
    jobs_execute_after_jitter job_arrival job_jitter sched ∧
    completed_jobs_dont_execute job_cost sched ∧
    work_conserving job_arrival job_cost job_jitter arr_seq sched ∧
    respects_JLDP_policy job_arrival job_cost job_jitter arr_seq sched higher_eq_priority

end DefiningValidSchedule

end ValidJitterAwareSchedule

end Prosa.Classic.Model.Schedule.Uni.Jitter.Valid_schedule
