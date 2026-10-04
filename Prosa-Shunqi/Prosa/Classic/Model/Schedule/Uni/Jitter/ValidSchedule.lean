-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/jitter/valid_schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 82)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Platform

/-!
Valid jitter-aware uniprocessor schedules (Rocq module `ValidJitterAwareSchedule`).

Representation notes: the section-local `Let`s `H1_jobs_come_from_arrival_sequence` … `H5_respects_priority` are
unfolded into the conjunction. Binder lists follow the Rocq contract (`{Job} job_arrival arr_seq
higher_eq_priority job_cost job_jitter sched`; neither `Task` nor `job_task` is taken).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Jitter.ValidSchedule.ValidJitterAwareSchedule

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
  (schedule jobs_come_from_arrival_sequence completed_jobs_dont_execute)
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter (jobs_execute_after_jitter)
open Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform (work_conserving respects_JLDP_policy)

universe v

def valid_jitter_aware_schedule {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (job_cost job_jitter : Job → time)
    (sched : schedule Job) : Prop :=
  jobs_come_from_arrival_sequence sched arr_seq ∧
  jobs_execute_after_jitter job_arrival job_jitter sched ∧
  completed_jobs_dont_execute job_cost sched ∧
  work_conserving job_arrival job_cost job_jitter arr_seq sched ∧
  respects_JLDP_policy job_arrival job_cost job_jitter arr_seq sched higher_eq_priority

end Prosa.Classic.Model.Schedule.Uni.Jitter.ValidSchedule.ValidJitterAwareSchedule
