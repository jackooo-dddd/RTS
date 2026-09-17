-- Translated from: ../rt-proofs/classic/model/schedule/uni/jitter/platform.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

namespace Prosa.Classic.Model.Schedule.Uni.Jitter.Platform

set_option linter.dupNamespace false

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Priority

namespace Platform

section Properties

  variable {sporadic_task : Type _} [DecidableEq sporadic_task]
  variable (task_cost : sporadic_task → Time)
  variable (task_period : sporadic_task → Time)
  variable (task_deadline : sporadic_task → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_deadline : Job → Time)
  variable (job_jitter : Job → Time)
  variable (job_task : Job → sporadic_task)

  variable (arr_seq : arrival_sequence Job)
  variable (sched : schedule Job)

  section Execution

    def work_conserving :=
      ∀ j t,
        arrives_in arr_seq j →
        Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged job_arrival job_cost job_jitter sched j t →
        ∃ j_other, scheduled_at sched j_other t = true

  end Execution

  section FP

    variable (higher_eq_priority : FP_policy sporadic_task)

    def respects_FP_policy :=
      ∀ j j_hp t,
        arrives_in arr_seq j →
        Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged job_arrival job_cost job_jitter sched j t →
        scheduled_at sched j_hp t = true →
        higher_eq_priority (job_task j_hp) (job_task j) = true

  end FP

  section JLFP

    variable (higher_eq_priority : JLFP_policy Job)

    def respects_JLFP_policy :=
      ∀ j j_hp t,
        arrives_in arr_seq j →
        Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged job_arrival job_cost job_jitter sched j t →
        scheduled_at sched j_hp t = true →
        higher_eq_priority j_hp j = true

  end JLFP

  section JLDP

    variable (higher_eq_priority : JLDP_policy Job)

    def respects_JLDP_policy :=
      ∀ j j_hp t,
        arrives_in arr_seq j →
        Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged job_arrival job_cost job_jitter sched j t →
        scheduled_at sched j_hp t = true →
        higher_eq_priority t j_hp j = true

  end JLDP

end Properties

end Platform

end Prosa.Classic.Model.Schedule.Uni.Jitter.Platform
