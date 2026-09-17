-- Translated from: ../rt-proofs/classic/model/schedule/apa/platform.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Interference
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Model.Priority

namespace Prosa.Classic.Model.Schedule.Apa.Platform

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Schedule ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Apa.Affinity
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

section Properties

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)

variable (arr_seq : arrival_sequence Job)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

variable (alpha : task_affinity sporadic_task num_cpus)

section Execution

def apa_work_conserving : Prop :=
  ∀ j t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t →
    ∀ cpu,
      can_execute_on alpha (job_task j) cpu →
      ∃ j_other,
        scheduled_on sched j_other cpu t = true

def respects_affinity : Prop :=
  ∀ j cpu t,
    scheduled_on sched j cpu t = true →
    can_execute_on alpha (job_task j) cpu

end Execution

section FP

variable (higher_eq_priority : FP_policy sporadic_task)

def respects_FP_policy_under_weak_APA : Prop :=
  ∀ j j_hp cpu t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t →
    scheduled_on sched j_hp cpu t = true →
    can_execute_on alpha (job_task j) cpu →
    higher_eq_priority (job_task j_hp) (job_task j) = true

end FP

section JLFP

variable (higher_eq_priority : JLFP_policy Job)

def respects_JLFP_policy_under_weak_APA : Prop :=
  ∀ j j_hp cpu t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t →
    scheduled_on sched j_hp cpu t = true →
    can_execute_on alpha (job_task j) cpu →
    higher_eq_priority j_hp j = true

end JLFP

section JLDP

variable (higher_eq_priority : JLDP_policy Job)

def respects_JLDP_policy_under_weak_APA : Prop :=
  ∀ j j_hp cpu t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t →
    scheduled_on sched j_hp cpu t = true →
    can_execute_on alpha (job_task j) cpu →
    higher_eq_priority t j_hp j = true

end JLDP

end Properties

end Prosa.Classic.Model.Schedule.Apa.Platform
