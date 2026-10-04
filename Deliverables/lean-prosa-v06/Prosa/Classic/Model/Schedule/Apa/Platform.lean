-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/apa/platform.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 37)

import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Interference
import Prosa.Classic.Model.Schedule.Apa.Affinity

/-!
Platform properties under processor affinities (Rocq module `Platform` of
`classic/model/schedule/apa`).  Binder lists follow the Rocq contract.
Boolean predicates in proposition position are `… = true`.
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Schedule.Apa.Platform.Platform

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Priority.Priority (FP_policy JLFP_policy JLDP_policy)
open Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity

universe u v

def apa_work_conserving {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (alpha : task_affinity sporadic_task num_cpus) : Prop :=
  ∀ j t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t = true →
    ∀ cpu,
      can_execute_on alpha (job_task j) cpu = true →
      ∃ j_other, scheduled_on sched j_other cpu t = true

def respects_affinity {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_task : Job → sporadic_task) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (alpha : task_affinity sporadic_task num_cpus) : Prop :=
  ∀ j cpu t,
    scheduled_on sched j cpu t = true →
    can_execute_on alpha (job_task j) cpu = true

def respects_FP_policy_under_weak_APA {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : FP_policy sporadic_task) : Prop :=
  ∀ j j_hp cpu t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t = true →
    scheduled_on sched j_hp cpu t = true →
    can_execute_on alpha (job_task j) cpu = true →
    higher_eq_priority (job_task j_hp) (job_task j) = true

def respects_JLFP_policy_under_weak_APA {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLFP_policy Job) : Prop :=
  ∀ j j_hp cpu t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t = true →
    scheduled_on sched j_hp cpu t = true →
    can_execute_on alpha (job_task j) cpu = true →
    higher_eq_priority j_hp j = true

def respects_JLDP_policy_under_weak_APA {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) : Prop :=
  ∀ j j_hp cpu t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t = true →
    scheduled_on sched j_hp cpu t = true →
    can_execute_on alpha (job_task j) cpu = true →
    higher_eq_priority t j_hp j = true

end Prosa.Classic.Model.Schedule.Apa.Platform.Platform
