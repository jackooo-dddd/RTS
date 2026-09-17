-- Translated from: ../rt-proofs/classic/model/schedule/apa/constrained_deadlines.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Interference
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Apa.Constrained_deadlines

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Apa.Interference
open Prosa.Classic.Model.Schedule.Apa.Affinity
open Schedule ScheduleOfSporadicTask

section Platform

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_task : Job → sporadic_task)
variable (arr_seq : arrival_sequence Job)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (alpha : task_affinity sporadic_task num_cpus)

def apa_work_conserving :=
  ∀ j t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t →
    ∀ cpu,
      can_execute_on alpha (job_task j) cpu →
      ∃ j_other, scheduled_on sched j_other cpu t = true

def respects_FP_policy_under_weak_APA
    (higher_eq_priority : FP_policy sporadic_task) :=
  ∀ j j_hp cpu t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t →
    scheduled_on sched j_hp cpu t = true →
    can_execute_on alpha (job_task j) cpu →
    higher_eq_priority (job_task j_hp) (job_task j) = true

end Platform

section Lemmas

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
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (alpha : task_affinity sporadic_task num_cpus)

variable (H_valid_job_parameters :
  ∀ j,
    arrives_in arr_seq j →
    valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

section NoMultipleJobs

variable (higher_eq_priority : JLDP_policy Job)
variable (H_work_conserving :
  apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
variable (H_respects_JLDP_policy :
  ∀ j j_hp cpu t,
    arrives_in arr_seq j →
    backlogged job_arrival job_cost sched j t →
    scheduled_on sched j_hp cpu t = true →
    can_execute_on alpha (job_task j) cpu →
    higher_eq_priority t j_hp j = true)

variable (ts : List sporadic_task)

variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (H_sequential_jobs : sequential_jobs sched)
variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

variable (H_sporadic_tasks :
  sporadic_task_model task_period job_arrival job_task arr_seq)

variable (tsk : sporadic_task)
variable (H_valid_task : is_valid_sporadic_task task_cost task_period task_deadline tsk)

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

variable (t : Time)
variable (H_j_backlogged : backlogged job_arrival job_cost sched j t)

variable (H_all_previous_jobs_completed :
  ∀ j_other tsk_other,
    arrives_in arr_seq j_other →
    job_task j_other = tsk_other →
    job_arrival j_other + task_period tsk_other ≤ t →
    completed job_cost sched j_other (job_arrival j_other + task_period (job_task j_other)))

def scheduled_task_other_than (tsk tsk_other : sporadic_task) : Prop :=
  task_is_scheduled job_task sched tsk_other t ∧ tsk_other ≠ tsk

theorem platform_at_most_one_pending_job_of_each_task
    (H_sporadic_tasks :
      sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_all_previous_jobs_completed :
      ∀ j_other tsk_other,
        arrives_in arr_seq j_other →
        job_task j_other = tsk_other →
        job_arrival j_other + task_period tsk_other ≤ t →
        completed job_cost sched j_other (job_arrival j_other + task_period (job_task j_other))) :
    ∀ j1 j2,
      arrives_in arr_seq j1 →
      arrives_in arr_seq j2 →
      pending job_arrival job_cost sched j1 t →
      pending job_arrival job_cost sched j2 t →
      job_task j1 = job_task j2 →
      j1 = j2 := by
    intro j1 j2 ARR1 ARR2 PENDING1 PENDING2 SAMEtsk
    by_contra DIFF
    obtain ⟨ARRIVED1, NOTCOMP1⟩ := PENDING1
    obtain ⟨ARRIVED2, NOTCOMP2⟩ := PENDING2
    by_cases h : job_arrival j1 ≤ job_arrival j2
    · -- j1 arrives before or at j2
      have SPO' := H_sporadic_tasks j1 j2 DIFF ARR1 ARR2 SAMEtsk h
      have LEt : job_arrival j1 + task_period (job_task j1) ≤ t := by
        exact le_trans SPO' ARRIVED2
      have COMP1 := H_all_previous_jobs_completed j1 (job_task j1) ARR1 rfl LEt
      exact NOTCOMP1 (completion_monotonic job_cost sched j1 H_completed_jobs_dont_execute
        (job_arrival j1 + task_period (job_task j1)) t LEt COMP1)
    · -- j2 arrives before j1
      push_neg at h
      have h' : job_arrival j2 ≤ job_arrival j1 := le_of_lt h
      have DIFF' : j2 ≠ j1 := Ne.symm DIFF
      have SAMEtsk' : job_task j2 = job_task j1 := SAMEtsk.symm
      have SPO' := H_sporadic_tasks j2 j1 DIFF' ARR2 ARR1 SAMEtsk' h'
      have LEt : job_arrival j2 + task_period (job_task j2) ≤ t := by
        exact le_trans SPO' ARRIVED1
      have COMP2 := H_all_previous_jobs_completed j2 (job_task j2) ARR2 rfl LEt
      exact NOTCOMP2 (completion_monotonic job_cost sched j2 H_completed_jobs_dont_execute
        (job_arrival j2 + task_period (job_task j2)) t LEt COMP2)

end NoMultipleJobs

section NoMultipleJobsFP

variable (higher_eq_priority : FP_policy sporadic_task)
variable (H_work_conserving :
  apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
variable (H_respects_JLDP_policy :
  respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched alpha higher_eq_priority)

variable (ts : List sporadic_task)

variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (H_sequential_jobs : sequential_jobs sched)
variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_sporadic_tasks :
  sporadic_task_model task_period job_arrival job_task arr_seq)

variable (tsk : sporadic_task)
variable (H_valid_task : is_valid_sporadic_task task_cost task_period task_deadline tsk)

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

variable (t : Time)
variable (H_j_backlogged : backlogged job_arrival job_cost sched j t)
variable (H_t_before_period : t < job_arrival j + task_period tsk)

variable (H_all_previous_jobs_completed :
  ∀ j_other tsk_other,
    arrives_in arr_seq j_other →
    job_task j_other = tsk_other →
    higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) tsk_other →
    completed job_cost sched j_other (job_arrival j_other + task_period tsk_other))

variable (H_all_previous_jobs_of_tsk_completed :
  ∀ j0,
    arrives_in arr_seq j0 →
    job_task j0 = tsk →
    job_arrival j0 < job_arrival j →
    completed job_cost sched j0 (job_arrival j0 + task_period tsk))

def scheduled_task_with_higher_eq_priority (tsk tsk_other : sporadic_task) : Prop :=
  task_is_scheduled job_task sched tsk_other t ∧
  higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) tsk_other

theorem platform_fp_no_multiple_jobs_of_interfering_tasks
    (H_sporadic_tasks :
      sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_completed_jobs_dont_execute :
      completed_jobs_dont_execute job_cost sched)
    (H_all_previous_jobs_completed :
      ∀ j_other tsk_other,
        arrives_in arr_seq j_other →
        job_task j_other = tsk_other →
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) tsk_other →
        completed job_cost sched j_other (job_arrival j_other + task_period tsk_other)) :
    ∀ j1 j2,
      arrives_in arr_seq j1 →
      arrives_in arr_seq j2 →
      pending job_arrival job_cost sched j1 t →
      pending job_arrival job_cost sched j2 t →
      job_task j1 = job_task j2 →
      higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) (job_task j1) →
      j1 = j2 := by
    intro j1 j2 ARR1 ARR2 PENDING1 PENDING2 SAMEtsk INTERF
    by_contra DIFF
    obtain ⟨ARRIVED1, NOTCOMP1⟩ := PENDING1
    obtain ⟨ARRIVED2, NOTCOMP2⟩ := PENDING2
    by_cases h : job_arrival j1 ≤ job_arrival j2
    · have SPO' := H_sporadic_tasks j1 j2 DIFF ARR1 ARR2 SAMEtsk h
      have LEt : job_arrival j1 + task_period (job_task j1) ≤ t := le_trans SPO' ARRIVED2
      have COMP1 := H_all_previous_jobs_completed j1 (job_task j1) ARR1 rfl INTERF
      exact NOTCOMP1 (completion_monotonic job_cost sched j1 H_completed_jobs_dont_execute
        (job_arrival j1 + task_period (job_task j1)) t LEt COMP1)
    · push_neg at h
      have h' : job_arrival j2 ≤ job_arrival j1 := le_of_lt h
      have DIFF' : j2 ≠ j1 := Ne.symm DIFF
      have SAMEtsk' : job_task j2 = job_task j1 := SAMEtsk.symm
      have SPO' := H_sporadic_tasks j2 j1 DIFF' ARR2 ARR1 SAMEtsk' h'
      have LEt : job_arrival j2 + task_period (job_task j2) ≤ t := le_trans SPO' ARRIVED1
      have INTERF2 : higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) (job_task j2) := by
        rwa [← SAMEtsk]
      have COMP2 := H_all_previous_jobs_completed j2 (job_task j2) ARR2 rfl INTERF2
      exact NOTCOMP2 (completion_monotonic job_cost sched j2 H_completed_jobs_dont_execute
        (job_arrival j2 + task_period (job_task j2)) t LEt COMP2)

include H_j_arrives in
theorem platform_fp_no_multiple_jobs_of_tsk
    (H_sporadic_tasks :
      sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_completed_jobs_dont_execute :
      completed_jobs_dont_execute job_cost sched)
    (H_valid_task : is_valid_sporadic_task task_cost task_period task_deadline tsk)
    (H_j_backlogged : backlogged job_arrival job_cost sched j t)
    (H_job_of_tsk : job_task j = tsk)
    (H_t_before_period : t < job_arrival j + task_period tsk)
    (H_all_previous_jobs_of_tsk_completed :
      ∀ j0,
        arrives_in arr_seq j0 →
        job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + task_period tsk)) :
    ∀ j',
      arrives_in arr_seq j' →
      pending job_arrival job_cost sched j' t →
      job_task j' = tsk →
      j' = j := by
    intro j' ARR' PENDING' SAMEtsk
    by_contra DIFF
    have JARR := H_j_arrives
    obtain ⟨⟨ARRIVED, NOTCOMP⟩, _NOTSCHED⟩ := H_j_backlogged
    obtain ⟨ARRIVED', NOTCOMP'⟩ := PENDING'
    by_cases h : job_arrival j' ≤ job_arrival j
    · -- Case 1: j' arrives before or at j
      have SPO' := H_sporadic_tasks j' j DIFF ARR' JARR
        (by rw [SAMEtsk, H_job_of_tsk]) h
      have hperiod_pos : task_period tsk > 0 := H_valid_task.2.1
      have hlt : job_arrival j' < job_arrival j := by
        have h1 : job_arrival j' + task_period tsk ≤ job_arrival j := by
          have := GE.ge.le SPO'; rwa [SAMEtsk] at this
        exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hperiod_pos) h1
      have COMP' := H_all_previous_jobs_of_tsk_completed j' ARR' SAMEtsk hlt
      apply NOTCOMP'
      apply completion_monotonic job_cost sched j' H_completed_jobs_dont_execute
        (job_arrival j' + task_period tsk) t _ COMP'
      have : job_arrival j' + task_period (job_task j') ≤ job_arrival j := SPO'
      rw [SAMEtsk] at this
      exact le_trans this ARRIVED
    · -- Case 2: j' arrives after j
      push_neg at h
      have DIFF' : j ≠ j' := Ne.symm DIFF
      have SAMEtsk' : job_task j = job_task j' := by rw [H_job_of_tsk, SAMEtsk]
      have SPO' := H_sporadic_tasks j j' DIFF' JARR ARR' SAMEtsk' (le_of_lt h)
      rw [H_job_of_tsk] at SPO'
      -- SPO': job_arrival j' ≥ job_arrival j + task_period tsk
      -- H_t_before_period: t < job_arrival j + task_period tsk
      -- ARRIVED': job_arrival j' ≤ t
      exact absurd (le_trans SPO' ARRIVED') (not_le.mpr H_t_before_period)

end NoMultipleJobsFP

end Lemmas

end Prosa.Classic.Model.Schedule.Apa.Constrained_deadlines
