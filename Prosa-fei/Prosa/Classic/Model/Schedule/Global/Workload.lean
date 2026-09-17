-- Translated from: classic/model/schedule/global/workload.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Global.Workload

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask

section WorkloadDef

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable {Job : Type _} [DecidableEq Job]
variable (job_task : Job → sporadic_task)
variable (arr_seq : arrival_sequence Job)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (tsk : sporadic_task)

def service_of_task (_cpu : processor num_cpus) (scheduled_job : Option Job) : Time :=
  match scheduled_job with
  | some j' => if job_task j' = tsk then 1 else 0
  | none => 0

def workload (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    ∑ cpu : Fin num_cpus,
      service_of_task job_task tsk cpu (sched cpu t)

def workload_joblist (t1 t2 : Time) : ℕ :=
  ∑ j ∈ (jobs_of_task_scheduled_between job_task sched tsk t1 t2).toFinset,
    service_during sched j t1 t2

theorem workload_eq_workload_joblist :
    ∀ t1 t2,
      workload job_task sched tsk t1 t2 = workload_joblist job_task sched tsk t1 t2 := by
  intro t1 t2
  simp only [workload, workload_joblist, service_during, service_at, service_of_task, scheduled_on]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cpu _
  rw [Finset.mem_Ico] at ht
  rcases (sched cpu t).eq_none_or_eq_some with h_sched | ⟨j', h_sched⟩
  · simp [h_sched]
  · simp only [h_sched, beq_iff_eq, Option.some.injEq]
    by_cases h_task : job_task j' = tsk
    · simp only [h_task, ite_true]
      have h_mem : j' ∈ (jobs_of_task_scheduled_between job_task sched tsk t1 t2).toFinset := by
        rw [List.mem_toFinset]
        unfold jobs_of_task_scheduled_between
        rw [List.mem_filter]
        refine ⟨?_, by simp [h_task]⟩
        unfold jobs_scheduled_between
        rw [List.mem_dedup]
        apply Prosa.Util.Bigcat.mem_bigcat_nat (x := j') (m := t1) (n := t2) (j := t)
        · exact ⟨ht.1, ht.2⟩
        · rw [mem_scheduled_jobs_eq_scheduled]
          exact ⟨cpu, by unfold scheduled_on; rw [h_sched]; simp⟩
      rw [← Finset.add_sum_erase _ _ h_mem]
      simp only [ite_true]
      have h_rest : ∑ x ∈ (jobs_of_task_scheduled_between job_task sched tsk t1 t2).toFinset.erase j',
          (if j' = x then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_erase] at hj
        simp [show j' ≠ j from Ne.symm hj.1]
      linarith [h_rest]
    · simp only [h_task, ite_false]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      have h_ne : j' ≠ j := by
        intro h_eq; subst h_eq
        rw [List.mem_toFinset] at hj
        unfold jobs_of_task_scheduled_between at hj
        rw [List.mem_filter] at hj
        simp at hj
        exact h_task hj.2
      simp [h_ne]

end WorkloadDef

end Prosa.Classic.Model.Schedule.Global.Workload
