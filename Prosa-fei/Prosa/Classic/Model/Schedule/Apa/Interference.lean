-- Translated from: ../rt-proofs/classic/model/schedule/apa/interference.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Model.Priority
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Apa.Interference

open Classical
open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Workload
open Prosa.Classic.Model.Schedule.Apa.Affinity
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Arrival.Basic.Job

section PossibleInterferingTasks

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable {num_cpus : ℕ}
variable (alpha : task_affinity sporadic_task num_cpus)

section FP

variable (higher_eq_priority : FP_policy sporadic_task)
variable (tsk : sporadic_task)
variable (alpha' : affinity num_cpus)
variable (tsk_other : sporadic_task)

def higher_priority_task_in : Prop :=
  higher_eq_priority tsk_other tsk = true ∧
  tsk_other ≠ tsk ∧
  affinity_intersects alpha' (alpha tsk_other)

end FP

section JLFP

variable (tsk : sporadic_task)
variable (alpha' : affinity num_cpus)
variable (tsk_other : sporadic_task)

def different_task_in : Prop :=
  tsk_other ≠ tsk ∧
  affinity_intersects alpha' (alpha tsk_other)

end JLFP

end PossibleInterferingTasks

section InterferenceDefs

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_task : Job → sporadic_task)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

variable (alpha : task_affinity sporadic_task num_cpus)

variable (j : Job)

section TotalInterference

noncomputable def total_interference (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    if backlogged job_arrival job_cost sched j t then 1 else 0

end TotalInterference

section JobInterference

variable (job_other : Job)

noncomputable def job_interference (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    ∑ cpu : Fin num_cpus,
      if backlogged job_arrival job_cost sched j t ∧
         can_execute_on alpha (job_task j) cpu ∧
         scheduled_on sched job_other cpu t = true
      then 1 else 0

end JobInterference

section TaskInterference

variable (tsk_other : sporadic_task)

noncomputable def task_interference (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    ∑ cpu : Fin num_cpus,
      if backlogged job_arrival job_cost sched j t ∧
         can_execute_on alpha (job_task j) cpu ∧
         task_scheduled_on job_task sched tsk_other cpu t = true
      then 1 else 0

end TaskInterference

section TaskInterferenceJobList

variable (tsk_other : sporadic_task)

noncomputable def task_interference_joblist (t1 t2 : Time) : ℕ :=
  ∑ j' ∈ (jobs_scheduled_between sched t1 t2).toFinset,
    if job_task j' = tsk_other
    then job_interference job_arrival job_cost job_task sched alpha j j' t1 t2
    else 0

end TaskInterferenceJobList

section BasicLemmas

theorem total_interference_le_delta :
    ∀ t1 t2,
      total_interference job_arrival job_cost sched j t1 t2 ≤ t2 - t1 := by
  intro t1 t2
  unfold total_interference
  calc ∑ t ∈ Finset.Ico t1 t2, (if backlogged job_arrival job_cost sched j t then 1 else 0)
      ≤ ∑ _t ∈ Finset.Ico t1 t2, 1 := by
        apply Finset.sum_le_sum
        intro t _
        split_ifs <;> omega
    _ = (Finset.Ico t1 t2).card := by simp
    _ ≤ t2 - t1 := by simp [Nat.card_Ico]

theorem job_interference_le_service :
    ∀ j_other t1 t2,
      job_interference job_arrival job_cost job_task sched alpha j j_other t1 t2 ≤
        service_during sched j_other t1 t2 := by
  intro j_other t1 t2
  unfold job_interference service_during service_at
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro cpu _
  by_cases hb : backlogged job_arrival job_cost sched j t
  · by_cases hc : can_execute_on alpha (job_task j) cpu
    · simp [hb, hc]
    · simp [hb, hc]
  · simp [hb]

theorem task_interference_le_workload :
    ∀ tsk t1 t2,
      task_interference job_arrival job_cost job_task sched alpha j tsk t1 t2 ≤
        workload job_task sched tsk t1 t2 := by
  intro tsk t1 t2
  unfold task_interference workload
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro cpu _
  by_cases hb : backlogged job_arrival job_cost sched j t
  · by_cases hc : can_execute_on alpha (job_task j) cpu
    · simp [hb, hc]
      unfold task_scheduled_on service_of_task
      cases h : sched cpu t with
      | none => simp
      | some j' =>
        simp only [decide_eq_true_eq]
        split_ifs <;> omega
    · simp only [hb, hc, false_and, and_false, ite_false]
      apply Nat.zero_le
  · simp only [hb, false_and, ite_false]
    apply Nat.zero_le

end BasicLemmas

section InterferenceNoParallelism

variable (H_sequential_jobs : sequential_jobs sched)
include H_sequential_jobs

theorem job_interference_le_delta :
    ∀ j_other t1 delta,
      job_interference job_arrival job_cost job_task sched alpha j j_other t1 (t1 + delta) ≤ delta := by
  intro j_other t1 delta
  unfold job_interference
  calc ∑ t ∈ Finset.Ico t1 (t1 + delta),
        ∑ cpu : Fin num_cpus,
          (if backlogged job_arrival job_cost sched j t ∧
              can_execute_on alpha (job_task j) cpu ∧
              scheduled_on sched j_other cpu t = true
           then 1 else 0)
      ≤ ∑ _t ∈ Finset.Ico t1 (t1 + delta), 1 := by
        apply Finset.sum_le_sum
        intro t _
        by_cases hex : ∃ cpu : Fin num_cpus, scheduled_on sched j_other cpu t = true
        · obtain ⟨cpu₀, hcpu₀⟩ := hex
          -- Since j_other is scheduled on cpu₀, by sequential_jobs it's only on cpu₀
          have hseq := H_sequential_jobs
          unfold sequential_jobs at hseq
          unfold scheduled_on at hcpu₀
          have hsome : sched cpu₀ t = some j_other := by
            rw [beq_iff_eq] at hcpu₀; exact hcpu₀
          -- The sum is at most 1 since only cpu₀ can contribute
          calc ∑ cpu : Fin num_cpus,
                (if backlogged job_arrival job_cost sched j t ∧
                    can_execute_on alpha (job_task j) cpu ∧
                    scheduled_on sched j_other cpu t = true
                 then 1 else 0)
              ≤ ∑ cpu : Fin num_cpus,
                  (if cpu = cpu₀ then 1 else 0) := by
                apply Finset.sum_le_sum
                intro cpu _
                by_cases hcpu_eq : cpu = cpu₀
                · simp [hcpu_eq]; split_ifs <;> omega
                · simp only [hcpu_eq, ite_false]
                  split_ifs with hcond
                  · exfalso; apply hcpu_eq
                    obtain ⟨_, _, hsched⟩ := hcond
                    unfold scheduled_on at hsched
                    rw [beq_iff_eq] at hsched
                    exact hseq j_other t cpu cpu₀ hsched hsome
                  · omega
            _ ≤ 1 := by
                simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, le_refl]
        · push_neg at hex
          have : ∀ cpu : Fin num_cpus, ¬(scheduled_on sched j_other cpu t = true) := hex
          calc ∑ cpu : Fin num_cpus,
                (if backlogged job_arrival job_cost sched j t ∧
                    can_execute_on alpha (job_task j) cpu ∧
                    scheduled_on sched j_other cpu t = true
                 then 1 else 0)
              = ∑ _cpu : Fin num_cpus, 0 := by
                apply Finset.sum_congr rfl
                intro cpu _
                have hns := this cpu
                split_ifs with hcond
                · exact absurd hcond.2.2 hns
                · rfl
            _ = 0 := by simp
            _ ≤ 1 := by omega
    _ = (Finset.Ico t1 (t1 + delta)).card := by simp
    _ ≤ delta := by simp [Nat.card_Ico]

end InterferenceNoParallelism

section BoundUsingPerTaskInterference

theorem interference_le_interference_joblist :
    ∀ tsk t1 t2,
      task_interference job_arrival job_cost job_task sched alpha j tsk t1 t2 ≤
        task_interference_joblist job_arrival job_cost job_task sched alpha j tsk t1 t2 := by
  intro tsk t1 t2
  unfold task_interference task_interference_joblist job_interference
  -- Step 1: For each (t, cpu), bound the LHS summand by the sum over jobs
  -- LHS: ∑_t ∑_cpu (if backlogged ∧ can_execute ∧ task_scheduled_on then 1 else 0)
  -- RHS: ∑_j' (if job_task j' = tsk then ∑_t ∑_cpu (if backlogged ∧ can_execute ∧ scheduled_on j' then 1 else 0) else 0)
  -- Strategy: show LHS ≤ ∑_t ∑_cpu ∑_j' (if job_task j' = tsk then ... else 0) = RHS (by Finset.sum_comm)
  calc ∑ t ∈ Finset.Ico t1 t2,
        ∑ cpu : Fin num_cpus,
          (if backlogged job_arrival job_cost sched j t ∧
              can_execute_on alpha (job_task j) cpu ∧
              task_scheduled_on job_task sched tsk cpu t = true
           then 1 else 0)
      ≤ ∑ t ∈ Finset.Ico t1 t2,
          ∑ cpu : Fin num_cpus,
            ∑ j' ∈ (jobs_scheduled_between sched t1 t2).toFinset,
              (if job_task j' = tsk then
                (if backlogged job_arrival job_cost sched j t ∧
                    can_execute_on alpha (job_task j) cpu ∧
                    scheduled_on sched j' cpu t = true
                 then 1 else 0)
              else 0) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro cpu _
        by_cases hb : backlogged job_arrival job_cost sched j t
        · by_cases hc : can_execute_on alpha (job_task j) cpu
          · by_cases hts : task_scheduled_on job_task sched tsk cpu t = true
            · -- LHS simplifies to 1
              rw [if_pos ⟨hb, hc, hts⟩]
              unfold task_scheduled_on at hts
              cases hsched : sched cpu t with
              | none => simp [hsched] at hts
              | some j' =>
                simp [hsched, decide_eq_true_eq] at hts
                have hj'_mem : j' ∈ (jobs_scheduled_between sched t1 t2).toFinset := by
                  rw [List.mem_toFinset]
                  unfold jobs_scheduled_between
                  rw [List.mem_dedup]
                  rw [Finset.mem_Ico] at ht
                  apply Prosa.Util.Bigcat.mem_bigcat_nat (x := j') (m := t1) (n := t2) (j := t)
                  · exact ⟨ht.1, ht.2⟩
                  · rw [mem_scheduled_jobs_eq_scheduled]
                    unfold scheduled
                    exact ⟨cpu, by unfold scheduled_on; rw [hsched]; simp⟩
                have hsched_on : scheduled_on sched j' cpu t = true := by
                  unfold scheduled_on; rw [hsched]; simp
                have h_term : (if job_task j' = tsk then
                    (if backlogged job_arrival job_cost sched j t ∧
                        can_execute_on alpha (job_task j) cpu ∧
                        scheduled_on sched j' cpu t = true
                     then 1 else 0)
                  else 0) = 1 := by
                  rw [if_pos hts, if_pos ⟨hb, hc, hsched_on⟩]
                calc (1 : ℕ) = (if job_task j' = tsk then
                      (if backlogged job_arrival job_cost sched j t ∧
                          can_execute_on alpha (job_task j) cpu ∧
                          scheduled_on sched j' cpu t = true
                       then 1 else 0)
                    else 0) := h_term.symm
                  _ ≤ ∑ j'' ∈ (jobs_scheduled_between sched t1 t2).toFinset,
                        (if job_task j'' = tsk then
                          (if backlogged job_arrival job_cost sched j t ∧
                              can_execute_on alpha (job_task j) cpu ∧
                              scheduled_on sched j'' cpu t = true
                           then 1 else 0)
                        else 0) := by
                      apply Finset.single_le_sum (fun i _ => ?_) hj'_mem
                      split_ifs <;> omega
            · -- LHS simplifies to 0
              rw [if_neg (by intro ⟨_, _, h⟩; exact hts h)]
              apply Finset.sum_nonneg; intro j' _; split_ifs <;> omega
          · simp only [hb, hc, false_and, and_false, ite_false]
            apply Finset.sum_nonneg; intro j' _; split_ifs <;> omega
        · simp only [hb, false_and, ite_false]
          apply Finset.sum_nonneg; intro j' _; split_ifs <;> omega
    _ = ∑ t ∈ Finset.Ico t1 t2,
          ∑ j' ∈ (jobs_scheduled_between sched t1 t2).toFinset,
            ∑ cpu : Fin num_cpus,
              (if job_task j' = tsk then
                (if backlogged job_arrival job_cost sched j t ∧
                    can_execute_on alpha (job_task j) cpu ∧
                    scheduled_on sched j' cpu t = true
                 then 1 else 0)
              else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.sum_comm ..
    _ = ∑ j' ∈ (jobs_scheduled_between sched t1 t2).toFinset,
          ∑ t ∈ Finset.Ico t1 t2,
            ∑ cpu : Fin num_cpus,
              (if job_task j' = tsk then
                (if backlogged job_arrival job_cost sched j t ∧
                    can_execute_on alpha (job_task j) cpu ∧
                    scheduled_on sched j' cpu t = true
                 then 1 else 0)
              else 0) := by
      exact Finset.sum_comm ..
    _ = ∑ j' ∈ (jobs_scheduled_between sched t1 t2).toFinset,
          (if job_task j' = tsk then
            ∑ t ∈ Finset.Ico t1 t2,
              ∑ cpu : Fin num_cpus,
                (if backlogged job_arrival job_cost sched j t ∧
                    can_execute_on alpha (job_task j) cpu ∧
                    scheduled_on sched j' cpu t = true
                 then 1 else 0)
          else 0) := by
      apply Finset.sum_congr rfl
      intro j' _
      split_ifs with h
      · rfl
      · simp

end BoundUsingPerTaskInterference

end InterferenceDefs

end Prosa.Classic.Model.Schedule.Apa.Interference
