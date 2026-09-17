-- Translated from: ../rt-proofs/classic/model/schedule/global/basic/schedule.v
import Prosa.Classic.Util.Notation
import Prosa.Classic.Util.Bigcat
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Global.Basic.Schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Util.Bigcat
open Prosa.Util.Bigcat

namespace Schedule

private def make_sequence' {T : Type _} (opt : Option T) : List T :=
  match opt with
  | some j => [j]
  | none => []

abbrev processor (num_cpus : ℕ) := Fin num_cpus

section ScheduleDef

variable (Job : Type _) [DecidableEq Job]
variable (num_cpus : ℕ)

def schedule := processor num_cpus → Time → Option Job

end ScheduleDef

section ScheduledJobs

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable {arr_seq : arrival_sequence Job}
variable (job_cost : Job → Time)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (j : Job)

def scheduled_on (cpu : processor num_cpus) (t : Time) : Bool :=
  sched cpu t == some j

def scheduled (t : Time) : Prop :=
  ∃ cpu : processor num_cpus, scheduled_on sched j cpu t = true

def is_idle (cpu : processor num_cpus) (t : Time) : Prop :=
  sched cpu t = none

def service_at (t : Time) : ℕ :=
  ∑ cpu : Fin num_cpus, if scheduled_on sched j cpu t then 1 else 0

def service (t' : Time) : ℕ :=
  ∑ t ∈ Finset.Ico 0 t', service_at sched j t

def service_during (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2, service_at sched j t

def completed (t : Time) : Prop :=
  service sched j t ≥ job_cost j

def pending (t : Time) : Prop :=
  has_arrived job_arrival j t ∧ ¬ completed job_cost sched j t

def backlogged (t : Time) : Prop :=
  pending job_arrival job_cost sched j t ∧ ¬ scheduled sched j t

def carried_in (t1 : Time) : Prop :=
  arrived_before job_arrival j t1 ∧ ¬ completed job_cost sched j t1

def carried_out (t1 t2 : Time) : Prop :=
  arrived_before job_arrival j t2 ∧ ¬ completed job_cost sched j t2

end ScheduledJobs

section ScheduledJobsList

variable {Job : Type _} [DecidableEq Job]
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

def jobs_scheduled_at (t : Time) : List Job :=
  bigcat_ord num_cpus (fun cpu => make_sequence' (sched cpu t))

def jobs_scheduled_between (t1 t2 : Time) : List Job :=
  (bigcat_nat (fun t => jobs_scheduled_at sched t) t1 t2).dedup

end ScheduledJobsList

section ValidSchedules

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

def sequential_jobs : Prop :=
  ∀ j t (cpu1 cpu2 : processor num_cpus),
    sched cpu1 t = some j → sched cpu2 t = some j → cpu1 = cpu2

def jobs_must_arrive_to_execute : Prop :=
  ∀ j t, scheduled sched j t → has_arrived job_arrival j t

def completed_jobs_dont_execute : Prop :=
  ∀ j t, service sched j t ≤ job_cost j

def jobs_come_from_arrival_sequence (arr_seq : arrival_sequence Job) : Prop :=
  ∀ j t, scheduled sched j t → arrives_in arr_seq j

end ValidSchedules

section JobLemmas

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (j : Job)

section Basic

theorem not_scheduled_no_service :
    ∀ t, ¬ scheduled sched j t ↔ service_at sched j t = 0 := by
  intro t
  constructor
  · intro h_not_sched
    unfold service_at
    apply Finset.sum_eq_zero
    intro cpu _
    simp only [ite_eq_right_iff]
    intro h_on
    exfalso; apply h_not_sched
    exact ⟨cpu, h_on⟩
  · intro h_zero h_sched
    unfold service_at at h_zero
    obtain ⟨cpu, h_on⟩ := h_sched
    have h_le : (if scheduled_on sched j cpu t = true then 1 else 0 : ℕ) ≤
        ∑ cpu : Fin num_cpus, if scheduled_on sched j cpu t = true then 1 else 0 :=
      Finset.single_le_sum (f := fun cpu => if scheduled_on sched j cpu t = true then 1 else 0)
        (fun i _ => by simp only []; split_ifs <;> omega) (Finset.mem_univ cpu)
    simp only [h_on, ite_true] at h_le
    linarith

theorem cumulative_service_implies_service :
    ∀ t1 t2,
      service_during sched j t1 t2 ≠ 0 →
      ∃ t, t1 ≤ t ∧ t < t2 ∧ service_at sched j t ≠ 0 := by
  intro t1 t2 h_nonzero
  unfold service_during at h_nonzero
  by_contra h_all_zero
  push_neg at h_all_zero
  apply h_nonzero
  apply Finset.sum_eq_zero
  intro t ht
  rw [Finset.mem_Ico] at ht
  exact h_all_zero t ht.1 ht.2

theorem service_implies_cumulative_service :
    ∀ t t1 t2,
      t1 ≤ t → t < t2 →
      service_at sched j t ≠ 0 →
      service_during sched j t1 t2 ≠ 0 := by
  intro t t1 t2 h_ge h_lt h_serv
  unfold service_during
  intro h_zero
  apply h_serv
  have h_mem : t ∈ Finset.Ico t1 t2 := Finset.mem_Ico.mpr ⟨h_ge, h_lt⟩
  have h_all_zero := Finset.sum_eq_zero_iff_of_nonneg (f := fun i => service_at sched j i)
    (fun i _ => Nat.zero_le _) |>.mp h_zero
  exact h_all_zero t h_mem

end Basic

section SequentialJobs

variable (H_sequential_jobs : sequential_jobs sched)
include H_sequential_jobs

theorem service_at_most_one :
    ∀ t, service_at sched j t ≤ 1 := by
  intro t
  by_cases h_sched : scheduled sched j t
  · obtain ⟨cpu, h_on⟩ := h_sched
    unfold service_at
    have h_rest : ∑ cpu' ∈ Finset.univ.erase cpu, (if scheduled_on sched j cpu' t then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro cpu' h_cpu'
      rw [Finset.mem_erase] at h_cpu'
      split_ifs with h_on'
      · exfalso; apply h_cpu'.1
        unfold scheduled_on at h_on h_on'
        have h1 := beq_iff_eq.mp h_on
        have h2 := beq_iff_eq.mp h_on'
        exact H_sequential_jobs j t cpu' cpu h2 h1
      · rfl
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ cpu), h_rest]
    simp [h_on]
  · have h_zero := (not_scheduled_no_service sched j t).mp h_sched
    unfold service_at at h_zero ⊢
    omega

theorem cumulative_service_le_delta :
    ∀ t delta, service_during sched j t (t + delta) ≤ delta := by
  intro t delta
  induction delta generalizing t with
  | zero =>
    simp [service_during, Nat.add_zero]
  | succ n ih =>
    show service_during sched j t (t + (n + 1)) ≤ n + 1
    unfold service_during
    have heq : t + (n + 1) = (t + n) + 1 := Nat.add_assoc t n 1
    have hle : t ≤ t + n := Nat.le_add_right t n
    rw [heq, Finset.sum_Ico_succ_top hle]
    have h1 := ih t
    unfold service_during at h1
    have h2 := service_at_most_one sched j H_sequential_jobs (t + n)
    linarith

end SequentialJobs

section Completion

variable (H_completed_jobs : completed_jobs_dont_execute job_cost sched)
include H_completed_jobs

theorem completion_monotonic :
    ∀ t t',
      t ≤ t' →
      completed job_cost sched j t →
      completed job_cost sched j t' := by
  intro t t' h_le h_comp
  unfold completed at h_comp ⊢
  unfold service at h_comp ⊢
  calc job_cost j ≤ ∑ t_0 ∈ Finset.Ico 0 t, service_at sched j t_0 := h_comp
    _ ≤ ∑ t_0 ∈ Finset.Ico 0 t', service_at sched j t_0 := by
        apply Finset.sum_le_sum_of_subset
        apply Finset.Ico_subset_Ico (le_refl 0) h_le

theorem completed_implies_not_scheduled :
    ∀ t,
      completed job_cost sched j t →
      ¬ scheduled sched j t := by
  intro t h_comp h_sched
  have h_bound := H_completed_jobs j (t + 1)
  unfold service at h_bound
  rw [Finset.sum_Ico_succ_top (Nat.zero_le t)] at h_bound
  have h_serv_pos : service_at sched j t ≠ 0 := by
    intro h_eq
    exact ((not_scheduled_no_service sched j t).mpr h_eq) h_sched
  unfold completed service at h_comp
  have h_serv_pos' : service_at sched j t ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_serv_pos
  linarith

theorem cumulative_service_le_job_cost :
    ∀ t t',
      service_during sched j t t' ≤ job_cost j := by
  intro t t'
  by_cases h : t ≤ t'
  · unfold service_during
    calc ∑ t_0 ∈ Finset.Ico t t', service_at sched j t_0
        ≤ ∑ t_0 ∈ Finset.Ico 0 t', service_at sched j t_0 := by
          apply Finset.sum_le_sum_of_subset
          apply Finset.Ico_subset_Ico (Nat.zero_le t) (le_refl t')
      _ ≤ job_cost j := H_completed_jobs j t'
  · unfold service_during
    have : t' ≤ t := Nat.le_of_not_le h
    rw [Finset.Ico_eq_empty_of_le this]
    simp [Nat.zero_le]

end Completion

section Arrival

variable (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched)
include H_jobs_must_arrive

theorem service_before_job_arrival_zero :
    ∀ t,
      t < job_arrival j →
      service_at sched j t = 0 := by
  intro t h_lt
  rw [← not_scheduled_no_service sched j t]
  intro h_sched
  have h_arrived := H_jobs_must_arrive j t h_sched
  change job_arrival j ≤ t at h_arrived
  exact absurd h_lt (not_lt.mpr h_arrived)

theorem cumulative_service_before_job_arrival_zero :
    ∀ t1 t2,
      t2 ≤ job_arrival j →
      ∑ i ∈ Finset.Ico t1 t2, service_at sched j i = 0 := by
  intro t1 t2 h_le
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_Ico] at hi
  exact service_before_job_arrival_zero job_arrival sched j H_jobs_must_arrive i (Nat.lt_of_lt_of_le hi.2 h_le)

theorem service_before_arrival_eq_service_during :
    ∀ t0 t,
      t0 ≤ job_arrival j →
      ∑ t' ∈ Finset.Ico t0 (job_arrival j + t), service_at sched j t' =
      ∑ t' ∈ Finset.Ico (job_arrival j) (job_arrival j + t), service_at sched j t' := by
  intro t0 t h_le
  rw [← Finset.sum_Ico_consecutive _ h_le (Nat.le_add_right _ t)]
  rw [cumulative_service_before_job_arrival_zero job_arrival sched j H_jobs_must_arrive t0 (job_arrival j) (le_refl _)]
  simp

end Arrival

section Pending

variable (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs : completed_jobs_dont_execute job_cost sched)
include H_jobs_must_arrive H_completed_jobs

theorem scheduled_implies_pending :
    ∀ t,
      scheduled sched j t →
      pending job_arrival job_cost sched j t := by
  intro t h_sched
  unfold pending
  constructor
  · exact H_jobs_must_arrive j t h_sched
  · intro h_comp
    exact completed_implies_not_scheduled job_cost sched j H_completed_jobs t h_comp h_sched

end Pending

end JobLemmas

section ScheduledJobsLemmas

variable {Job : Type _} [DecidableEq Job]
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

section Membership

theorem mem_scheduled_jobs_eq_scheduled :
    ∀ j t,
      j ∈ jobs_scheduled_at sched t ↔ scheduled sched j t := by
  intro j t
  unfold jobs_scheduled_at scheduled scheduled_on
  constructor
  · intro h_mem
    have ⟨i, h_in⟩ := mem_bigcat_ord_exists j num_cpus _ h_mem
    use i
    unfold make_sequence' at h_in
    cases h_eq : sched i t with
    | none => simp [h_eq] at h_in
    | some job =>
      simp [h_eq] at h_in
      simp [h_in, beq_iff_eq]
  · intro ⟨cpu, h_on⟩
    have h_eq : sched cpu t = some j := by
      simp [beq_iff_eq] at h_on
      exact h_on
    apply mem_bigcat_ord j num_cpus cpu (fun cpu => make_sequence' (sched cpu t)) cpu.isLt
    unfold make_sequence'
    rw [h_eq]
    simp

end Membership

section Uniqueness

variable (H_sequential_jobs : sequential_jobs sched)
include H_sequential_jobs

theorem scheduled_jobs_uniq :
    ∀ t, (jobs_scheduled_at sched t).Nodup := by
  intro t
  unfold jobs_scheduled_at
  apply bigcat_ord_uniq
  · intro i
    unfold make_sequence'
    cases sched i t with
    | none => exact List.nodup_nil
    | some j => exact List.nodup_singleton j
  · intro x i1 i2 h1 h2
    unfold make_sequence' at h1 h2
    match h_eq1 : sched i1 t, h1 with
    | some j1, h1 =>
      match h_eq2 : sched i2 t, h2 with
      | some j2, h2 =>
        simp [h_eq1] at h1; simp [h_eq2] at h2
        have h_eq1' : sched i1 t = some x := by rw [h_eq1, h1]
        have h_eq2' : sched i2 t = some x := by rw [h_eq2, h2]
        exact H_sequential_jobs x t i1 i2 h_eq1' h_eq2'

end Uniqueness

section NumberOfJobs

theorem num_scheduled_jobs_le_num_cpus :
    ∀ t, (jobs_scheduled_at sched t).length ≤ num_cpus := by
  intro t
  unfold jobs_scheduled_at
  calc (bigcat_ord num_cpus fun cpu => make_sequence' (sched cpu t)).length
      ≤ 1 * num_cpus := by
        apply size_bigcat_ord_max
        intro x
        unfold make_sequence'
        cases sched x t with
        | none => simp
        | some j => simp
    _ = num_cpus := by omega

end NumberOfJobs

end ScheduledJobsLemmas

end Schedule

namespace ScheduleOfSporadicTask

open Schedule

section ScheduledJobs

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable {Job : Type _} [DecidableEq Job]
variable (job_task : Job → sporadic_task)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (tsk : sporadic_task)

def task_scheduled_on (cpu : processor num_cpus) (t : Time) : Bool :=
  match sched cpu t with
  | some j => decide (job_task j = tsk)
  | none => false

def task_is_scheduled (t : Time) : Prop :=
  ∃ cpu : processor num_cpus, task_scheduled_on job_task sched tsk cpu t = true

def jobs_of_task_scheduled_between (t1 t2 : Time) : List Job :=
  (jobs_scheduled_between sched t1 t2).filter (fun j => decide (job_task j = tsk))

end ScheduledJobs

section ScheduleProperties

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable {Job : Type _} [DecidableEq Job]
variable (job_cost : Job → Time)
variable (job_task : Job → sporadic_task)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

def jobs_of_same_task_dont_execute_in_parallel : Prop :=
  ∀ j j' t,
    job_task j = job_task j' →
    scheduled sched j t →
    scheduled sched j' t →
    j = j'

end ScheduleProperties

section BasicLemmas

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable {Job : Type _} [DecidableEq Job]
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (jobs_dont_execute_after_completion : completed_jobs_dont_execute job_cost sched)
variable (tsk : sporadic_task)
variable (j : Job)
variable (H_job_of_task : job_task j = tsk)
variable (valid_job :
  Prosa.Classic.Model.Arrival.Basic.Job.valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
include jobs_dont_execute_after_completion H_job_of_task valid_job

theorem cumulative_service_le_task_cost :
    ∀ t t',
      service_during sched j t t' ≤ task_cost tsk := by
  intro t t'
  have h_le_job := Schedule.cumulative_service_le_job_cost job_cost sched j jobs_dont_execute_after_completion t t'
  have h_valid := valid_job
  unfold Prosa.Classic.Model.Arrival.Basic.Job.valid_sporadic_job at h_valid
  obtain ⟨_, h_cost_le, _⟩ := h_valid
  unfold Prosa.Classic.Model.Arrival.Basic.Job.job_cost_le_task_cost at h_cost_le
  rw [H_job_of_task] at h_cost_le
  exact le_trans h_le_job h_cost_le

end BasicLemmas

end ScheduleOfSporadicTask

end Prosa.Classic.Model.Schedule.Global.Basic.Schedule
