import Solutions.Support.WorkloadArith
import Prosa.Classic.Model.Schedule.Global.Workload

/-!
Job-level view of a task's workload in an interval (classic `workload_eq_workload_joblist`) and
per-job service bounds, used for the sporadic workload bounds of the 2009/2014 case studies.
-/

set_option linter.unusedVariables false

namespace Solutions.Support.WorkloadJobs

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Util.Sum (sumSeq)

universe u v

/-- The workload of `k` in `[t1, t2)` is the sum of the service in `[t1, t2)` of a duplicate-free list
of jobs of `k`, each scheduled at some instant of `[t1, t2)`. -/
theorem workload_as_jobs {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_task : Job → sporadic_task) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (k : sporadic_task) (t1 t2 : time) :
    ∃ L : List Job, L.Nodup ∧
      (∀ x ∈ L, job_task x = k ∧ ∃ s, t1 ≤ s ∧ s < t2 ∧ scheduled sched x s = true) ∧
      workload job_task sched k t1 t2 = sumSeq L (fun x => service_during sched x t1 t2) := by
  refine ⟨jobs_of_task_scheduled_between job_task sched k t1 t2, (List.nodup_dedup _).filter _,
    ?_, workload_eq_workload_joblist job_task sched k t1 t2⟩
  intro x hx
  simp only [jobs_of_task_scheduled_between, jobs_scheduled_between, List.mem_filter,
    List.mem_dedup, decide_eq_true_eq] at hx
  refine ⟨hx.2, ?_⟩
  obtain ⟨s, hs, h1, h2⟩ := Prosa.Util.Bigcat.mem_bigcat_nat_exists (hMem := hx.1)
  refine ⟨s, h1, h2, ?_⟩
  rw [← mem_scheduled_jobs_eq_scheduled]; simpa using hs

theorem service_during_le_remaining {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (x : Job) (t1 t2 : time) (h12 : t1 ≤ t2) :
    service_during sched x t1 t2 ≤ job_cost x - service sched x t1 := by
  have h := H_completed_jobs_dont_execute x t2
  unfold service at h ⊢
  unfold service_during
  rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le t1) h12] at h
  tomega

theorem service_during_le_after_arrival {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (x : Job) (t1 t2 : time) (h1 : t1 ≤ job_arrival x) :
    service_during sched x t1 t2 ≤ t2 - job_arrival x := by
  unfold service_during
  rcases Nat.le_total t2 (job_arrival x) with h | h
  · rw [cumulative_service_before_job_arrival_zero job_arrival sched x
      H_jobs_must_arrive_to_execute t1 t2 h]
    exact Nat.zero_le _
  · rw [← Finset.sum_Ico_consecutive _ h1 h, cumulative_service_before_job_arrival_zero
      job_arrival sched x H_jobs_must_arrive_to_execute t1 _ (le_refl _), Nat.zero_add]
    have := cumulative_service_le_delta sched x H_sequential_jobs (job_arrival x)
      (t2 - job_arrival x)
    unfold service_during at this
    rwa [Nat.add_sub_cancel' h] at this

theorem service_during_le_before_completion {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_sequential_jobs : sequential_jobs sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (x : Job) (t1 t2 c : time) (hc : completed job_cost sched x c = true) :
    service_during sched x t1 t2 ≤ c - t1 := by
  unfold service_during
  have hzero : ∀ s, c ≤ s → service_at sched x s = 0 := by
    intro s hs
    have hcs := completion_monotonic job_cost sched x c s hs hc
    have := completed_implies_not_scheduled job_cost sched x H_completed_jobs_dont_execute s hcs
    have h2 := not_scheduled_no_service sched x s
    rw [this] at h2
    simpa using h2.symm
  rcases Nat.le_total c t1 with h | h
  · rw [Finset.sum_eq_zero (fun s hs => hzero s (le_trans h (Finset.mem_Ico.mp hs).1))]
    exact Nat.zero_le _
  · rcases Nat.le_total t2 c with h' | h'
    · have := cumulative_service_le_delta sched x H_sequential_jobs t1 (t2 - t1)
      unfold service_during at this
      by_cases h12 : t1 ≤ t2
      · rw [Nat.add_sub_cancel' h12] at this; tomega
      · rw [Finset.Ico_eq_empty (by simp only [Prosa.Classic.Model.Time.Time.time] at *; omega)]; simp
    · rw [← Finset.sum_Ico_consecutive _ h h',
        Finset.sum_eq_zero (fun s hs => hzero s (Finset.mem_Ico.mp hs).1), Nat.add_zero]
      have := cumulative_service_le_delta sched x H_sequential_jobs t1 (c - t1)
      unfold service_during at this
      rwa [Nat.add_sub_cancel' h] at this

/-- A job scheduled at `s` is not complete at any `t ≤ s`. -/
theorem not_completed_of_scheduled_later {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (x : Job) (t s : time) (hts : t ≤ s) (hs : scheduled sched x s = true) :
    completed job_cost sched x t = false := by
  cases hc : completed job_cost sched x t
  · rfl
  · have := completion_monotonic job_cost sched x t s hts hc
    have hp := scheduled_implies_pending job_arrival job_cost sched x
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute s hs
    simp [pending, this] at hp

theorem workload_split {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_task : Job → sporadic_task) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (k : sporadic_task) (t1 t2 t3 : time) (h12 : t1 ≤ t2)
    (h23 : t2 ≤ t3) :
    workload job_task sched k t1 t3 = workload job_task sched k t1 t2 + workload job_task sched k t2 t3 := by
  unfold workload
  rw [Finset.sum_Ico_consecutive _ h12 h23]

theorem workload_mono {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_task : Job → sporadic_task) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (k : sporadic_task) (t1 t2 t3 : time) (h23 : t2 ≤ t3) :
    workload job_task sched k t1 t2 ≤ workload job_task sched k t1 t3 := by
  unfold workload
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico (le_refl _) h23)
    (fun _ _ _ => Nat.zero_le _)

/-- If at most one processor runs a job of `k` at a time, `k`'s workload in an interval is at most its
length. -/
theorem workload_le_length {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_task : Job → sporadic_task) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (k : sporadic_task)
    (honce : ∀ s c1 c2 j1 j2, sched c1 s = some j1 → sched c2 s = some j2 → job_task j1 = k →
      job_task j2 = k → c1 = c2)
    (t1 L : time) : workload job_task sched k t1 (t1 + L) ≤ L := by
  unfold workload
  calc ∑ s ∈ Finset.Ico t1 (t1 + L), ∑ cpu : Fin num_cpus, service_of_task job_task k cpu (sched cpu s)
      ≤ ∑ _s ∈ Finset.Ico t1 (t1 + L), 1 := by
        apply Finset.sum_le_sum
        intro s _
        calc ∑ cpu : Fin num_cpus, service_of_task job_task k cpu (sched cpu s)
            = (Finset.univ.filter (fun cpu : Fin num_cpus =>
                ∃ j', sched cpu s = some j' ∧ job_task j' = k)).card := by
              rw [Finset.card_filter]
              apply Finset.sum_congr rfl
              intro cpu _
              unfold service_of_task
              cases sched cpu s with
              | none => simp
              | some j' => by_cases h : job_task j' = k <;> simp [h]
          _ ≤ 1 := by
              apply Finset.card_le_one.mpr
              intro c1 h1 c2 h2
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
              obtain ⟨j1, hs1, ht1⟩ := h1
              obtain ⟨j2, hs2, ht2⟩ := h2
              exact honce s c1 c2 j1 j2 hs1 hs2 ht1 ht2
    _ = L := by simp

end Solutions.Support.WorkloadJobs
