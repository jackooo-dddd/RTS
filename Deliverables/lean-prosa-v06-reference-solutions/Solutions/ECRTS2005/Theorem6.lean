import CaseStudies.ECRTS2005.Theorem6
import Solutions.Support.Common

/-! Reference solution of benchmark task `2005-ECRTS-Theorem6`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.ECRTS2005.Theorem6.SchedulabilityAnalysisEDF

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Util.Sum (sumFiltered sumSeq)
open Solutions.Support.Common (low_interference_of_completed too_much_interference_job sumSeq_le_sumSeq
  sumSeq_mul_left sumSeq_perm)

theorem Theorem6_05 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      0 < job_cost j ∧ job_cost j < job_deadline j ∧ 0 < job_deadline j ∧
        job_deadline j = task_deadline (job_task j) ∧ job_cost j = task_cost (job_task j))
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (uniq_ts : ts.val.Nodup)
    (H_edf_policy : respects_JLFP_policy job_arrival job_cost arr_seq sched
      (EDF job_arrival job_deadline))
    (H_constrained_deadlines : ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_positive_slack : ∀ tsk : sporadic_task, tsk ∈ ts → task_cost tsk < task_deadline tsk)
    (Lemma5_05 : ∀ (j : Job) (a b : time) (tsk : sporadic_task),
      tsk ∈ ts → arrives_in arr_seq j → job_task j = tsk →
      cumulative_task_interference job_arrival job_cost job_task ts num_cpus sched j a b tsk =
        num_cpus * total_interference job_arrival job_cost sched j a b)
    (H_Lemma4_05 : ∀ (tsk_k : sporadic_task) (j : Job) (a b : time) (c : Nat),
      tsk_k ∈ ts → arrives_in arr_seq j → job_task j = tsk_k →
      (c ≤ total_interference job_arrival job_cost sched j a b ↔
        num_cpus * c ≤ sumFiltered ts.val (fun tsk_other => !decide (tsk_other = tsk_k))
          (fun tsk_other =>
            min (task_interference job_arrival job_cost job_task sched j tsk_other a b) c)))
    (worst_case_job_of_task : sporadic_task → Job)
    (H_worst_case_job_arrives : ∀ tsk : sporadic_task, tsk ∈ ts →
      arrives_in arr_seq (worst_case_job_of_task tsk))
    (H_worst_case_job_of_task : ∀ tsk : sporadic_task, tsk ∈ ts →
      job_task (worst_case_job_of_task tsk) = tsk)
    (H_worst_case_interference : ∀ (tsk : sporadic_task) (j : Job),
      tsk ∈ ts → arrives_in arr_seq j → job_task j = tsk →
      total_interference job_arrival job_cost sched j (job_arrival j)
          (job_arrival j + job_deadline j) ≤
        total_interference job_arrival job_cost sched (worst_case_job_of_task tsk)
          (job_arrival (worst_case_job_of_task tsk))
          (job_arrival (worst_case_job_of_task tsk) + job_deadline (worst_case_job_of_task tsk))) :
    taskset_schedulable job_arrival job_cost job_deadline job_task arr_seq ts num_cpus sched ↔
      ∀ tsk : sporadic_task, tsk ∈ ts →
        theorem6_task_condition task_cost task_deadline job_arrival job_cost job_deadline job_task
          ts num_cpus sched worst_case_job_of_task tsk := by
  -- (1) a job meets its deadline iff it is backlogged for at most its slack before the deadline
  have meets : ∀ j : Job, arrives_in arr_seq j →
      (completed job_cost sched j (job_arrival j + job_deadline j) = true ↔
        total_interference job_arrival job_cost sched j (job_arrival j)
          (job_arrival j + job_deadline j) ≤ job_deadline j - job_cost j) := by
    intro j hj
    constructor
    · exact low_interference_of_completed job_arrival job_cost sched H_sequential_jobs
        H_jobs_must_arrive_to_execute j _
    · intro hX
      by_contra hnc
      have := too_much_interference_job job_arrival job_cost sched H_jobs_must_arrive_to_execute j
        (job_deadline j) (le_of_lt (H_valid_job_parameters j hj).2.1) (by simpa using hnc)
      tomega
  have hslack : ∀ tsk j, arrives_in arr_seq j → job_task j = tsk →
      job_deadline j - job_cost j = slack task_cost task_deadline tsk := by
    intro tsk j hj hjt
    obtain ⟨_, _, _, hd, hc⟩ := H_valid_job_parameters j hj
    rw [hd, hc, hjt]; rfl
  -- (2) hence a task meets its deadlines iff its worst-case job does
  have task_iff : ∀ tsk, tsk ∈ ts →
      (task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk ↔
        total_interference job_arrival job_cost sched (worst_case_job_of_task tsk)
          (job_arrival (worst_case_job_of_task tsk))
          (job_arrival (worst_case_job_of_task tsk) + job_deadline (worst_case_job_of_task tsk)) ≤
          slack task_cost task_deadline tsk) := by
    intro tsk htsk
    have hWa := H_worst_case_job_arrives tsk htsk
    have hWt := H_worst_case_job_of_task tsk htsk
    constructor
    · intro h
      have := (meets _ hWa).mp (h _ hWa hWt)
      rwa [hslack tsk _ hWa hWt] at this
    · intro hX j hj hjt
      unfold job_misses_no_deadline
      apply (meets j hj).mpr
      rw [hslack tsk j hj hjt]
      exact le_trans (H_worst_case_interference tsk j htsk hj hjt) hX
  -- (3) and, by Lemmas 4 and 5, the worst-case job meets its deadline iff the task condition holds
  have cond_iff : ∀ tsk, tsk ∈ ts →
      (total_interference job_arrival job_cost sched (worst_case_job_of_task tsk)
          (job_arrival (worst_case_job_of_task tsk))
          (job_arrival (worst_case_job_of_task tsk) + job_deadline (worst_case_job_of_task tsk)) ≤
          slack task_cost task_deadline tsk ↔
        theorem6_task_condition task_cost task_deadline job_arrival job_cost job_deadline job_task
          ts num_cpus sched worst_case_job_of_task tsk) := by
    intro tsk htsk
    have hWa := H_worst_case_job_arrives tsk htsk
    have hWt := H_worst_case_job_of_task tsk htsk
    have hs1 : 1 ≤ slack task_cost task_deadline tsk := by
      have := H_positive_slack tsk htsk; unfold slack; tomega
    have hm := H_at_least_one_cpu
    have L5 := Lemma5_05 (worst_case_job_of_task tsk) (job_arrival (worst_case_job_of_task tsk))
      (job_arrival (worst_case_job_of_task tsk) + job_deadline (worst_case_job_of_task tsk)) tsk
      htsk hWa hWt
    have L4 := fun c => H_Lemma4_05 tsk (worst_case_job_of_task tsk)
      (job_arrival (worst_case_job_of_task tsk))
      (job_arrival (worst_case_job_of_task tsk) + job_deadline (worst_case_job_of_task tsk)) c
      htsk hWa hWt
    unfold cumulative_task_interference at L5
    unfold theorem6_task_condition theorem6_first_condition theorem6_second_condition
      truncated_task_interference_sum task_interference_in_worst_case_window
    simp only [decide_eq_true_eq]
    have hSF : ∀ (P : sporadic_task → Bool) (F : sporadic_task → Nat),
        sumFiltered ts.val P F = sumSeq (ts.val.filter P) F := fun _ _ => rfl
    simp only [hSF] at L4 L5 ⊢
    generalize hL : ts.val.filter (fun k => !decide (k = tsk)) = L at L4 L5
    generalize job_arrival (worst_case_job_of_task tsk) + job_deadline (worst_case_job_of_task tsk) = b
      at L4 L5 ⊢
    generalize job_arrival (worst_case_job_of_task tsk) = a at L4 L5 ⊢
    generalize task_interference job_arrival job_cost job_task sched (worst_case_job_of_task tsk) = I
      at L4 L5 ⊢
    generalize total_interference job_arrival job_cost sched (worst_case_job_of_task tsk) a b = X
      at L4 L5 ⊢
    generalize slack task_cost task_deadline tsk = s at hs1 ⊢
    constructor
    · intro hX
      rcases Nat.lt_or_ge X s with hlt | hge
      · left; by_contra h; exact absurd ((L4 s).mpr (Nat.le_of_not_lt h)) (by omega)
      · right
        have hXs : X = s := le_antisymm hX hge
        have hSle : sumSeq L (fun k => min (I k a b) s) ≤ num_cpus * s := by
          rw [← hXs, ← L5]; exact sumSeq_le_sumSeq _ _ _ (fun k _ => min_le_left _ _)
        have hSeq := le_antisymm hSle ((L4 s).mp hge)
        refine ⟨hSeq, ?_⟩
        by_contra hne
        push_neg at hne
        have hpt : ∀ k ∈ L, (s + 1) * min (I k a b) s ≤ s * I k a b := by
          intro k hk
          rw [← hL, List.mem_filter] at hk
          rcases Nat.eq_zero_or_pos (I k a b) with h0 | hpos
          · rw [h0]; simp
          · have := hne k hk.1 hk.2 hpos
            rw [min_eq_right (le_of_lt this), Nat.mul_comm]
            exact Nat.mul_le_mul_left _ this
        have := sumSeq_le_sumSeq L _ _ hpt
        rw [sumSeq_mul_left, sumSeq_mul_left, hSeq, L5, hXs] at this
        have hpos : 0 < num_cpus * s := Nat.mul_pos hm hs1
        nlinarith
    · rintro (h1 | ⟨hSeq, h, hh, hne, hpos, hle⟩)
      · by_contra hX; exact absurd ((L4 s).mp (by omega)) (by omega)
      · by_contra hX
        have hT := (L4 (s + 1)).mp (by omega)
        have hhL : h ∈ L := by rw [← hL]; exact List.mem_filter.mpr ⟨hh, hne⟩
        have hperm := List.perm_cons_erase hhL
        rw [sumSeq_perm _ hperm] at hT hSeq
        have hcons : ∀ (F : sporadic_task → Nat) (l : List sporadic_task),
            sumSeq (h :: l) F = F h + sumSeq l F := by
          intro F l; unfold sumSeq; simp
        rw [hcons] at hT hSeq
        rw [min_eq_left hle] at hSeq
        rw [min_eq_left (by omega : I h a b ≤ s + 1)] at hT
        have hrest := sumSeq_le_sumSeq (L.erase h) (fun k => s * min (I k a b) (s + 1))
          (fun k => (s + 1) * min (I k a b) s) (by
            intro k _
            rcases Nat.le_total (I k a b) s with hk | hk
            · rw [min_eq_left hk, min_eq_left (by omega : I k a b ≤ s + 1)]
              exact Nat.mul_le_mul_right _ (Nat.le_succ s)
            · rw [min_eq_right hk]
              rcases Nat.eq_or_lt_of_le hk with hk' | hk'
              · rw [← hk', min_eq_left (Nat.le_succ _)]
                exact Nat.mul_le_mul_right _ (Nat.le_succ s)
              · rw [min_eq_right hk', Nat.mul_comm])
        rw [sumSeq_mul_left, sumSeq_mul_left] at hrest
        nlinarith [Nat.mul_le_mul_left s hT]
  constructor
  · intro hsch tsk htsk
    exact (cond_iff tsk htsk).mp ((task_iff tsk htsk).mp (hsch tsk htsk))
  · intro hc tsk htsk
    exact (task_iff tsk htsk).mpr ((cond_iff tsk htsk).mpr (hc tsk htsk))

end CaseStudies.ECRTS2005.Theorem6.SchedulabilityAnalysisEDF

theorem Solutions.ECRTS2005.Theorem6.solution : CaseStudies.ECRTS2005.Theorem6.SchedulabilityAnalysisEDF.Theorem6_05_statement.{u, v} :=
  @CaseStudies.ECRTS2005.Theorem6.SchedulabilityAnalysisEDF.Theorem6_05
