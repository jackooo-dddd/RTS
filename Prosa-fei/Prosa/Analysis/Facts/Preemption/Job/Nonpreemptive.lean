-- Translated from: ../rt-proofs/analysis/facts/preemption/job/nonpreemptive.v
import Prosa.Analysis.Facts.Behavior.All
import Prosa.Analysis.Facts.Model.Ideal_schedule
import Prosa.Analysis.Definitions.Job_properties
import Prosa.Model.Schedule.Nonpreemptive
import Prosa.Model.Preemption.Fully_nonpreemptive

namespace Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Service
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Processor.Ideal
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.Fully_nonpreemptive
open Prosa.Model.Schedule.Nonpreemptive
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Facts.Model.Ideal_schedule
open Prosa.Util.List
open Prosa.Util.Epsilon

section FullyNonPreemptiveModel

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobArrival Job]
variable [JobCost Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)

attribute [local instance] pstate_instance

variable (sched : schedule (processor_state Job))
variable (H_nonpreemptive_sched : nonpreemptive_schedule (Job := Job) sched)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

attribute [local instance] fully_nonpreemptive_model

include H_arrival_times_are_consistent H_nonpreemptive_sched
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute in
lemma valid_fully_nonpreemptive_model :
    valid_preemption_model arr_seq sched := by
  intro j _
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Sub-goal 1: job_cannot_become_nonpreemptive_before_execution
  · unfold job_cannot_become_nonpreemptive_before_execution
    simp [job_preemptable, fully_nonpreemptive_model]
  -- Sub-goal 2: job_cannot_be_nonpreemptive_after_completion
  · unfold job_cannot_be_nonpreemptive_after_completion
    simp [job_preemptable, fully_nonpreemptive_model]
  -- Sub-goal 3: not_preemptive_implies_scheduled
  · unfold not_preemptive_implies_scheduled
    intro t hnotpre
    simp only [job_preemptable, fully_nonpreemptive_model, Bool.or_eq_true, decide_eq_true_eq] at hnotpre
    push_neg at hnotpre
    obtain ⟨hne0, hnecost⟩ := hnotpre
    -- service > 0 and service ≠ cost, so not completed
    simp only [bne_iff_ne, ne_eq, beq_eq_decide, decide_eq_true_eq] at hne0 hnecost
    have hpos : 0 < service sched j t := Nat.pos_of_ne_zero hne0
    -- service < cost (not completed)
    have hlt : service sched j t < job_cost j := by
      rcases Nat.lt_or_ge (service sched j t) (job_cost j) with h | h
      · exact h
      · exfalso
        have hle := Prosa.Analysis.Facts.Behavior.Completion.service_at_most_cost sched H_completed_jobs_dont_execute j
              (ideal_proc_model_provides_unit_service) t
        exact absurd (Nat.le_antisymm hle h) hnecost
    -- Since service sched j t > 0 at time t, there exists ft < t with j scheduled at ft
    -- and service_during sched j 0 ft = 0 (first scheduling)
    have hincr := positive_service_during sched j 0 t hpos
    obtain ⟨ft, hft_ge, hft_lt, hft_sched, hft_serv⟩ := hincr
    -- Use nonpreemptive schedule: j scheduled at ft, not completed at t, ft ≤ t
    apply H_nonpreemptive_sched j ft t (Nat.le_of_lt hft_lt) hft_sched
    -- Show not completed at t
    intro hcomp
    unfold completed_by at hcomp
    simp only [work] at hcomp hlt
    omega
  -- Sub-goal 4: execution_starts_with_preemption_point
  · unfold execution_starts_with_preemption_point
    intro prt hnsched hsched
    simp only [job_preemptable, fully_nonpreemptive_model, Bool.or_eq_true, decide_eq_true_eq]
    -- Show service sched j (prt + 1) = 0, hence preemptable
    left
    by_contra hne0
    -- service sched j (prt + 1) > 0
    simp only [bne_iff_ne, ne_eq, beq_eq_decide, decide_eq_true_eq] at hne0
    have hpos : 0 < service sched j (prt + 1) := Nat.pos_of_ne_zero hne0
    -- There exists ft with j first scheduled and service up to ft is 0
    have hincr := positive_service_during sched j 0 (prt + 1) hpos
    obtain ⟨ft, hft_ge, hft_lt, hft_sched, hft_serv⟩ := hincr
    -- ft < prt + 1, so ft ≤ prt
    have hft_le_prt : ft ≤ prt := by omega
    -- j is scheduled at ft and we need to show j is not completed at prt
    -- First show j is not completed at prt + 1 + 1 (using the fact it's scheduled at prt+1)
    -- Actually, let's show j is not completed at prt
    -- j scheduled at prt+1 means service at prt+1 < cost (by completed_jobs_dont_execute)
    have hlt_cost : service sched j (prt + 1) < job_cost j :=
      H_completed_jobs_dont_execute j (prt + 1) hsched
    -- service at prt ≤ service at prt + 1 < cost, so not completed at prt
    have hnotcomp : ¬completed_by sched j prt := by
      unfold completed_by
      have hmon := Prosa.Analysis.Facts.Behavior.Service.service_monotonic sched j prt (prt + 1) (Nat.le_succ prt)
      simp only [work] at hmon hlt_cost ⊢
      omega
    -- By nonpreemptive: ft ≤ prt, scheduled at ft, not completed at prt => scheduled at prt
    have := H_nonpreemptive_sched j ft prt hft_le_prt hft_sched hnotcomp
    -- But j is not scheduled at prt (hnsched)
    exact hnsched this

lemma job_max_nps_is_job_cost :
    ∀ j : Job, job_max_nonpreemptive_segment j = job_cost j := by
  intro j
  unfold job_max_nonpreemptive_segment lengths_of_segments
  unfold job_preemption_points
  simp only [job_preemptable, fully_nonpreemptive_model]
  unfold Prosa.Model.Preemption.Parameter.distances range
  simp only [Nat.sub_zero]
  rcases Nat.eq_zero_or_pos (job_cost j) with hzero | hpos
  · -- job_cost j = 0
    rw [hzero]
    rfl
  · -- Show filter gives [0, job_cost j]
    set n := job_cost j with hn_def
    suffices hkey : (List.range' 0 (n + 1)).filter (fun ρ => ((ρ == 0) || (ρ == n))) = [0, n] by
      rw [hkey]
      -- distances [0, n] = [n - 0] = [n], max0 [n] = n
      show max0 (List.map (fun p => p.2 - p.1) (([0, n].zip ([0, n].drop 1)))) = n
      simp only [List.drop, List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil]
      show List.foldl Nat.max 0 [n - 0] = n
      simp only [List.foldl, Nat.zero_max, Nat.sub_zero]
    -- Split range' 0 (n+1) = 0 :: List.range' 1 n
    rw [List.range'_succ]
    simp only [List.filter_cons, beq_self_eq_true, Bool.true_or, ite_true, Nat.zero_add]
    congr 1
    -- Need: filter (fun ρ => (ρ == 0) || (ρ == n)) (List.range' 1 n) = [n]
    have hsimp : ∀ x ∈ List.range' 1 n, ((x == 0 : Bool) || (x == n : Bool)) = (x == n : Bool) := by
      intro x hx; rw [List.mem_range'] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have hne : ¬(1 + 1 * i = 0) := by omega
      rw [show (1 + 1 * i == 0 : Bool) = false from by exact beq_false_of_ne hne, Bool.false_or]
    rw [List.filter_congr hsimp]
    -- Need: filter (fun x => x == n) (List.range' 1 n) = [n]
    suffices h : ∀ m : ℕ, 0 < m → (List.range' 1 m).filter (fun x => x == m) = [m] from h n hpos
    intro m hm
    induction m with
    | zero => omega
    | succ k _ih =>
      rw [show List.range' 1 (k + 1) = List.range' 1 k ++ List.range' (1 + k) 1 from by
        rw [← List.range'_append]; ring_nf]
      have hfilt_nil : (List.range' 1 k).filter (fun x => x == k + 1) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx; rw [List.mem_range'] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        intro heq; rw [beq_iff_eq] at heq; omega
      have hk1_eq : (1 + k == k + 1 : Bool) = true := by rw [beq_iff_eq]; omega
      simp only [List.filter_append, List.range'_one, List.filter_cons, List.filter_nil,
                  hk1_eq, ite_true, hfilt_nil, List.nil_append]
      show [1 + k] = [k + 1]; congr 1; omega

lemma job_last_nps_is_job_cost :
    ∀ j : Job, job_last_nonpreemptive_segment j = job_cost j := by
  intro j
  unfold job_last_nonpreemptive_segment lengths_of_segments
  unfold job_preemption_points
  simp only [job_preemptable, fully_nonpreemptive_model]
  unfold Prosa.Model.Preemption.Parameter.distances range
  simp only [Nat.sub_zero]
  rcases Nat.eq_zero_or_pos (job_cost j) with hzero | hpos
  · -- job_cost j = 0
    rw [hzero]
    rfl
  · set n := job_cost j with hn_def
    suffices hkey : (List.range' 0 (n + 1)).filter (fun ρ => ((ρ == 0) || (ρ == n))) = [0, n] by
      rw [hkey]
      -- distances [0, n] = [n - 0] = [n], last0 [n] = n
      show last0 (List.map (fun p => p.2 - p.1) (([0, n].zip ([0, n].drop 1)))) = n
      simp only [List.drop, List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil]
      show last0 [n - 0] = n
      unfold last0
      simp only [List.getLastD, Nat.sub_zero]
      rfl
    rw [List.range'_succ]
    simp only [List.filter_cons, beq_self_eq_true, Bool.true_or, ite_true, Nat.zero_add]
    congr 1
    have hsimp : ∀ x ∈ List.range' 1 n, ((x == 0 : Bool) || (x == n : Bool)) = (x == n : Bool) := by
      intro x hx; rw [List.mem_range'] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have hne : ¬(1 + 1 * i = 0) := by omega
      rw [show (1 + 1 * i == 0 : Bool) = false from by exact beq_false_of_ne hne, Bool.false_or]
    rw [List.filter_congr hsimp]
    -- Need: filter (fun x => x == n) (List.range' 1 n) = [n]
    suffices h : ∀ m : ℕ, 0 < m → (List.range' 1 m).filter (fun x => x == m) = [m] from h n hpos
    intro m hm
    induction m with
    | zero => omega
    | succ k _ih =>
      rw [show List.range' 1 (k + 1) = List.range' 1 k ++ List.range' (1 + k) 1 from by
        rw [← List.range'_append]; ring_nf]
      have hfilt_nil : (List.range' 1 k).filter (fun x => x == k + 1) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx; rw [List.mem_range'] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        intro heq; rw [beq_iff_eq] at heq; omega
      have hk1_eq : (1 + k == k + 1 : Bool) = true := by rw [beq_iff_eq]; omega
      simp only [List.filter_append, List.range'_one, List.filter_cons, List.filter_nil,
                  hk1_eq, ite_true, hfilt_nil, List.nil_append]
      show [1 + k] = [k + 1]; congr 1; omega

end FullyNonPreemptiveModel

end Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive
