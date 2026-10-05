-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/arrival_curves.v

import Prosa.Util.Epsilon
import Prosa.Model.Priority.Classes
import Prosa.Model.Task.Arrival.Curves
import Prosa.Analysis.Facts.Model.TaskArrivals

namespace Prosa.Analysis.Facts.Model.ArrivalCurves

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Util.Notation
open Prosa.Util.Sum

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration] at *) <;> omega)

/-! Representation notes: `ε` is the numeral `1` (as the source notation);
`\sum_(tsk <- ts) F tsk` is `sumSeq ts F`, `\sum_(tsk <- ts | P tsk) F tsk`
is `sumFiltered ts P F`; `size [seq x <- s | P x]` is `(s.filter P).length`;
under an FP policy, `hep_job` is the accepted `FP_to_JLFP` coercion. -/

theorem non_pathological_max_arrivals {Task : TaskType} [DecidableEq Task] [MaxArrivals Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] (tsk : Task)
    (arr_seq : arrival_sequence Job) :
    respects_max_arrivals arr_seq tsk (max_arrivals tsk) →
      ∀ j : Job, job_of_task tsk j = true → arrives_in arr_seq j → 0 < max_arrivals tsk 1 := by
  intro hresp j hjt harr
  obtain ⟨t, ht⟩ := harr
  have hr := hresp t (t + 1) (by omega')
  rw [show t + 1 - t = 1 by omega'] at hr
  have hmem : j ∈ task_arrivals_between arr_seq tsk t (t + 1) := by
    unfold task_arrivals_between arrivals_between
    refine List.mem_filter.mpr ⟨?_, hjt⟩
    simp only [bigCat, show t + 1 - t = 1 by omega', List.range_one, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, Nat.add_zero]
    exact of_decide_eq_true ht
  have hpos : 0 < number_of_task_arrivals arr_seq tsk t (t + 1) := List.length_pos_of_mem hmem
  omega'

private theorem length_le_sum_partition {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (xs : List Job) (ts : List Task) (P : Job → Bool)
    (hcov : ∀ x, x ∈ xs → P x = true → job_task (Task := Task) x ∈ ts) :
    (xs.filter P).length ≤
      sumSeq ts (fun tsk => (xs.filter (fun x => P x && decide (job_task (Task := Task) x = tsk))).length) := by
  have h := sum_over_partitions_le (fun x => job_task (Task := Task) x) (fun _ => 1) P xs ts hcov
  have hl : sumFiltered xs P (fun _ => 1) = (xs.filter P).length := by
    simp [sumFiltered]
  rw [hl] at h
  refine Nat.le_trans h (le_of_eq ?_)
  unfold sumOverPartitions sumOfPartition
  congr 1
  funext tsk
  simp [sumFiltered]

private theorem sumSeq_mono_mem {I : Type _} (r : List I) (E1 E2 : I → Nat)
    (h : ∀ i, i ∈ r → E1 i ≤ E2 i) : sumSeq r E1 ≤ sumSeq r E2 := by
  induction r with
  | nil => simp [sumSeq]
  | cons a r ih =>
      simp only [sumSeq, List.map_cons, List.sum_cons] at ih ⊢
      exact Nat.add_le_add (h a List.mem_cons_self)
        (ih (fun i hi => h i (List.mem_cons_of_mem a hi)))

private theorem sumSeq_eq_sumFiltered {I : Type _} (r : List I) (Q : I → Bool) (g : I → Nat)
    (h : ∀ i, i ∈ r → Q i = false → g i = 0) : sumSeq r g = sumFiltered r Q g := by
  induction r with
  | nil => simp [sumSeq, sumFiltered]
  | cons a r ih =>
      have ih' := ih (fun i hi hq => h i (List.mem_cons_of_mem a hi) hq)
      simp only [sumSeq, sumFiltered, List.map_cons, List.sum_cons] at ih' ⊢
      cases hq : Q a with
      | false =>
          simp only [List.filter_cons, hq, Bool.false_eq_true, if_false]
          rw [h a List.mem_cons_self hq, Nat.zero_add]
          exact ih'
      | true =>
          simp only [List.filter_cons, hq, if_true, List.map_cons, List.sum_cons]
          rw [ih']

private theorem count_task_le_max {Task : TaskType} [DecidableEq Task] [MaxArrivals Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) (ts : List Task)
    (hresp : taskset_respects_max_arrivals arr_seq ts) (P : Job → Bool) (t1 : instant) (Δ : duration)
    (tsk : Task) (hin : tsk ∈ ts) :
    ((arrivals_between arr_seq t1 (t1 + Δ)).filter
        (fun x => P x && decide (job_task (Task := Task) x = tsk))).length ≤ max_arrivals tsk Δ := by
  have hr := hresp tsk (decide_eq_true hin) t1 (t1 + Δ) (by omega')
  rw [show t1 + Δ - t1 = Δ by omega'] at hr
  refine Nat.le_trans ?_ hr
  unfold number_of_task_arrivals task_arrivals_between
  apply List.Sublist.length_le
  apply List.monotone_filter_right
  intro x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  simp [job_of_task, hx.2]

theorem jlfp_hep_arrivals_bounded_by_sum_max_arrivals {Task : TaskType} [DecidableEq Task]
    [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JLFP_policy Job] (arr_seq : arrival_sequence Job) (ts : List Task) :
    all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
      ∀ (j : Job) (t1 : instant) (Δ : duration),
        ((arrivals_between arr_seq t1 (t1 + Δ)).filter (fun jhp => hep_job jhp j)).length ≤
          sumSeq ts (fun tsk => max_arrivals tsk Δ) := by
  intro hall hresp j t1 Δ
  have hcov : ∀ x, x ∈ arrivals_between arr_seq t1 (t1 + Δ) → (fun _ => true) x = true →
      job_task (Task := Task) x ∈ ts := fun x hx _ =>
    of_decide_eq_true (hall x (Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived
      arr_seq x t1 (t1 + Δ) (decide_eq_true hx)))
  have h1 := length_le_sum_partition (Task := Task) (arrivals_between arr_seq t1 (t1 + Δ)) ts
    (fun _ => true) hcov
  have h0 : ((arrivals_between arr_seq t1 (t1 + Δ)).filter (fun jhp => hep_job jhp j)).length ≤
      ((arrivals_between arr_seq t1 (t1 + Δ)).filter (fun _ => true)).length := by
    rw [List.filter_true]; exact List.length_filter_le _ _
  refine Nat.le_trans h0 (Nat.le_trans h1 ?_)
  exact sumSeq_mono_mem ts _ _ (fun tsk hin =>
    count_task_le_max arr_seq ts hresp (fun _ => true) t1 Δ tsk hin)

theorem fp_hep_arrivals_bounded_by_sum_max_arrivals {Task : TaskType} [DecidableEq Task]
    [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [FP : FP_policy Task] (arr_seq : arrival_sequence Job) (ts : List Task) :
    all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
      ∀ (j : Job) (t1 : instant) (Δ : duration),
        ((arrivals_between arr_seq t1 (t1 + Δ)).filter
            (fun jhp => @hep_job Job _ (FP_to_JLFP FP) jhp j)).length ≤
          sumFiltered ts (fun tsk => hep_task tsk (job_task (Task := Task) j))
            (fun tsk => max_arrivals tsk Δ) := by
  intro hall hresp j t1 Δ
  set P : Job → Bool := fun x => hep_task (job_task (Task := Task) x) (job_task (Task := Task) j) with hP
  have hcov : ∀ x, x ∈ arrivals_between arr_seq t1 (t1 + Δ) → P x = true →
      job_task (Task := Task) x ∈ ts := fun x hx _ =>
    of_decide_eq_true (hall x (Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived
      arr_seq x t1 (t1 + Δ) (decide_eq_true hx)))
  have h1 := length_le_sum_partition (Task := Task) (arrivals_between arr_seq t1 (t1 + Δ)) ts P hcov
  have hsplit := sumSeq_eq_sumFiltered ts (fun tsk => hep_task tsk (job_task (Task := Task) j))
    (fun tsk => ((arrivals_between arr_seq t1 (t1 + Δ)).filter
      (fun x => P x && decide (job_task (Task := Task) x = tsk))).length) (by
      intro tsk _ hq
      apply List.length_eq_zero_iff.mpr
      apply List.filter_eq_nil_iff.mpr
      intro x _ hx
      simp only [Bool.and_eq_true, decide_eq_true_eq, hP] at hx
      rw [hx.2] at hx
      simp [hq] at hx)
  change (List.filter P (arrivals_between arr_seq t1 (t1 + Δ))).length ≤ _
  refine Nat.le_trans h1 ?_
  rw [hsplit]
  exact leq_sum_seq ts _ _ _ (fun tsk hin _ =>
    count_task_le_max arr_seq ts hresp P t1 Δ tsk hin)

end Prosa.Analysis.Facts.Model.ArrivalCurves
