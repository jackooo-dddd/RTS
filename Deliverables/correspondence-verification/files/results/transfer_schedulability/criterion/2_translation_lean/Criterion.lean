-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/transfer_schedulability/criterion.v

import Prosa.Util.All
import Prosa.Analysis.Facts.Model.ServiceOfJobs
import Prosa.Analysis.Definitions.Schedulability
import Prosa.Analysis.Facts.Model.Ideal.Schedule
import Prosa.Analysis.Facts.Model.Uniprocessor

namespace Prosa.Results.TransferSchedulability.Criterion

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.Model.Uniprocessor
open Prosa.Util.Sum

/-! Transfer schedulability for ideal uniprocessors.

Binders follow the elaborated source types. The processor model is the ideal
uniprocessor `processor_state Job` (the source's section-local
`#[local] Existing Instance ideal.processor_state` and `Let PState`). The
source's `Let` abbreviations `ref_completed_by`, `online_completed_by`,
`ref_job_meets_deadline`, `online_job_meets_deadline` and
`online_remaining_cost` are inlined with the corresponding job-cost parameter
passed explicitly; several job-cost parameters are in scope, so every use of a
cost-dependent notion names its cost explicitly.

Representation: `\sum_(j <- js) F j` is `sumSeq js F`; `[seq j <- xs | p j]`
is `xs.filter p`; `j \in xs` is `decide (j ∈ xs) = true`; `uniq xs` is
`xs.Nodup`; `~~ b` is `!b`; `t.+1` is `t + 1`; `t.-1` is `t - 1`;
`[forall delta : 'I_n, p delta]` is `(List.range' 0 n).all p`; `xpredT` is
`fun _ => true`; `{in xs, forall j, P j}` is `∀ j, j ∈ xs → P j`; a Boolean
in `Prop` is `b = true`. -/

section Helpers

private theorem sumSeq_nil {I : Type _} (F : I → Nat) : sumSeq [] F = 0 := rfl

private theorem sumSeq_cons {I : Type _} (x : I) (l : List I) (F : I → Nat) :
    sumSeq (x :: l) F = F x + sumSeq l F := by
  simp [sumSeq]

private theorem sumSeq_add {I : Type _} (l : List I) (f g : I → Nat) :
    sumSeq l (fun x => f x + g x) = sumSeq l f + sumSeq l g := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [sumSeq_cons, ih]; omega'

private theorem sumSeq_congr {I : Type _} (l : List I) (f g : I → Nat)
    (h : ∀ x, x ∈ l → f x = g x) : sumSeq l f = sumSeq l g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [sumSeq_cons, sumSeq_cons, h x (List.mem_cons_self ..),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem sumSeq_le {I : Type _} (l : List I) (f g : I → Nat)
    (h : ∀ x, x ∈ l → f x ≤ g x) : sumSeq l f ≤ sumSeq l g := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    rw [sumSeq_cons, sumSeq_cons]
    exact Nat.add_le_add (h x (List.mem_cons_self ..))
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

private theorem sumSeq_sublist {I : Type _} {l1 l2 : List I} (hs : l1.Sublist l2)
    (f : I → Nat) : sumSeq l1 f ≤ sumSeq l2 f := by
  induction hs with
  | slnil => exact Nat.le_refl _
  | cons x _ ih => rw [sumSeq_cons]; omega'
  | cons_cons x _ ih => rw [sumSeq_cons, sumSeq_cons]; omega'

private theorem sumSeq_mem_le {I : Type _} (l : List I) (f : I → Nat) (x : I)
    (hx : x ∈ l) : f x ≤ sumSeq l f := by
  induction l with
  | nil => cases hx
  | cons y l ih =>
    rw [sumSeq_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; omega'
    · have := ih h; omega'

private theorem sumSeq_eq_zero {I : Type _} (l : List I) (f : I → Nat)
    (h : sumSeq l f = 0) : ∀ x, x ∈ l → f x = 0 := by
  intro x hx
  have := sumSeq_mem_le l f x hx
  omega'

private theorem sumSeq_zero {I : Type _} (l : List I) (f : I → Nat)
    (h : ∀ x, x ∈ l → f x = 0) : sumSeq l f = 0 := by
  rw [sumSeq_congr l f (fun _ => 0) h]
  induction l with
  | nil => rfl
  | cons x l ih => rw [sumSeq_cons, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem sumSeq_pos {I : Type _} (l : List I) (f : I → Nat)
    (h : 0 < sumSeq l f) : ∃ x, x ∈ l ∧ 0 < f x := by
  induction l with
  | nil => simp [sumSeq_nil] at h
  | cons y l ih =>
    rw [sumSeq_cons] at h
    by_cases hy : 0 < f y
    · exact ⟨y, List.mem_cons_self .., hy⟩
    · obtain ⟨x, hx, hpos⟩ := ih (by omega')
      exact ⟨x, List.mem_cons_of_mem _ hx, hpos⟩

/-- Dropping elements whose terms vanish does not change the sum. -/
private theorem sumSeq_filter_of_zero {I : Type _} (l : List I) (p : I → Bool) (f : I → Nat)
    (h : ∀ x, x ∈ l → p x = false → f x = 0) : sumSeq (l.filter p) f = sumSeq l f := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    by_cases hp : p y = true
    · rw [List.filter_cons_of_pos hp, sumSeq_cons, sumSeq_cons, ih']
    · have hpf : p y = false := by simpa using hp
      rw [List.filter_cons_of_neg (by simpa using hpf), sumSeq_cons, ih',
        h y (List.mem_cons_self ..) hpf, Nat.zero_add]

private theorem filter_sublist_filter_of_imp {I : Type _} (l : List I) (p q : I → Bool)
    (h : ∀ x, p x = true → q x = true) : (l.filter p).Sublist (l.filter q) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons y l ih =>
    by_cases hp : p y = true
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (h y hp)]
      exact ih.cons_cons y
    · rw [List.filter_cons_of_neg hp]
      by_cases hq : q y = true
      · rw [List.filter_cons_of_pos hq]; exact ih.cons y
      · rw [List.filter_cons_of_neg hq]; exact ih

/-- On a duplicate-free sequence containing `x`, the sum splits off `x`. -/
private theorem sumSeq_split_mem {I : Type _} [DecidableEq I] (l : List I) (f : I → Nat)
    (x : I) (hnd : l.Nodup) (hx : x ∈ l) :
    sumSeq l f = f x + sumSeq (l.filter (fun y => decide (y ≠ x))) f := by
  induction l with
  | nil => cases hx
  | cons y l ih =>
    have hnd' := (List.nodup_cons.mp hnd)
    rcases List.mem_cons.mp hx with h | h
    · subst h
      have hall : l.filter (fun y => decide (y ≠ x)) = l := by
        rw [List.filter_eq_self]
        intro a ha
        simp only [decide_eq_true_eq]
        intro hax; subst hax; exact hnd'.1 ha
      rw [List.filter_cons_of_neg (by simp), hall, sumSeq_cons]
    · have hyx : y ≠ x := by intro hyx; subst hyx; exact hnd'.1 h
      rw [List.filter_cons_of_pos (by simpa using hyx), sumSeq_cons, sumSeq_cons, ih hnd'.2 h]
      omega'

private theorem all_range'_iff (n : Nat) (p : Nat → Bool) :
    (List.range' 0 n).all p = true ↔ ∀ d, d < n → p d = true := by
  rw [List.all_eq_true]
  constructor
  · intro h d hd
    exact h d (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega'⟩)
  · intro h d hd
    have := List.mem_range'_1.mp hd
    exact h d (by omega')

end Helpers

section TransferSchedulability

variable {Job : JobType} [DecidableEq Job]

/-- No job finishes later in the online schedule than in the reference schedule. -/
def schedulability_transferred (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) : Prop :=
  ∀ (j : Job) (t : instant), @completed_by Job _ _ ref_sched ref_job_cost j t = true →
    @completed_by Job _ _ online_sched online_job_cost j t = true

/-- Schedulability transfer extends to deadlines. -/
theorem deadlines_met [JobDeadline Job] (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) :
    schedulability_transferred ref_sched online_sched ref_job_cost online_job_cost →
    ∀ j : Job, @job_meets_deadline Job _ _ ref_sched ref_job_cost _ j = true →
      @job_meets_deadline Job _ _ online_sched online_job_cost _ j = true := by
  intro htrans j hmet
  exact htrans j _ hmet

/-- By transitivity, the reference cost bounds the online cost. -/
theorem ref_cost_bounds_online_cost (ref_job_cost online_job_cost job_cost_bound : JobCost Job) :
    (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
    (∀ j : Job, @job_cost Job _ job_cost_bound j ≤ @job_cost Job _ ref_job_cost j) →
    ∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ ref_job_cost j :=
  fun h1 h2 j => Nat.le_trans (h1 j) (h2 j)

/-- The remaining job-cost bound. -/
noncomputable def remaining_cost_bound (online_sched : schedule (processor_state Job))
    (job_cost_bound : JobCost Job) (j : Job) (t : instant) : Nat :=
  @job_cost Job _ job_cost_bound j - service online_sched j t

private theorem online_service_le_bound (online_sched : schedule (processor_state Job))
    (online_job_cost : JobCost Job)
    (hcde : @completed_jobs_dont_execute Job _ _ online_sched online_job_cost)
    (job_cost_bound : JobCost Job)
    (hb : ∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j)
    (j : Job) (t : instant) : service online_sched j t ≤ @job_cost Job _ job_cost_bound j :=
  Nat.le_trans (@service_at_most_cost Job _ online_job_cost _ online_sched hcde j
    (ideal_proc_model_provides_unit_service Job) t) (hb j)

/-- The remaining cost bound splits into the next instant's and the service now. -/
theorem remcost_service (online_sched : schedule (processor_state Job))
    (online_job_cost : JobCost Job) :
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      ∀ (j : Job) (t : instant),
        remaining_cost_bound online_sched job_cost_bound j t =
          remaining_cost_bound online_sched job_cost_bound j (t + 1) + service_at online_sched j t := by
  intro hcde job_cost_bound hb j t
  have h1 := online_service_le_bound online_sched online_job_cost hcde job_cost_bound hb j (t + 1)
  have h2 := service_last_plus_before online_sched j t
  unfold remaining_cost_bound
  omega'

/-- The same split over an interval. -/
theorem remcost_service_during (online_sched : schedule (processor_state Job))
    (online_job_cost : JobCost Job) :
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      ∀ (j : Job) (t1 t2 : Nat), t1 ≤ t2 →
        remaining_cost_bound online_sched job_cost_bound j t1 =
          remaining_cost_bound online_sched job_cost_bound j t2 +
            service_during online_sched j t1 t2 := by
  intro hcde job_cost_bound hb j t1 t2 hle
  have h1 := online_service_le_bound online_sched online_job_cost hcde job_cost_bound hb j t2
  have h2 := service_cat online_sched j t1 t2 hle
  unfold remaining_cost_bound
  omega'

/-- The interval split lifted to a set of jobs. -/
theorem remcost_total_service_during (online_sched : schedule (processor_state Job))
    (online_job_cost : JobCost Job) :
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      ∀ (js : List Job) (t1 t2 : Nat), t1 ≤ t2 →
        sumSeq js (fun j => remaining_cost_bound online_sched job_cost_bound j t1) =
          sumSeq js (fun j => remaining_cost_bound online_sched job_cost_bound j t2) +
            service_of_jobs online_sched (fun _ => true) js t1 t2 := by
  intro hcde job_cost_bound hb js t1 t2 hle
  have hsoj : service_of_jobs online_sched (fun _ => true) js t1 t2 =
      sumSeq js (fun j => service_during online_sched j t1 t2) := by
    unfold service_of_jobs sumFiltered
    rw [List.filter_true]; rfl
  rw [hsoj, ← sumSeq_add]
  exact sumSeq_congr _ _ _ (fun j _ =>
    remcost_service_during online_sched online_job_cost hcde job_cost_bound hb j t1 t2 hle)

/-- If some job of the set is always scheduled, the remaining cost bound drops
by the interval length. -/
theorem remaining_cost_invariant (online_sched : schedule (processor_state Job))
    (online_job_cost : JobCost Job) :
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      ∀ (js : List Job) (t1 t2 : Nat), t1 ≤ t2 → js.Nodup →
        (∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true →
          ∃ j : Job, (decide (j ∈ js) && scheduled_at online_sched j t) = true) →
        sumSeq js (fun j => remaining_cost_bound online_sched job_cost_bound j t1) =
          sumSeq js (fun j => remaining_cost_bound online_sched job_cost_bound j t2) + (t2 - t1) := by
  intro hcde job_cost_bound hb js t1 t2 hle hnd hsched
  rw [remcost_total_service_during online_sched online_job_cost hcde job_cost_bound hb js t1 t2 hle]
  congr 1
  apply service_of_jobs_always_scheduled (ideal_proc_model_provides_unit_service Job)
    (ideal_proc_model_is_a_uniprocessor_model Job) online_sched _
    (ideal_proc_model_ensures_ideal_progress Job) js hnd
  intro t ht
  obtain ⟨j, hj⟩ := hsched t ht
  simp only [Bool.and_eq_true] at hj
  exact ⟨j, hj.1, hj.2, rfl⟩

/-- The remaining cost bound bounds the true remaining online cost. -/
theorem online_remaining_cost_bounded (online_sched : schedule (processor_state Job))
    (online_job_cost : JobCost Job) :
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      ∀ (j : Job) (t : instant),
        @remaining_cost Job _ _ online_sched online_job_cost j t ≤
          remaining_cost_bound online_sched job_cost_bound j t := by
  intro _ job_cost_bound hb j t
  have := hb j
  unfold remaining_cost remaining_cost_bound
  omega'

/-- An incomplete job has a positive remaining cost bound. -/
theorem remaining_cost_positive (online_sched : schedule (processor_state Job))
    (online_job_cost job_cost_bound : JobCost Job) :
    (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
    ∀ (j : Job) (t : instant),
      (!@completed_by Job _ _ online_sched online_job_cost j t) = true →
      0 < remaining_cost_bound online_sched job_cost_bound j t := by
  intro hb j t hnc
  have := hb j
  simp only [completed_by, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at hnc
  unfold remaining_cost_bound
  omega'

/-- A zero total remaining cost bound means every job of the set is complete. -/
theorem remaining_cost_zero (online_sched : schedule (processor_state Job))
    (online_job_cost : JobCost Job) :
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      ∀ (js : List Job) (t : instant),
        decide (sumSeq js (fun j => remaining_cost_bound online_sched job_cost_bound j t) = 0) = true →
        ∀ j : Job, decide (j ∈ js) = true → @completed_by Job _ _ online_sched online_job_cost j t = true := by
  intro _ job_cost_bound hb js t hz j hj
  have h0 := sumSeq_eq_zero js _ (of_decide_eq_true hz) j (of_decide_eq_true hj)
  have := hb j
  unfold remaining_cost_bound at h0
  unfold completed_by
  exact decide_eq_true (by omega')

/-- The critical jobs at `t1` w.r.t. reference time `t2`. -/
noncomputable def critical_jobs (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job)
    (t1 t2 : instant) : List Job :=
  (arrivals_up_to arr_seq t2).filter (fun j =>
    @completed_by Job _ _ ref_sched ref_job_cost j t2 &&
      !@completed_by Job _ _ online_sched online_job_cost j t1)

private theorem mem_critical_jobs (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job)
    (t1 t2 : instant) (j : Job) :
    j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2 ↔
      j ∈ arrivals_up_to arr_seq t2 ∧ @completed_by Job _ _ ref_sched ref_job_cost j t2 = true ∧
        @completed_by Job _ _ online_sched online_job_cost j t1 = false := by
  unfold critical_jobs
  simp [List.mem_filter, Bool.and_eq_true]

/-- Criticality is monotone towards earlier times. -/
theorem critical_jobs_monotonicity (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) (t1 t2 t3 : Nat) :
    (decide (t1 ≤ t2) && decide (t2 ≤ t3)) = true →
    ∀ j : Job,
      decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t2 t3) = true →
      decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t3) = true := by
  intro hle j hj
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hle
  rw [decide_eq_true_eq, mem_critical_jobs] at hj ⊢
  refine ⟨hj.1, hj.2.1, ?_⟩
  have := @incompletion_monotonic Job _ online_job_cost _ online_sched j t1 t2 hle.1
    (by rw [hj.2.2]; rfl)
  simpa using this

/-- A job that stops being critical has completed. -/
theorem critical_jobs_dropout (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) (t1 t2 t3 : Nat) :
    (decide (t1 ≤ t2) && decide (t2 ≤ t3)) = true →
    ∀ j : Job,
      decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t3) = true →
      (!decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t2 t3)) = true →
      @completed_by Job _ _ online_sched online_job_cost j t2 = true := by
  intro _ j hj hn
  rw [decide_eq_true_eq, mem_critical_jobs] at hj
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, mem_critical_jobs, not_and] at hn
  cases hc : @completed_by Job _ _ online_sched online_job_cost j t2
  · exact absurd hc (hn hj.1 hj.2.1)
  · rfl

/-- The later critical jobs are the earlier ones that are still incomplete. -/
theorem critical_jobs_filter_complete (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) (t1 t2 : Nat)
    (t3 : instant) :
    t1 ≤ t2 →
    critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t2 t3 =
      (critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t3).filter
        (fun j => !@completed_by Job _ _ online_sched online_job_cost j t2) := by
  intro hle
  unfold critical_jobs
  rw [List.filter_filter]
  apply List.filter_congr
  intro j _
  cases h3 : @completed_by Job _ _ ref_sched ref_job_cost j t3 <;>
    cases h2 : @completed_by Job _ _ online_sched online_job_cost j t2 <;>
    cases h1 : @completed_by Job _ _ online_sched online_job_cost j t1 <;> simp
  have := @completion_monotonic Job _ online_job_cost _ online_sched j t1 t2 hle h1
  rw [h2] at this
  exact Bool.false_ne_true this

/-- The critical jobs form a set. -/
theorem critical_jobs_uniq [JobArrival Job] (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ t1 t2 : instant,
      (critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2).Nodup := by
  intro hva t1 t2
  exact (arrivals_uniq arr_seq hva.1 hva.2 0 (t2 + 1)).filter _

/-- The critical jobs at time zero need at least their bounded cost to complete. -/
theorem critical_jobs_min_completion_time [JobArrival Job]
    (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    @completed_jobs_dont_execute Job _ _ ref_sched ref_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ job_cost_bound j ≤ @job_cost Job _ ref_job_cost j) →
      ∀ t : instant,
        sumSeq (critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq 0 t)
          (fun j => @job_cost Job _ job_cost_bound j) ≤ t := by
  intro hva hcde job_cost_bound hb t
  set cj := critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq 0 t
  have h1 : sumSeq cj (fun j => @job_cost Job _ job_cost_bound j) ≤
      sumSeq cj (fun j => service_during ref_sched j 0 t) := by
    apply sumSeq_le
    intro j hj
    rw [mem_critical_jobs] at hj
    have hc := hj.2.1
    unfold completed_by at hc
    have := of_decide_eq_true hc
    exact Nat.le_trans (hb j) this
  have h2 : sumSeq cj (fun j => service_during ref_sched j 0 t) =
      service_of_jobs ref_sched (fun _ => true) cj 0 t := by
    unfold service_of_jobs sumFiltered
    rw [List.filter_true]; rfl
  have h3 := service_of_jobs_le_length_of_interval' (ideal_proc_model_provides_unit_service Job)
    (ideal_proc_model_is_a_uniprocessor_model Job) ref_sched (fun _ => true) cj
    (critical_jobs_uniq ref_sched online_sched ref_job_cost online_job_cost arr_seq hva 0 t) 0 t
  omega'

/-- The total remaining cost bound of critical jobs is monotonically decreasing. -/
theorem critical_jobs_remaining_cost_monotonic (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      ∀ t1 t2 t3 : Nat, (decide (t1 ≤ t2) && decide (t2 ≤ t3)) = true →
        sumSeq (critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t2 t3)
            (fun j => remaining_cost_bound online_sched job_cost_bound j t2) ≤
          sumSeq (critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t3)
            (fun j => remaining_cost_bound online_sched job_cost_bound j t1) := by
  intro _ job_cost_bound _ t1 t2 t3 hle
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hle
  rw [critical_jobs_filter_complete ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2 t3 hle.1]
  refine Nat.le_trans (sumSeq_sublist (List.filter_sublist) _) (sumSeq_le _ _ _ ?_)
  intro j _
  have := service_monotonic online_sched j t1 t2 hle.1
  unfold remaining_cost_bound
  omega'

/-- A slackless interval. -/
noncomputable def slackless_interval (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job)
    (job_cost_bound : JobCost Job) (t1 t2 : Nat) : Bool :=
  decide (t1 < t2) &&
    decide (sumSeq (critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2)
      (fun j => remaining_cost_bound online_sched job_cost_bound j t1) = t2 - t1)

/-- A contiguously slackless interval. -/
noncomputable def contiguously_slackless_interval (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job)
    (job_cost_bound : JobCost Job) (t1 t2 : Nat) : Bool :=
  slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 &&
    (List.range' 0 (t2 - t1)).all (fun delta =>
      slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
        (t1 + delta) t2)

/-- The transfer schedulability criterion. -/
def transfer_schedulability_criterion (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job)
    (job_cost_bound : JobCost Job) : Prop :=
  ∀ t1 t2 : Nat,
    slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 = true →
    ∃ j : Job, (scheduled_at online_sched j t1 &&
      decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2)) = true

/-- A late job is critical. -/
theorem late_in_critical_jobs [JobArrival Job] (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    jobs_come_from_arrival_sequence ref_sched arr_seq →
    jobs_must_arrive_to_execute ref_sched →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      (∀ j : Job, @job_cost Job _ job_cost_bound j ≤ @job_cost Job _ ref_job_cost j) →
      ∀ (j : Job) (t : instant),
        @completed_by Job _ _ ref_sched ref_job_cost j t = true →
        (!@completed_by Job _ _ online_sched online_job_cost j t) = true →
        decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t t) = true := by
  intro hva hfrom harr job_cost_bound hb hd j t hc hnc
  have hbo := hb j
  have hdo := hd j
  simp only [Bool.not_eq_true', completed_by, decide_eq_false_iff_not, Nat.not_le] at hnc
  have hc' := of_decide_eq_true (show decide _ = true from hc)
  rw [decide_eq_true_eq, mem_critical_jobs]
  refine ⟨?_, hc, by simp [completed_by]; omega'⟩
  have hpos : 0 < service ref_sched j t := by omega'
  obtain ⟨t', ht', hs⟩ := positive_service_implies_scheduled_since_arrival ref_sched j harr t hpos
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
  have hin := job_in_arrivals_between arr_seq hva.1 j 0 (t + 1) (hfrom j t' hs) (Nat.zero_le _)
    (by omega')
  exact of_decide_eq_true hin

/-- No job is late at time zero. -/
theorem late_not_at_start (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost job_cost_bound : JobCost Job) :
    (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
    (∀ j : Job, @job_cost Job _ job_cost_bound j ≤ @job_cost Job _ ref_job_cost j) →
    ∀ (j : Job) (t : instant),
      @completed_by Job _ _ ref_sched ref_job_cost j t = true →
      (!@completed_by Job _ _ online_sched online_job_cost j t) = true → 0 < t := by
  intro hb hd j t hc hnc
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · subst h0
    have hbo := hb j
    have hdo := hd j
    simp only [completed_by, service0, decide_eq_true_eq] at hc
    simp only [completed_by, service0, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at hnc
    omega'
  · exact hpos

/-- An interval with non-positive slack. -/
noncomputable def nonpositive_slack (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job)
    (job_cost_bound : JobCost Job) (t1 t2 : Nat) : Bool :=
  decide (t2 - t1 ≤
    sumSeq (critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2)
      (fun j => remaining_cost_bound online_sched job_cost_bound j t1))

/-- An interval all of whose suffixes have non-positive slack. -/
noncomputable def contiguously_nps (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job)
    (job_cost_bound : JobCost Job) (t1 t2 : Nat) : Bool :=
  (List.range' 0 (t2 - t1)).all (fun delta =>
    nonpositive_slack ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
      (t1 + delta) t2)

/-- Before a maximal contiguously non-positive slack interval the slack is positive. -/
theorem contiguously_nps_start (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job)
    (job_cost_bound : JobCost Job) (t0 t2 : Nat) :
    (!contiguously_nps ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t0 t2) = true →
    contiguously_nps ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound (t0 + 1) t2 = true →
    (!nonpositive_slack ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t0 t2) = true := by
  intro hn hc
  unfold contiguously_nps at hn hc
  rw [all_range'_iff] at hc
  rw [Bool.not_eq_true'] at hn ⊢
  rcases Bool.eq_false_or_eq_true
      (nonpositive_slack ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t0 t2)
    with h | h
  · exfalso
    have hall : (List.range' 0 (t2 - t0)).all (fun delta =>
        nonpositive_slack ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
          (t0 + delta) t2) = true := by
      rw [all_range'_iff]
      intro d hd
      rcases d with _ | d
      · simpa using h
      · have := hc d (by omega')
        rwa [show t0 + 1 + d = t0 + (d + 1) by omega'] at this
    rw [hn] at hall
    exact Bool.false_ne_true hall
  · exact h

/-- A late job is preceded by a contiguously non-positive slack interval that
starts at zero or after an interval with positive slack. -/
theorem contiguously_nps_existence [JobArrival Job] (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    jobs_come_from_arrival_sequence ref_sched arr_seq →
    jobs_must_arrive_to_execute ref_sched →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      (∀ j : Job, @job_cost Job _ job_cost_bound j ≤ @job_cost Job _ ref_job_cost j) →
      ∀ (j : Job) (t2 : instant),
        @completed_by Job _ _ ref_sched ref_job_cost j t2 = true →
        (!@completed_by Job _ _ online_sched online_job_cost j t2) = true →
        ∃ t1 : Nat,
          contiguously_nps ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 = true ∧
          t1 < t2 ∧
          (t1 = 0 ∨
            (!nonpositive_slack ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
              (t1 - 1) t2) = true) := by
  intro hva hfrom harr job_cost_bound hb hd j t2 hc hnc
  have hpos := late_not_at_start ref_sched online_sched ref_job_cost online_job_cost job_cost_bound hb hd j t2 hc hnc
  have hin2 := late_in_critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq hva hfrom harr
    job_cost_bound hb hd j t2 hc hnc
  have NPS2 : nonpositive_slack ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
      (t2 - 1) t2 = true := by
    unfold nonpositive_slack
    apply decide_eq_true
    have hmem := critical_jobs_monotonicity ref_sched online_sched ref_job_cost online_job_cost arr_seq
      (t2 - 1) t2 t2 (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') j hin2
    have hle := sumSeq_mem_le _ (fun j => remaining_cost_bound online_sched job_cost_bound j (t2 - 1)) j
      (of_decide_eq_true hmem)
    have hinc := @incompletion_monotonic Job _ online_job_cost _ online_sched j (t2 - 1) t2 (by omega') hnc
    have hp := remaining_cost_positive online_sched online_job_cost job_cost_bound hb j (t2 - 1) hinc
    omega'
  have CNPS2 : contiguously_nps ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
      (t2 - 1) t2 = true := by
    unfold contiguously_nps
    rw [all_range'_iff]
    intro d hd
    rw [show t2 - 1 + d = t2 - 1 by omega']
    exact NPS2
  have hex : ∃ t, contiguously_nps ref_sched online_sched ref_job_cost online_job_cost arr_seq
      job_cost_bound t t2 = true := ⟨t2 - 1, CNPS2⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, ?_⟩
  · have := Nat.find_min' hex CNPS2
    omega'
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hp0
    · exact Or.inl h0
    · right
      obtain ⟨t0, ht0⟩ : ∃ t0, Nat.find hex = t0 + 1 := ⟨Nat.find hex - 1, by omega'⟩
      have hmin := Nat.find_min hex (show t0 < Nat.find hex by omega')
      rw [ht0, Nat.add_sub_cancel]
      apply contiguously_nps_start ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t0 t2
      · simpa using hmin
      · rw [← ht0]; exact Nat.find_spec hex

private theorem slackless_parts (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job)
    (job_cost_bound : JobCost Job) (t1 t2 : Nat) :
    slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 = true ↔
      t1 < t2 ∧ sumSeq (critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2)
        (fun j => remaining_cost_bound online_sched job_cost_bound j t1) = t2 - t1 := by
  unfold slackless_interval
  simp [Bool.and_eq_true]

/-- A job other than the one scheduled at `t1` that is incomplete at `t1`
remains incomplete at `t1 + 1` and keeps its remaining cost bound. -/
private theorem other_job_unchanged (online_sched : schedule (processor_state Job))
    (online_job_cost : JobCost Job)
    (hcde : @completed_jobs_dont_execute Job _ _ online_sched online_job_cost)
    (job_cost_bound : JobCost Job)
    (hb : ∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j)
    (j j' : Job) (t1 : Nat) (hs : scheduled_at online_sched j t1 = true) (hne : j ≠ j') :
    remaining_cost_bound online_sched job_cost_bound j' (t1 + 1) =
        remaining_cost_bound online_sched job_cost_bound j' t1 ∧
      ((!@completed_by Job _ _ online_sched online_job_cost j' t1) = true →
        (!@completed_by Job _ _ online_sched online_job_cost j' (t1 + 1)) = true) := by
  have hns := scheduled_job_at_neq (ideal_proc_model_is_a_uniprocessor_model Job) online_sched j j' t1
    (by simpa using hne) hs
  have hsa : service_at online_sched j' t1 = 0 := by
    rw [service_at_is_scheduled_at]
    simp only [Bool.not_eq_true'] at hns
    rw [hns]; rfl
  refine ⟨?_, fun hinc => @not_scheduled_remains_incomplete Job _ online_job_cost _ online_sched j' t1 hinc hns⟩
  have := remcost_service online_sched online_job_cost hcde job_cost_bound hb j' t1
  omega'

/-- Case 1 helper: a critical job that completes has a zero remaining cost bound. -/
theorem slackless_interval_step_case_completed_job_rem [JobArrival Job]
    (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      ∀ t1 t2 : Nat,
        slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 = true →
        nonpositive_slack ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound (t1 + 1) t2 = true →
        ∀ j : Job, scheduled_at online_sched j t1 = true →
          decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2) = true →
          @completed_by Job _ _ online_sched online_job_cost j (t1 + 1) = true →
          remaining_cost_bound online_sched job_cost_bound j (t1 + 1) = 0 := by
  intro hva hcde job_cost_bound hb t1 t2 hsl hnps j hs hin hcomp
  rw [slackless_parts] at hsl
  obtain ⟨hlt, hzs⟩ := hsl
  set S := critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2
  have hnd : S.Nodup := critical_jobs_uniq ref_sched online_sched ref_job_cost online_job_cost arr_seq hva t1 t2
  have hjS : j ∈ S := of_decide_eq_true hin
  by_contra hpos
  have hpos' : 0 < remaining_cost_bound online_sched job_cost_bound j (t1 + 1) := by omega'
  unfold nonpositive_slack at hnps
  have hnps' := of_decide_eq_true hnps
  rw [critical_jobs_filter_complete ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 (t1 + 1) t2
    (by omega')] at hnps'
  change t2 - (t1 + 1) ≤ sumSeq (S.filter _) _ at hnps'
  -- the surviving jobs are the other ones, which keep their bound
  have hsub : (S.filter (fun j' => !@completed_by Job _ _ online_sched online_job_cost j' (t1 + 1))).Sublist
      (S.filter (fun y => decide (y ≠ j))) := by
    apply filter_sublist_filter_of_imp
    intro y hy
    simp only [Bool.not_eq_true'] at hy
    simp only [decide_eq_true_eq]
    intro hyj; subst hyj; rw [hcomp] at hy; exact Bool.false_ne_true hy.symm
  have hle1 := sumSeq_sublist hsub (fun j => remaining_cost_bound online_sched job_cost_bound j (t1 + 1))
  have heq2 : sumSeq (S.filter (fun y => decide (y ≠ j)))
        (fun j => remaining_cost_bound online_sched job_cost_bound j (t1 + 1)) =
      sumSeq (S.filter (fun y => decide (y ≠ j)))
        (fun j => remaining_cost_bound online_sched job_cost_bound j t1) := by
    apply sumSeq_congr
    intro y hy
    rw [List.mem_filter] at hy
    exact (other_job_unchanged online_sched online_job_cost hcde job_cost_bound hb j y t1 hs
      (by intro h; subst h; simp at hy)).1
  have hsplit := sumSeq_split_mem S (fun j => remaining_cost_bound online_sched job_cost_bound j t1) j hnd hjS
  have hrj := remcost_service online_sched online_job_cost hcde job_cost_bound hb j t1
  have hsa : service_at online_sched j t1 = 1 := by
    rw [service_at_is_scheduled_at, hs]; rfl
  omega'

/-- Case 1: the critical job scheduled at `t1` completes. -/
theorem slackless_interval_step_case_completed_job [JobArrival Job]
    (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      ∀ t1 t2 : Nat,
        slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 = true →
        t1 + 1 < t2 →
        nonpositive_slack ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound (t1 + 1) t2 = true →
        ∀ j : Job, scheduled_at online_sched j t1 = true →
          decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2) = true →
          @completed_by Job _ _ online_sched online_job_cost j (t1 + 1) = true →
          slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
            (t1 + 1) t2 = true := by
  intro hva hcde job_cost_bound hb t1 t2 hsl hlt hnps j hs hin hcomp
  have hz := slackless_interval_step_case_completed_job_rem ref_sched online_sched ref_job_cost online_job_cost
    arr_seq hva hcde job_cost_bound hb t1 t2 hsl hnps j hs hin hcomp
  rw [slackless_parts] at hsl ⊢
  refine ⟨hlt, ?_⟩
  set S := critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2
  have hnd : S.Nodup := critical_jobs_uniq ref_sched online_sched ref_job_cost online_job_cost arr_seq hva t1 t2
  rw [critical_jobs_filter_complete ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 (t1 + 1) t2
    (by omega')]
  have hsched : ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t1 + 1)) = true →
      ∃ j' : Job, (decide (j' ∈ S) && scheduled_at online_sched j' t) = true := by
    intro t ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    have htt : t = t1 := by omega
    subst htt
    exact ⟨j, by simp only [Bool.and_eq_true]; exact ⟨hin, hs⟩⟩
  have hinv := remaining_cost_invariant online_sched online_job_cost hcde job_cost_bound hb S t1 (t1 + 1)
    (Nat.le_succ t1) hnd hsched
  have hzero : ∀ y, y ∈ S →
      (!@completed_by Job _ _ online_sched online_job_cost y (t1 + 1)) = false →
      remaining_cost_bound online_sched job_cost_bound y (t1 + 1) = 0 := by
    intro y hy hfalse
    simp only [Bool.not_eq_false'] at hfalse
    by_cases hyj : y = j
    · rw [hyj]; exact hz
    · exfalso
      have hinc : (!@completed_by Job _ _ online_sched online_job_cost y t1) = true := by
        rw [mem_critical_jobs] at hy
        rw [hy.2.2]; rfl
      have := (other_job_unchanged online_sched online_job_cost hcde job_cost_bound hb j y t1 hs
        (Ne.symm hyj)).2 hinc
      rw [hfalse] at this
      exact Bool.false_ne_true this
  have hf := sumSeq_filter_of_zero S
    (fun y => !@completed_by Job _ _ online_sched online_job_cost y (t1 + 1))
    (fun y => remaining_cost_bound online_sched job_cost_bound y (t1 + 1)) hzero
  rw [hf]
  omega'

/-- Case 2: the critical job scheduled at `t1` remains incomplete. -/
theorem slackless_interval_step_case_incomplete_job [JobArrival Job]
    (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      ∀ t1 t2 : Nat,
        slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 = true →
        t1 + 1 < t2 →
        nonpositive_slack ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound (t1 + 1) t2 = true →
        ∀ j : Job, scheduled_at online_sched j t1 = true →
          decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2) = true →
          (!@completed_by Job _ _ online_sched online_job_cost j (t1 + 1)) = true →
          slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
            (t1 + 1) t2 = true := by
  intro hva hcde job_cost_bound hb t1 t2 hsl hlt _ j hs hin hncomp
  rw [slackless_parts] at hsl ⊢
  refine ⟨hlt, ?_⟩
  set S := critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2
  have hnd : S.Nodup := critical_jobs_uniq ref_sched online_sched ref_job_cost online_job_cost arr_seq hva t1 t2
  rw [critical_jobs_filter_complete ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 (t1 + 1) t2
    (by omega')]
  have hself : S.filter (fun y => !@completed_by Job _ _ online_sched online_job_cost y (t1 + 1)) = S := by
    rw [List.filter_eq_self]
    intro y hy
    by_cases hyj : y = j
    · subst hyj; exact hncomp
    · have hinc : (!@completed_by Job _ _ online_sched online_job_cost y t1) = true := by
        rw [mem_critical_jobs] at hy
        rw [hy.2.2]; rfl
      exact (other_job_unchanged online_sched online_job_cost hcde job_cost_bound hb j y t1 hs
        (Ne.symm hyj)).2 hinc
  rw [hself]
  have hsched : ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t1 + 1)) = true →
      ∃ j' : Job, (decide (j' ∈ S) && scheduled_at online_sched j' t) = true := by
    intro t ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    have htt : t = t1 := by omega
    subst htt
    exact ⟨j, by simp only [Bool.and_eq_true]; exact ⟨hin, hs⟩⟩
  have hinv := remaining_cost_invariant online_sched online_job_cost hcde job_cost_bound hb S t1 (t1 + 1)
    (Nat.le_succ t1) hnd hsched
  omega'

/-- The induction step: slackless intervals shrink to slackless intervals. -/
theorem slackless_interval_step [JobArrival Job] (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      transfer_schedulability_criterion ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound →
      ∀ t1 t2 : Nat,
        slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 = true →
        t1 + 1 < t2 →
        nonpositive_slack ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound (t1 + 1) t2 = true →
        slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
          (t1 + 1) t2 = true := by
  intro hva hcde job_cost_bound hb hcrit t1 t2 hsl hlt hnps
  obtain ⟨j, hj⟩ := hcrit t1 t2 hsl
  simp only [Bool.and_eq_true] at hj
  cases hc : @completed_by Job _ _ online_sched online_job_cost j (t1 + 1)
  · exact slackless_interval_step_case_incomplete_job ref_sched online_sched ref_job_cost online_job_cost
      arr_seq hva hcde job_cost_bound hb t1 t2 hsl hlt hnps j hj.1 hj.2 (by rw [hc]; rfl)
  · exact slackless_interval_step_case_completed_job ref_sched online_sched ref_job_cost online_job_cost
      arr_seq hva hcde job_cost_bound hb t1 t2 hsl hlt hnps j hj.1 hj.2 hc

/-- A slackless, contiguously non-positive slack interval is contiguously slackless. -/
theorem slackless_interval_continuation [JobArrival Job]
    (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      transfer_schedulability_criterion ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound →
      ∀ t1 t2 : Nat,
        slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 = true →
        contiguously_nps ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t1 t2 = true →
        (List.range' 0 (t2 - t1)).all (fun delta =>
          slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
            (t1 + delta) t2) = true := by
  intro hva hcde job_cost_bound hb hcrit t1 t2 hsl hcnps
  unfold contiguously_nps at hcnps
  rw [all_range'_iff] at hcnps ⊢
  intro d hd
  induction d with
  | zero => simpa using hsl
  | succ d ih =>
    have := slackless_interval_step ref_sched online_sched ref_job_cost online_job_cost arr_seq hva hcde
      job_cost_bound hb hcrit (t1 + d) t2 (ih (by omega')) (by omega')
      (by have := hcnps (d + 1) hd; rwa [show t1 + (d + 1) = t1 + d + 1 by omega'] at this)
    rwa [show t1 + d + 1 = t1 + (d + 1) by omega'] at this

/-- A late completion is preceded by a contiguously slackless interval. -/
theorem slackless_interval_existence [JobArrival Job]
    (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    jobs_come_from_arrival_sequence ref_sched arr_seq →
    jobs_must_arrive_to_execute ref_sched →
    @completed_jobs_dont_execute Job _ _ ref_sched ref_job_cost →
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      (∀ j : Job, @job_cost Job _ job_cost_bound j ≤ @job_cost Job _ ref_job_cost j) →
      transfer_schedulability_criterion ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound →
      ∀ (j : Job) (t2 : instant),
        @completed_by Job _ _ ref_sched ref_job_cost j t2 = true →
        (!@completed_by Job _ _ online_sched online_job_cost j t2) = true →
        ∃ t1 : instant,
          (contiguously_slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq
              job_cost_bound t1 t2 &&
            decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2)) = true := by
  intro hva hfrom harr hcder hcde job_cost_bound hb hd hcrit j t2 hc hnc
  obtain ⟨t1, hcnps, hlt, hstart⟩ := contiguously_nps_existence ref_sched online_sched ref_job_cost
    online_job_cost arr_seq hva hfrom harr job_cost_bound hb hd j t2 hc hnc
  refine ⟨t1, ?_⟩
  have hin : decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2) = true :=
    critical_jobs_monotonicity ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2 t2
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') j
      (late_in_critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq hva hfrom harr
        job_cost_bound hb hd j t2 hc hnc)
  have hcnps' := hcnps
  unfold contiguously_nps at hcnps'
  rw [all_range'_iff] at hcnps'
  have NPS1 := hcnps' 0 (by omega')
  simp only [Nat.add_zero] at NPS1
  have SL1 : slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
      t1 t2 = true := by
    rw [slackless_parts]
    refine ⟨hlt, ?_⟩
    have h1 : t2 - t1 ≤ sumSeq (critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2)
        (fun j => remaining_cost_bound online_sched job_cost_bound j t1) := by
      have := NPS1
      unfold nonpositive_slack at this
      exact of_decide_eq_true this
    rcases hstart with h0 | hpos
    · subst h0
      have hmin := critical_jobs_min_completion_time ref_sched online_sched ref_job_cost online_job_cost
        arr_seq hva hcder job_cost_bound hd t2
      have hc0 : sumSeq (critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq 0 t2)
          (fun j => remaining_cost_bound online_sched job_cost_bound j 0) =
          sumSeq (critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq 0 t2)
          (fun j => @job_cost Job _ job_cost_bound j) := by
        apply sumSeq_congr
        intro y _
        unfold remaining_cost_bound
        rw [service0]; rfl
      omega'
    · rcases Nat.eq_zero_or_pos t1 with h0 | ht1
      · subst h0
        simp only [Nat.zero_sub] at hpos
        rw [NPS1] at hpos
        exact absurd hpos (by decide)
      · unfold nonpositive_slack at hpos
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at hpos
        have hmono := critical_jobs_remaining_cost_monotonic ref_sched online_sched ref_job_cost
          online_job_cost arr_seq hcde job_cost_bound hb (t1 - 1) t1 t2 (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
        omega'
  simp only [Bool.and_eq_true]
  refine ⟨?_, hin⟩
  unfold contiguously_slackless_interval
  simp only [Bool.and_eq_true]
  exact ⟨SL1, slackless_interval_continuation ref_sched online_sched ref_job_cost online_job_cost arr_seq
    hva hcde job_cost_bound hb hcrit t1 t2 SL1 hcnps⟩

/-- All critical jobs complete by the end of a contiguously slackless interval. -/
theorem slackless_interval_completion [JobArrival Job]
    (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ job_cost_bound : JobCost Job,
      (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ job_cost_bound j) →
      transfer_schedulability_criterion ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound →
      ∀ (j : Job) (t1 t2 : Nat),
        contiguously_slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq
          job_cost_bound t1 t2 = true →
        decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2) = true →
        @completed_by Job _ _ online_sched online_job_cost j t2 = true := by
  intro hva hcde job_cost_bound hb hcrit j t1 t2 hcsl hcrj
  unfold contiguously_slackless_interval at hcsl
  simp only [Bool.and_eq_true] at hcsl
  obtain ⟨hsl, hall⟩ := hcsl
  rw [all_range'_iff] at hall
  rw [slackless_parts] at hsl
  obtain ⟨hlt, hzs⟩ := hsl
  set S := critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2
  have hsched : ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true →
      ∃ j' : Job, (decide (j' ∈ S) && scheduled_at online_sched j' t) = true := by
    intro t ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    have hsl' := hall (t - t1) (by omega')
    rw [show t1 + (t - t1) = t by omega'] at hsl'
    obtain ⟨j', hj'⟩ := hcrit t t2 hsl'
    simp only [Bool.and_eq_true] at hj'
    refine ⟨j', ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨critical_jobs_monotonicity ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t t2
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') j' hj'.2, hj'.1⟩
  have hinv := remaining_cost_invariant online_sched online_job_cost hcde job_cost_bound hb S t1 t2
    (by omega') (critical_jobs_uniq ref_sched online_sched ref_job_cost online_job_cost arr_seq hva t1 t2) hsched
  exact remaining_cost_zero online_sched online_job_cost hcde job_cost_bound hb S t2
    (decide_eq_true (by omega')) j hcrj

end TransferSchedulability

section MainResults

variable {Job : JobType} [DecidableEq Job]

/-- Sufficiency of the criterion w.r.t. online job costs. -/
theorem online_transfer_schedulability_criterion_sufficiency [JobArrival Job]
    (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    jobs_come_from_arrival_sequence ref_sched arr_seq →
    jobs_must_arrive_to_execute ref_sched →
    @completed_jobs_dont_execute Job _ _ ref_sched ref_job_cost →
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ ref_job_cost j) →
    transfer_schedulability_criterion ref_sched online_sched ref_job_cost online_job_cost arr_seq online_job_cost →
    schedulability_transferred ref_sched online_sched ref_job_cost online_job_cost := by
  intro hva hfrom harr hcder hcde hbnd hcrit j t2 hc
  by_contra hnc
  have hnc' : (!@completed_by Job _ _ online_sched online_job_cost j t2) = true := by simpa using hnc
  obtain ⟨t1, h⟩ := slackless_interval_existence ref_sched online_sched ref_job_cost online_job_cost arr_seq
    hva hfrom harr hcder hcde online_job_cost (fun _ => Nat.le_refl _) hbnd hcrit j t2 hc hnc'
  simp only [Bool.and_eq_true] at h
  exact hnc (slackless_interval_completion ref_sched online_sched ref_job_cost online_job_cost arr_seq hva hcde
    online_job_cost (fun _ => Nat.le_refl _) hcrit j t1 t2 h.1 h.2)

/-- The online sufficiency lifted to deadlines. -/
theorem online_transfer_schedulability_criterion_ensures_schedulability [JobArrival Job] [JobDeadline Job]
    (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    jobs_come_from_arrival_sequence ref_sched arr_seq →
    jobs_must_arrive_to_execute ref_sched →
    @completed_jobs_dont_execute Job _ _ ref_sched ref_job_cost →
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ ref_job_cost j) →
    transfer_schedulability_criterion ref_sched online_sched ref_job_cost online_job_cost arr_seq online_job_cost →
    ∀ j : Job, @job_meets_deadline Job _ _ ref_sched ref_job_cost _ j = true →
      @job_meets_deadline Job _ _ online_sched online_job_cost _ j = true := by
  intro hva hfrom harr hcder hcde hbnd hcrit j hmet
  exact deadlines_met ref_sched online_sched ref_job_cost online_job_cost
    (online_transfer_schedulability_criterion_sufficiency ref_sched online_sched ref_job_cost online_job_cost
      arr_seq hva hfrom harr hcder hcde hbnd hcrit) j hmet

/-- A slackless interval without a scheduled critical job forces a late completion. -/
theorem delay_if_no_critical_job_is_scheduled [JobArrival Job]
    (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    ∀ t1 t2 : Nat,
      slackless_interval ref_sched online_sched ref_job_cost online_job_cost arr_seq online_job_cost t1 t2 = true →
      (∀ j : Job,
        decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2) = true →
        (!scheduled_at online_sched j t1) = true) →
      ∃ j : Job,
        decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2) = true ∧
        (!@completed_by Job _ _ online_sched online_job_cost j t2) = true := by
  intro hva hcde t1 t2 hsl hnone
  rw [slackless_parts] at hsl
  obtain ⟨hlt, hzs⟩ := hsl
  set S := critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2
  by_contra hcon
  have hall : ∀ j, j ∈ S → @completed_by Job _ _ online_sched online_job_cost j t2 = true := by
    intro j hj
    by_contra hnc
    exact hcon ⟨j, decide_eq_true hj, by simpa using hnc⟩
  have hb : ∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ online_job_cost j :=
    fun _ => Nat.le_refl _
  -- the remaining cost bounds at t2 vanish
  have hz2 : sumSeq S (fun j => remaining_cost_bound online_sched online_job_cost j t2) = 0 := by
    apply sumSeq_zero
    intro j hj
    have := of_decide_eq_true (show decide _ = true from hall j hj)
    unfold remaining_cost_bound
    omega'
  -- the service at t1 vanishes
  have hsplit : sumSeq S (fun j => remaining_cost_bound online_sched online_job_cost j t1) =
      sumSeq S (fun j => remaining_cost_bound online_sched online_job_cost j t2) +
        sumSeq S (fun j => service_during online_sched j (t1 + 1) t2) := by
    rw [← sumSeq_add]
    apply sumSeq_congr
    intro j hj
    have h1 := remcost_service_during online_sched online_job_cost hcde online_job_cost hb j t1 t2 (by omega')
    have h2 := service_during_first_plus_later online_sched j t1 t2 hlt
    have hns := hnone j (decide_eq_true hj)
    have h3 : service_at online_sched j t1 = 0 := by
      rw [service_at_is_scheduled_at]
      simp only [Bool.not_eq_true'] at hns
      rw [hns]; rfl
    omega'
  have hsoj : sumSeq S (fun j => service_during online_sched j (t1 + 1) t2) =
      service_of_jobs online_sched (fun _ => true) S (t1 + 1) t2 := by
    unfold service_of_jobs sumFiltered
    rw [List.filter_true]; rfl
  have hle := service_of_jobs_le_length_of_interval' (ideal_proc_model_provides_unit_service Job)
    (ideal_proc_model_is_a_uniprocessor_model Job) online_sched (fun _ => true) S
    (critical_jobs_uniq ref_sched online_sched ref_job_cost online_job_cost arr_seq hva t1 t2) (t1 + 1) t2
  omega'

/-- Necessity of the criterion w.r.t. online job costs. -/
theorem online_transfer_schedulability_criterion_necessity [JobArrival Job]
    (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    schedulability_transferred ref_sched online_sched ref_job_cost online_job_cost →
    transfer_schedulability_criterion ref_sched online_sched ref_job_cost online_job_cost arr_seq online_job_cost := by
  intro hva hcde htrans t1 t2 hsl
  by_contra hno
  have hnone : ∀ j : Job,
      decide (j ∈ critical_jobs ref_sched online_sched ref_job_cost online_job_cost arr_seq t1 t2) = true →
      (!scheduled_at online_sched j t1) = true := by
    intro j hj
    cases hs : scheduled_at online_sched j t1
    · rfl
    · exact absurd ⟨j, by simp only [Bool.and_eq_true]; exact ⟨hs, hj⟩⟩ hno
  obtain ⟨j, hj, hnc⟩ := delay_if_no_critical_job_is_scheduled ref_sched online_sched ref_job_cost
    online_job_cost arr_seq hva hcde t1 t2 hsl hnone
  rw [decide_eq_true_eq, mem_critical_jobs] at hj
  have := htrans j t2 hj.2.1
  rw [this] at hnc
  exact Bool.false_ne_true hnc

/-- Sufficiency of the criterion w.r.t. reference job costs. -/
theorem ref_transfer_schedulability_criterion_sufficiency [JobArrival Job]
    (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    jobs_come_from_arrival_sequence ref_sched arr_seq →
    jobs_must_arrive_to_execute ref_sched →
    @completed_jobs_dont_execute Job _ _ ref_sched ref_job_cost →
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ ref_job_cost j) →
    transfer_schedulability_criterion ref_sched online_sched ref_job_cost online_job_cost arr_seq ref_job_cost →
    schedulability_transferred ref_sched online_sched ref_job_cost online_job_cost := by
  intro hva hfrom harr hcder hcde hbnd hcrit j t2 hc
  by_contra hnc
  have hnc' : (!@completed_by Job _ _ online_sched online_job_cost j t2) = true := by simpa using hnc
  obtain ⟨t1, h⟩ := slackless_interval_existence ref_sched online_sched ref_job_cost online_job_cost arr_seq
    hva hfrom harr hcder hcde ref_job_cost hbnd (fun _ => Nat.le_refl _) hcrit j t2 hc hnc'
  simp only [Bool.and_eq_true] at h
  exact hnc (slackless_interval_completion ref_sched online_sched ref_job_cost online_job_cost arr_seq hva hcde
    ref_job_cost hbnd hcrit j t1 t2 h.1 h.2)

/-- The reference sufficiency lifted to deadlines. -/
theorem ref_transfer_schedulability_criterion_ensures_schedulability [JobArrival Job] [JobDeadline Job]
    (ref_sched online_sched : schedule (processor_state Job))
    (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    jobs_come_from_arrival_sequence ref_sched arr_seq →
    jobs_must_arrive_to_execute ref_sched →
    @completed_jobs_dont_execute Job _ _ ref_sched ref_job_cost →
    @completed_jobs_dont_execute Job _ _ online_sched online_job_cost →
    (∀ j : Job, @job_cost Job _ online_job_cost j ≤ @job_cost Job _ ref_job_cost j) →
    transfer_schedulability_criterion ref_sched online_sched ref_job_cost online_job_cost arr_seq ref_job_cost →
    ∀ j : Job, @job_meets_deadline Job _ _ ref_sched ref_job_cost _ j = true →
      @job_meets_deadline Job _ _ online_sched online_job_cost _ j = true := by
  intro hva hfrom harr hcder hcde hbnd hcrit j hmet
  exact deadlines_met ref_sched online_sched ref_job_cost online_job_cost
    (ref_transfer_schedulability_criterion_sufficiency ref_sched online_sched ref_job_cost online_job_cost
      arr_seq hva hfrom harr hcder hcde hbnd hcrit) j hmet

end MainResults

end Prosa.Results.TransferSchedulability.Criterion
