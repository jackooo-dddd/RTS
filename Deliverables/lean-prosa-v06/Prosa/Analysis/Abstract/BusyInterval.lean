-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/busy_interval.v

import Prosa.Analysis.Abstract.IwAuxiliary
import Prosa.Analysis.Facts.Model.Workload
import Prosa.Analysis.Abstract.Definitions

namespace Prosa.Analysis.Abstract.BusyInterval


open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Aggregate.Workload
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.IwAuxiliary
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Util.Sum
open scoped BigOperators

/-! Lemmas about abstract busy intervals. Binders follow the elaborated
source types: every lemma takes only the section inputs and hypotheses it
uses, in their elaborated order (unused task/cost context and hypotheses are
absent). Representation: a Boolean in `Prop` position is `= true`;
`a < b <= c` is `(decide (a < b) && decide (b ≤ c)) = true`; `t.+1` is
`t + 1`; `~ P` is `¬ P`; `j \in s` is `decide (j ∈ s) = true`. -/

section LemmasAboutAbstractBusyInterval

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}
variable [Interference Job] [InterferingWorkload Job]

theorem busy_interval_prefix_case (sched : schedule PState) (j : Job) (t1 t2 : instant) :
    busy_interval_prefix sched j t1 t2 ∨ ¬ busy_interval_prefix sched j t1 t2 :=
  Classical.em _

theorem terminating_busy_prefix_is_busy_interval (sched : schedule PState) (j : Job) :
    job_cost_positive j = true →
    ∀ (t1 : instant) (t2 t2' : Nat), t2 ≤ t2' →
      busy_interval_prefix sched j t1 t2 → ¬ busy_interval_prefix sched j t1 t2' →
      ∃ t2'' : instant, busy_interval sched j t1 t2'' := by
  intro _ t1 t2 t2' LE BUSY
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le LE
  clear LE
  induction k with
  | zero => intro NBUSY; exact absurd BUSY NBUSY
  | succ k ih =>
      intro NBUSY
      by_cases BUSY' : busy_interval_prefix sched j t1 (t2 + k)
      · refine ⟨t2 + k, BUSY', ?_⟩
        by_contra hq
        apply NBUSY
        obtain ⟨⟨h1, h2⟩, hq1, hint⟩ := BUSY
        refine ⟨⟨h1, by omega'⟩, hq1, ?_⟩
        intro t ⟨ht1, ht2⟩
        by_cases heq : t = t2 + k
        · subst heq; exact hq
        · exact BUSY'.2.2 t ⟨ht1, by omega'⟩
      · exact ih BUSY'

theorem job_completes_within_busy_interval (sched : schedule PState) (j : Job) (t1 t2 : instant) :
    busy_interval sched j t1 t2 → completed_by sched j t2 = true := by
  rintro ⟨⟨⟨_, hlt⟩, _, _⟩, hq⟩
  unfold quiet_time pending_earlier_and_at arrived_before at hq
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Bool.not_eq_false'] at hq
  rcases hq.2 with h | h
  · exact absurd hlt h
  · exact h

theorem no_service_before_busy_interval (sched : schedule PState) :
    jobs_must_arrive_to_execute sched →
    ∀ j : Job, job_cost_positive j = true →
      ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
        ∀ t : instant, service sched j t = service_during sched j t1 t := by
  intro harr j _ t1 t2 hbi t
  have hle : t1 ≤ job_arrival j := hbi.1.1.1
  by_cases h : t1 ≤ t
  · rw [← service_cat sched j t1 t h]
    have h0 : service sched j t1 = 0 :=
      cumulative_service_before_job_arrival_zero sched j harr 0 t1 hle
    rw [h0, Nat.zero_add]
  · rw [service_during_geq sched j t1 t (by omega')]
    exact cumulative_service_before_job_arrival_zero sched j harr 0 t (by omega')

theorem service_within_busy_interval_ge_job_cost (sched : schedule PState) :
    jobs_must_arrive_to_execute sched →
    ∀ j : Job, job_cost_positive j = true →
      ∀ t1 t2 : instant, busy_interval sched j t1 t2 → job_cost j ≤ service_during sched j t1 t2 := by
  intro harr j hpos t1 t2 hbi
  have hc := job_completes_within_busy_interval sched j t1 t2 hbi
  unfold completed_by at hc
  have hc' := of_decide_eq_true hc
  rw [no_service_before_busy_interval sched harr j hpos t1 t2 hbi t2] at hc'
  exact hc'

theorem abstract_busy_interval_arrivals_before (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (j : Job) :
    arrives_in arr_seq j → ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
      consistent_arrival_times arr_seq → decide (j ∈ arrivals_before arr_seq t2) = true := by
  intro ha t1 t2 hbi hc
  have hlt : job_arrival j < t2 := hbi.1.1.2
  exact arrived_between_implies_in_arrivals arr_seq hc j 0 t2 ha
    (by simp [arrived_between, hlt])

theorem abstract_busy_interval_prefix_job_arrival (sched : schedule PState) (j : Job) (t t' : instant) :
    busy_interval_prefix sched j t t' → t ≤ job_arrival j :=
  fun h => h.1.1

theorem abstract_busy_interval_job_arrival (sched : schedule PState) (j : Job) (t1 t2 : instant) :
    busy_interval sched j t1 t2 → t1 ≤ job_arrival j :=
  fun h => abstract_busy_interval_prefix_job_arrival sched j t1 t2 h.1

theorem service_and_interference_bound (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
      ∀ t1 t2 : instant, busy_interval sched j t1 t2 → unit_service_proc_model PState →
        ∀ Δ : Nat, t1 + Δ ≤ t2 →
          service_during sched j t1 (t1 + Δ) + cumulative_interference j t1 (t1 + Δ) ≤ Δ := by
  intro hwc j ha hpos t1 t2 hbi hunit Δ hle
  have hpos' : job_cost j > 0 := of_decide_eq_true hpos
  unfold service_during cumulative_interference cumul_cond_interference
  rw [← Finset.sum_add_distrib]
  calc ∑ t ∈ Finset.Ico t1 (t1 + Δ), (service_at sched j t + (cond_interference (fun _ _ => true) j t).toNat)
      ≤ ∑ t ∈ Finset.Ico t1 (t1 + Δ), (1 : Nat) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_Ico] at ht
        have hw := hwc j t1 t2 t ha hpos' hbi.1 ⟨ht.1, by omega'⟩
        unfold cond_interference
        simp only [Bool.true_and]
        cases hi : interference j t
        · have hs : service_at sched j t ≤ 1 := hunit j (sched t)
          simp only [Bool.toNat_false]
          omega'
        · have hns : ¬ receives_service_at sched j t = true := fun hr => (hw.mpr hr) hi
          unfold receives_service_at at hns
          have : service_at sched j t = 0 := by
            by_contra hne
            exact hns (decide_eq_true (Nat.pos_of_ne_zero hne))
          simp only [this, Bool.toNat_true]
          omega'
    _ = Δ := sum_of_ones t1 Δ

end LemmasAboutAbstractBusyInterval

section AbstractBusyIntervalExists

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}

/-- `LEAN_HELPER`: at time `0` every job is in a quiet time. -/
private theorem quiet_time_zero [Interference Job] [InterferingWorkload Job]
    (sched : schedule PState) (j : Job) : quiet_time sched j 0 = true := by
  unfold quiet_time
  have h1 : cumulative_interference j 0 0 = 0 := by
    simp [cumulative_interference, cumul_cond_interference]
  have h2 : cumulative_interfering_workload j 0 0 = 0 := by
    simp [cumulative_interfering_workload]
  rw [h1, h2, not_pending_earlier_and_at_0]
  rfl

theorem exists_busy_interval_prefix [Interference Job] [InterferingWorkload Job]
    (sched : schedule PState) (j : Job) (t_busy : instant) :
    pending sched j t_busy = true →
      ∃ t1 : instant, busy_interval_prefix sched j t1 (t_busy + 1) ∧
        (decide (t1 ≤ job_arrival j) && decide (job_arrival j ≤ t_busy)) = true := by
  intro PEND
  have hP0 : quiet_time sched j 0 = true := quiet_time_zero sched j
  let t1 := Nat.findGreatest (fun t => quiet_time sched j t = true) t_busy
  have hQ : quiet_time sched j t1 = true :=
    Nat.findGreatest_spec (P := fun t => quiet_time sched j t = true) (Nat.zero_le t_busy) hP0
  have hle : t1 ≤ t_busy := Nat.findGreatest_le t_busy
  unfold pending at PEND
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at PEND
  obtain ⟨harr, hnc⟩ := PEND
  have harr' : job_arrival j ≤ t_busy := of_decide_eq_true harr
  have hA : t1 ≤ job_arrival j := by
    by_contra hlt
    have hq := hQ
    unfold quiet_time pending_earlier_and_at arrived_before at hq
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
      Bool.not_eq_false'] at hq
    rcases hq.2 with h | h
    · exact h (by omega')
    · have := completion_monotonic sched j t1 t_busy hle h
      rw [this] at hnc; exact absurd hnc (by decide)
  refine ⟨t1, ⟨⟨hA, by omega'⟩, hQ, ?_⟩, ?_⟩
  · intro t ⟨ht1, ht2⟩ hq
    exact Nat.findGreatest_is_greatest ht1 (by omega') hq
  · simp [hA, harr']

section Bounding

variable [Interference Job] [InterferingWorkload Job]

theorem busy_interval_has_uninterrupted_service (arr_seq : arrival_sequence Job) (tsk : Task)
    (sched : schedule PState) :
    work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
      ∀ t_busy t1 : instant, busy_interval_prefix sched j t1 (t_busy + 1) →
        ∀ δ : duration,
          (∀ t : Nat, (decide (t1 < t) && decide (t ≤ t1 + δ)) = true → ¬ quiet_time sched j t = true) →
          δ ≤ service_during sched j t1 (t1 + δ) + cumulative_interference j t1 (t1 + δ) := by
  intro hwc j ha _ hpos t_busy t1 hpre δ hnq
  have hpos' : job_cost j > 0 := of_decide_eq_true hpos
  unfold service_during cumulative_interference cumul_cond_interference
  rw [← Finset.sum_add_distrib]
  calc δ = ∑ t ∈ Finset.Ico t1 (t1 + δ), (1 : Nat) := (sum_of_ones t1 δ).symm
    _ ≤ ∑ t ∈ Finset.Ico t1 (t1 + δ),
          (service_at sched j t + (cond_interference (fun _ _ => true) j t).toNat) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.mem_Ico] at hx
        have hw : (¬ interference j x = true ↔ receives_service_at sched j x = true) := by
          by_cases hle : t1 + δ ≤ t_busy + 1
          · exact hwc j t1 (t_busy + 1) x ha hpos' hpre ⟨hx.1, by omega'⟩
          · have hpre' : busy_interval_prefix sched j t1 (t1 + δ) := by
              obtain ⟨⟨h1, h2⟩, hq1, _⟩ := hpre
              refine ⟨⟨h1, by omega'⟩, hq1, ?_⟩
              intro t ⟨ht1, ht2⟩
              exact hnq t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
            exact hwc j t1 (t1 + δ) x ha hpos' hpre' ⟨hx.1, hx.2⟩
        unfold cond_interference
        simp only [Bool.true_and]
        cases hi : interference j x
        · have hr := hw.mp (by rw [hi]; simp)
          unfold receives_service_at at hr
          have := of_decide_eq_true hr
          simp only [Bool.toNat_false]
          omega'
        · simp only [Bool.toNat_true]
          omega'

/-- `LEAN_HELPER`: the cumulative interference and interfering workload over
`[0, t1 + δ)` split at `t1`. -/
private theorem cumulative_interference_split (j : Job) (t1 δ : Nat) :
    cumulative_interference j 0 (t1 + δ) =
      cumulative_interference j 0 t1 + cumulative_interference j t1 (t1 + δ) :=
  cumulative_interference_cat (fun _ _ => true) j t1 0 (t1 + δ) (by simp)

private theorem cumulative_interfering_workload_split (j : Job) (t1 δ : Nat) :
    cumulative_interfering_workload j 0 (t1 + δ) =
      cumulative_interfering_workload j 0 t1 + cumulative_interfering_workload j t1 (t1 + δ) := by
  unfold cumulative_interfering_workload
  exact (Finset.sum_Ico_consecutive _ (Nat.zero_le t1) (Nat.le_add_right t1 δ)).symm

private theorem quiet_time_eq_of_quiet (sched : schedule PState) (j : Job) (t : instant) :
    quiet_time sched j t = true →
      cumulative_interference j 0 t = cumulative_interfering_workload j 0 t := by
  intro h
  unfold quiet_time at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem busy_interval_too_much_workload :
    no_speculative_execution (Job := Job) →
    ∀ arr_seq : arrival_sequence Job, consistent_arrival_times arr_seq → arrival_sequence_uniq arr_seq →
    ∀ (tsk : Task) (sched : schedule PState), work_conserving arr_seq sched →
      jobs_must_arrive_to_execute sched →
      ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
        ∀ t_busy t1 : instant, busy_interval_prefix sched j t1 (t_busy + 1) →
          ∀ δ : duration, 0 < δ →
            workload_of_job arr_seq j t1 (t1 + δ) + cumulative_interfering_workload j t1 (t1 + δ) ≤ δ →
            (∀ t : Nat, (decide (t1 < t) && decide (t ≤ t1 + δ)) = true → ¬ quiet_time sched j t = true) →
            job_cost j + cumulative_interfering_workload j t1 (t1 + δ) ≤
              service_during sched j t1 (t1 + δ) + cumulative_interference j t1 (t1 + δ) := by
  intro hns arr_seq hcons huniq tsk sched hwc harr j ha hjt hpos t_busy t1 hpre δ hδ hwl hnq
  have hU := busy_interval_has_uninterrupted_service arr_seq tsk sched hwc j ha hjt hpos t_busy t1 hpre δ hnq
  have hWL := workload_of_job_eq_job_arrival arr_seq hcons huniq j t1 (t1 + δ) ha
  have hA1 : t1 ≤ job_arrival j := hpre.1.1
  have hA2 : job_arrival j < t1 + δ := by
    by_contra hge
    have hge' : t1 + δ ≤ job_arrival j := by omega'
    apply hnq (t1 + δ) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    rw [hWL] at hwl
    simp only [show decide (job_arrival j < t1 + δ) = false from decide_eq_false hge,
      Bool.and_false, cond_false, Nat.zero_add] at hwl
    have hsd : service_during sched j t1 (t1 + δ) = 0 :=
      cumulative_service_before_job_arrival_zero sched j harr t1 (t1 + δ) hge'
    have hiw : cumulative_interfering_workload j t1 (t1 + δ) ≤ cumulative_interference j t1 (t1 + δ) := by
      omega'
    have hq1 := quiet_time_eq_of_quiet sched j t1 hpre.2.1
    have hle1 := hns j (t1 + δ)
    rw [cumulative_interference_split, cumulative_interfering_workload_split] at hle1
    unfold quiet_time pending_earlier_and_at arrived_before
    rw [cumulative_interference_split, cumulative_interfering_workload_split]
    have : decide (job_arrival j < t1 + δ) = false := decide_eq_false hge
    simp only [this, Bool.false_and, Bool.not_false, Bool.and_true, decide_eq_true_eq]
    omega'
  rw [hWL] at hwl
  simp only [show decide (t1 ≤ job_arrival j) = true from decide_eq_true hA1,
    show decide (job_arrival j < t1 + δ) = true from decide_eq_true hA2, Bool.and_self,
    cond_true] at hwl
  omega'

end Bounding

theorem t1δ_is_quiet :
    unit_service_proc_model PState →
    ∀ [Interference Job] [InterferingWorkload Job],
    no_speculative_execution (Job := Job) →
    ∀ arr_seq : arrival_sequence Job, consistent_arrival_times arr_seq → arrival_sequence_uniq arr_seq →
    ∀ (tsk : Task) (sched : schedule PState), work_conserving arr_seq sched →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
        ∀ t_busy : instant, pending sched j t_busy = true →
        ∀ t1 : instant, busy_interval_prefix sched j t1 (t_busy + 1) →
          ∀ δ : duration, 0 < δ →
            workload_of_job arr_seq j t1 (t1 + δ) + cumulative_interfering_workload j t1 (t1 + δ) ≤ δ →
            (∀ t : Nat, (decide (t1 < t) && decide (t ≤ t1 + δ)) = true → ¬ quiet_time sched j t = true) →
            quiet_time sched j (t1 + δ) = true := by
  intro hunit _ _ hns arr_seq hcons huniq tsk sched hwc harr hcomp j ha hjt hpos t_busy _ t1 hpre δ hδ hwl hnq
  have LW := busy_interval_too_much_workload hns arr_seq hcons huniq tsk sched hwc harr j ha hjt hpos
    t_busy t1 hpre δ hδ hwl hnq
  have hsd : service_during sched j t1 (t1 + δ) ≤ job_cost j := by
    have h1 := service_at_most_cost sched hcomp j hunit (t1 + δ)
    have h2 := service_cat sched j t1 (t1 + δ) (Nat.le_add_right t1 δ)
    omega'
  have hq1 := quiet_time_eq_of_quiet sched j t1 hpre.2.1
  have hle1 := hns j (t1 + δ)
  rw [cumulative_interference_split, cumulative_interfering_workload_split] at hle1
  have hci : cumulative_interference j t1 (t1 + δ) ≤ cumulative_interfering_workload j t1 (t1 + δ) := by
    omega'
  have EQ1 : job_cost j = service_during sched j t1 (t1 + δ) := by omega'
  have EQ2 : cumulative_interfering_workload j t1 (t1 + δ) = cumulative_interference j t1 (t1 + δ) := by
    omega'
  have hcompl : completed_by sched j (t1 + δ) = true := by
    unfold completed_by
    have h2 := service_cat sched j t1 (t1 + δ) (Nat.le_add_right t1 δ)
    exact decide_eq_true (by omega')
  unfold quiet_time pending_earlier_and_at
  rw [hcompl, cumulative_interference_split, cumulative_interfering_workload_split]
  simp only [Bool.not_true, Bool.and_false, Bool.not_false, Bool.and_true, decide_eq_true_eq]
  omega'

theorem t1δ_is_quiet_contra :
    unit_service_proc_model PState →
    ∀ [Interference Job] [InterferingWorkload Job],
    no_speculative_execution (Job := Job) →
    ∀ arr_seq : arrival_sequence Job, consistent_arrival_times arr_seq → arrival_sequence_uniq arr_seq →
    ∀ (tsk : Task) (sched : schedule PState), work_conserving arr_seq sched →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
        ∀ t_busy : instant, pending sched j t_busy = true →
        ∀ t1 : instant, busy_interval_prefix sched j t1 (t_busy + 1) →
          ∀ δ : duration, 0 < δ →
            workload_of_job arr_seq j t1 (t1 + δ) + cumulative_interfering_workload j t1 (t1 + δ) ≤ δ →
            (∀ t : Nat, (decide (t1 < t) && decide (t ≤ t1 + δ)) = true → ¬ quiet_time sched j t = true) →
            False := by
  intro hunit _ _ hns arr_seq hcons huniq tsk sched hwc harr hcomp j ha hjt hpos t_busy hpend t1 hpre δ hδ hwl hnq
  exact hnq (t1 + δ) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    (t1δ_is_quiet hunit hns arr_seq hcons huniq tsk sched hwc harr hcomp j ha hjt hpos t_busy hpend t1
      hpre δ hδ hwl hnq)

theorem busy_interval_is_bounded :
    unit_service_proc_model PState →
    ∀ [Interference Job] [InterferingWorkload Job],
    no_speculative_execution (Job := Job) →
    ∀ arr_seq : arrival_sequence Job, consistent_arrival_times arr_seq → arrival_sequence_uniq arr_seq →
    ∀ (tsk : Task) (sched : schedule PState), work_conserving arr_seq sched →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
        ∀ t_busy : instant, pending sched j t_busy = true →
        ∀ t1 : instant, busy_interval_prefix sched j t1 (t_busy + 1) →
          ∀ δ : duration, 0 < δ →
            workload_of_job arr_seq j t1 (t1 + δ) + cumulative_interfering_workload j t1 (t1 + δ) ≤ δ →
            ∃ t2 : Nat, t_busy < t2 ∧ t2 ≤ t1 + δ ∧ busy_interval sched j t1 t2 := by
  intro hunit _ _ hns arr_seq hcons huniq tsk sched hwc harr hcomp j ha hjt hpos t_busy hpend t1 hpre δ hδ hwl
  by_cases EX : ∃ t, t1 < t ∧ t ≤ t1 + δ ∧ quiet_time sched j t = true
  · classical
    let t2 := Nat.find EX
    have hspec : t1 < t2 ∧ t2 ≤ t1 + δ ∧ quiet_time sched j t2 = true := Nat.find_spec EX
    have hmin : ∀ t, t < t2 → ¬ (t1 < t ∧ t ≤ t1 + δ ∧ quiet_time sched j t = true) :=
      fun t ht => Nat.find_min EX ht
    have hbusy : t_busy < t2 := by
      by_contra hle
      exact hpre.2.2 t2 ⟨hspec.1, by omega'⟩ hspec.2.2
    refine ⟨t2, hbusy, hspec.2.1, ⟨⟨hpre.1.1, by have := hpre.1.2; omega'⟩, hpre.2.1, ?_⟩, hspec.2.2⟩
    intro t ⟨ht1, ht2⟩ hq
    exact hmin t ht2 ⟨ht1, by omega', hq⟩
  · exfalso
    apply t1δ_is_quiet_contra hunit hns arr_seq hcons huniq tsk sched hwc harr hcomp j ha hjt hpos t_busy
      hpend t1 hpre δ hδ hwl
    intro t ht hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    exact EX ⟨t, ht.1, ht.2, hq⟩


end AbstractBusyIntervalExists

end Prosa.Analysis.Abstract.BusyInterval
