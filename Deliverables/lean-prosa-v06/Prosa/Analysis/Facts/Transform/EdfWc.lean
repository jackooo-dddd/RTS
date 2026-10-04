-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/transform/edf_wc.v

import Prosa.Analysis.Facts.Transform.EdfOpt
import Prosa.Analysis.Facts.Transform.WcCorrectness
import Prosa.Analysis.Facts.Behavior.Deadlines
import Prosa.Analysis.Facts.Readiness.Backlogged

namespace Prosa.Analysis.Facts.Transform.EdfWc

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.WorkConserving
open Prosa.Analysis.Transform.Swap
open Prosa.Analysis.Transform.Prefix
open Prosa.Analysis.Transform.EdfTrans
open Prosa.Analysis.Definitions.SchedulePrefix
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Facts.Transform.Swaps
open Prosa.Analysis.Facts.Transform.EdfOpt
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.Behavior.Deadlines
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Facts.Readiness.Backlogged

/-! Work conservation is preserved by the EDF transformation.

Binder orders and hypothesis sets follow the elaborated source types (unused section context and hypotheses are
absent). The processor model is the accepted ideal processor `processor_state Job`; the sections' local
`basic_ready_instance` is the accepted Lean definition, registered as a local instance, so readiness in the
statements (`work_conserving`, `backlogged`, `valid_schedule`) is that instance, as in the elaborated types. A
Boolean in `Prop` position is `= true`; `t1 < t <= t2` is `(decide (t1 < t) && decide (t ≤ t2)) = true`. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

section NonIdleSwapWorkConservationLemmas

variable {Job : JobType} [DecidableEq Job]

attribute [local instance] basic_ready_instance

/-- A readiness-free unfolding of `backlogged` under the basic readiness model. -/
private theorem backlogged_basic [JobCost Job] [JobArrival Job] (sched : schedule (processor_state Job)) (j : Job)
    (t : instant) :
    backlogged sched j t = (has_arrived j t && !completed_by sched j t && !scheduled_at sched j t) := rfl

/-- Swapping keeps a job scheduled at `t1`. -/
theorem non_idle_swap_maintains_work_conservation_t1 [JobCost Job] [JobArrival Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (t1 t2 : instant) (j2 : Job) :
    scheduled_at sched j2 t2 = true → ∀ t : instant, work_conserving arr_seq sched → t = t1 →
      ∃ j_other : Job, scheduled_at (swapped sched t1 t2) j_other t = true := by
  intro h t _ ht
  subst ht
  exact ⟨j2, by rw [swap_job_scheduled_t1]; exact h⟩

/-- Swapping keeps a job scheduled at `t2`. -/
theorem non_idle_swap_maintains_work_conservation_t2 [JobCost Job] [JobArrival Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (t1 t2 : instant) (j1 : Job) :
    scheduled_at sched j1 t1 = true → ∀ t : instant, work_conserving arr_seq sched → t = t2 →
      ∃ j_other : Job, scheduled_at (swapped sched t1 t2) j_other t = true := by
  intro h t _ ht
  subst ht
  exact ⟨j1, by rw [swap_job_scheduled_t2]; exact h⟩

/-- Outside the two swapped instants, a job backlogged after the swap with unchanged service was backlogged
before it, so the original schedule is busy there, and so is the swapped one. -/
private theorem other_time_busy [JobCost Job] [JobArrival Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) (t1 t2 : instant) (j : Job) (t : instant)
    (h1 : t ≠ t1) (h2 : t ≠ t2) (hsrv : service sched j t = service (swapped sched t1 t2) j t)
    (harr : arrives_in arr_seq j) (hbl : backlogged (swapped sched t1 t2) j t = true)
    (hwc : work_conserving arr_seq sched) :
    ∃ j_other : Job, scheduled_at (swapped sched t1 t2) j_other t = true := by
  have hother : ∀ j', scheduled_at (swapped sched t1 t2) j' t = scheduled_at sched j' t := fun j' =>
    swap_job_scheduled_other_times sched t1 t2 j' t (decide_eq_true (Ne.symm h1)) (decide_eq_true (Ne.symm h2))
  have hbl' : backlogged sched j t = true := by
    rw [backlogged_basic] at hbl ⊢
    unfold completed_by at hbl ⊢
    rw [hsrv, ← hother j]
    exact hbl
  obtain ⟨j', hj'⟩ := hwc j t harr hbl'
  exact ⟨j', by rw [hother]; exact hj'⟩

/-- Work conservation before `t1` survives the swap. -/
theorem non_idle_swap_maintains_work_conservation_LEQ_t1 [JobCost Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) (t1 t2 : instant) :
    t1 ≤ t2 → ∀ j1 j2 : Job, scheduled_at sched j1 t1 = true → scheduled_at sched j2 t2 = true →
      ∀ (j : Job) (t : instant), arrives_in arr_seq j → backlogged (swapped sched t1 t2) j t = true →
        work_conserving arr_seq sched → t ≤ t1 →
          ∃ j_other : Job, scheduled_at (swapped sched t1 t2) j_other t = true := by
  intro hle j1 j2 hs1 hs2 j t harr hbl hwc ht
  by_cases e1 : t = t1
  · exact non_idle_swap_maintains_work_conservation_t1 arr_seq sched t1 t2 j2 hs2 t hwc e1
  by_cases e2 : t = t2
  · exact non_idle_swap_maintains_work_conservation_t2 arr_seq sched t1 t2 j1 hs1 t hwc e2
  exact other_time_busy arr_seq sched t1 t2 j t e1 e2 (service_before_swap_invariant sched t1 t2 hle t ht j)
    harr hbl hwc

/-- Work conservation after `t2` survives the swap. -/
theorem non_idle_swap_maintains_work_conservation_GT_t2 [JobCost Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) (t1 t2 : instant) :
    t1 ≤ t2 → ∀ j1 j2 : Job, scheduled_at sched j1 t1 = true → scheduled_at sched j2 t2 = true →
      ∀ (j : Job) (t : instant), arrives_in arr_seq j → backlogged (swapped sched t1 t2) j t = true →
        work_conserving arr_seq sched → t2 < t →
          ∃ j_other : Job, scheduled_at (swapped sched t1 t2) j_other t = true := by
  intro hle j1 j2 hs1 hs2 j t harr hbl hwc ht
  by_cases e1 : t = t1
  · exact non_idle_swap_maintains_work_conservation_t1 arr_seq sched t1 t2 j2 hs2 t hwc e1
  by_cases e2 : t = t2
  · exact non_idle_swap_maintains_work_conservation_t2 arr_seq sched t1 t2 j1 hs1 t hwc e2
  exact other_time_busy arr_seq sched t1 t2 j t e1 e2 (service_after_swap_invariant sched t1 t2 hle t ht j)
    harr hbl hwc

/-- Work conservation strictly after `t1` and up to `t2` survives the swap. -/
theorem non_idle_swap_maintains_work_conservation_BET_t1_t2 [JobCost Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) :
    completed_jobs_dont_execute sched → jobs_come_from_arrival_sequence sched arr_seq →
      ∀ (t1 t2 : instant) (j1 j2 : Job), job_arrival j2 ≤ t1 → scheduled_at sched j1 t1 = true →
        scheduled_at sched j2 t2 = true → ∀ t : instant, work_conserving arr_seq sched →
          (decide (t1 < t) && decide (t ≤ t2)) = true →
            ∃ j_other : Job, scheduled_at (swapped sched t1 t2) j_other t = true := by
  intro hcde hfrom t1 t2 j1 j2 harr2 hs1 hs2 t hwc hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  by_cases e2 : t = t2
  · exact non_idle_swap_maintains_work_conservation_t2 arr_seq sched t1 t2 j1 hs1 t hwc e2
  have e1 : t ≠ t1 := by omega'
  have hother : ∀ j', scheduled_at (swapped sched t1 t2) j' t = scheduled_at sched j' t := fun j' =>
    swap_job_scheduled_other_times sched t1 t2 j' t (decide_eq_true (Ne.symm e1)) (decide_eq_true (Ne.symm e2))
  by_cases hj2 : scheduled_at sched j2 t = true
  · exact ⟨j2, by rw [hother]; exact hj2⟩
  · have hbl : backlogged sched j2 t = true := by
      rw [backlogged_basic]
      have hlt := hcde j2 t2 hs2
      have hmono := service_monotonic sched j2 t t2 hr.2
      simp only [Bool.and_eq_true, Bool.not_eq_true', has_arrived, decide_eq_true_eq, completed_by,
        decide_eq_false_iff_not, Nat.not_le]
      refine ⟨⟨by omega', by omega'⟩, ?_⟩
      simpa using hj2
    obtain ⟨j', hj'⟩ := hwc j2 t (hfrom j2 t2 hs2) hbl
    exact ⟨j', by rw [hother]; exact hj'⟩

end NonIdleSwapWorkConservationLemmas

section FSCWorkConservationLemmas

variable {Job : JobType} [DecidableEq Job]

attribute [local instance] basic_ready_instance

/-- Swapping with the swap candidate maintains work conservation. -/
theorem fsc_swap_maintains_work_conservation [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      jobs_come_from_arrival_sequence sched arr_seq →
        ∀ (j1 : Job) (t1 : instant), scheduled_at sched j1 t1 = true → t1 < job_deadline j1 →
          work_conserving arr_seq sched →
            work_conserving arr_seq (swapped sched t1 (find_swap_candidate sched t1 j1)) := by
  intro hmust hcde hfrom j1 t1 hs hdl hwc j t harr hbl
  obtain ⟨j2, hs2, harr2⟩ := fsc_not_idle sched hmust j1 t1 hs hdl
  have hrange := fsc_range1 sched hmust j1 t1 hs hdl
  by_cases e1 : t = t1
  · exact non_idle_swap_maintains_work_conservation_t1 arr_seq sched t1 _ j2 hs2 t hwc e1
  by_cases e2 : t = find_swap_candidate sched t1 j1
  · exact non_idle_swap_maintains_work_conservation_t2 arr_seq sched t1 _ j1 hs t hwc e2
  by_cases hle : t ≤ t1
  · exact non_idle_swap_maintains_work_conservation_LEQ_t1 arr_seq sched t1 _ hrange j1 j2 hs hs2 j t harr hbl hwc hle
  by_cases hgt : find_swap_candidate sched t1 j1 < t
  · exact non_idle_swap_maintains_work_conservation_GT_t2 arr_seq sched t1 _ hrange j1 j2 hs hs2 j t harr hbl hwc hgt
  exact non_idle_swap_maintains_work_conservation_BET_t1_t2 arr_seq sched hcde hfrom t1 _ j1 j2 harr2 hs hs2 t hwc
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')

end FSCWorkConservationLemmas

section MakeEDFWorkConservationLemmas

variable {Job : JobType} [DecidableEq Job]

attribute [local instance] basic_ready_instance

/-- `make_edf_at` maintains work conservation. -/
theorem mea_maintains_work_conservation [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) :
    jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched → all_deadlines_met sched →
        ∀ t_edf : instant, work_conserving arr_seq sched → work_conserving arr_seq (make_edf_at sched t_edf) := by
  intro hfrom hmust hcde hdm t_edf hwc
  unfold make_edf_at
  cases h : sched t_edf with
  | none => exact hwc
  | some j_orig =>
    have hs : scheduled_at sched j_orig t_edf = true := by rw [scheduled_at_def]; simpa using h
    exact fsc_swap_maintains_work_conservation arr_seq sched hmust hcde hfrom j_orig t_edf hs
      (scheduled_at_implies_later_deadline sched hcde j_orig t_edf (hdm j_orig t_edf hs) hs) hwc

end MakeEDFWorkConservationLemmas

section EDFPrefixWorkConservationLemmas

variable {Job : JobType} [DecidableEq Job]

attribute [local instance] basic_ready_instance

/-- The schedule is well-behaved, its jobs come from the arrival sequence, and no scheduled job misses its
deadline. -/
def scheduled_behavior_premises [JobCost Job] [JobDeadline Job] [JobArrival Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) : Prop :=
  jobs_must_arrive_to_execute sched ∧ completed_jobs_dont_execute sched ∧
    jobs_come_from_arrival_sequence sched arr_seq ∧ all_deadlines_met sched

/-- The EDF prefix transformation maintains the premises and work conservation. -/
theorem edf_transform_prefix_maintains_work_conservation [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) (horizon : instant) :
    scheduled_behavior_premises arr_seq sched ∧ work_conserving arr_seq sched →
      scheduled_behavior_premises arr_seq (edf_transform_prefix sched horizon) ∧
        work_conserving arr_seq (edf_transform_prefix sched horizon) := by
  intro hP
  unfold edf_transform_prefix
  apply prefix_map_property_invariance
    (fun s => scheduled_behavior_premises arr_seq s ∧ work_conserving arr_seq s)
  · intro s t ⟨⟨hm, hc, hf, hd⟩, hw⟩
    exact ⟨⟨mea_jobs_must_arrive s hm hc hd t, mea_completed_jobs s hm hc hd t,
      mea_jobs_come_from_arrival_sequence s t arr_seq hf, mea_no_deadline_misses s hm hc hd t⟩,
      mea_maintains_work_conservation arr_seq s hf hm hc hd t hw⟩
  · exact hP

end EDFPrefixWorkConservationLemmas

section EDFTransformWorkConservationLemmas

variable {Job : JobType} [DecidableEq Job]

attribute [local instance] basic_ready_instance

/-- A valid schedule without deadline misses satisfies the premises. -/
theorem sched_satisfies_behavior_premises [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) :
    valid_schedule sched arr_seq → all_deadlines_met sched → scheduled_behavior_premises arr_seq sched := by
  intro hvs hdm
  exact ⟨jobs_must_arrive_to_be_ready sched hvs.2, completed_jobs_are_not_ready sched hvs.2, hvs.1, hdm⟩

/-- The EDF transformation maintains work conservation. -/
theorem edf_transform_maintains_work_conservation [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) :
    valid_schedule sched arr_seq → all_deadlines_met sched → work_conserving arr_seq sched →
      work_conserving arr_seq (edf_transform sched) := by
  intro hvs hdm hwc j t harr hbl
  have hP := sched_satisfies_behavior_premises arr_seq sched hvs hdm
  have ⟨hmust, hcde, _, _⟩ := hP
  have hid : identical_prefix (edf_transform sched) (edf_transform_prefix sched (t + 1)) (t + 1) :=
    edf_finite_prefix sched hmust hcde hdm (t + 1)
  rw [backlogged_prefix_invariance basic_readiness_nonclairvoyance _ _ (t + 1) hid t j (by omega')] at hbl
  have hwc' := (edf_transform_prefix_maintains_work_conservation arr_seq sched (t + 1) ⟨hP, hwc⟩).2
  obtain ⟨j', hj'⟩ := hwc' j t harr hbl
  exact ⟨j', by rw [identical_prefix_scheduled_at _ _ (t + 1) hid j' t (by omega')]; exact hj'⟩

end EDFTransformWorkConservationLemmas

end Prosa.Analysis.Facts.Transform.EdfWc
