-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/abstract_rta.v

import Prosa.Analysis.Definitions.Schedulability
import Prosa.Analysis.Abstract.SearchSpace
import Prosa.Analysis.Abstract.LowerBoundOnService

namespace Prosa.Analysis.Abstract.AbstractRta

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.SearchSpace
open Prosa.Analysis.Abstract.BusyInterval
open Prosa.Analysis.Abstract.LowerBoundOnService

/-! Abstract response-time analysis.
Binders follow the elaborated source types: every declaration takes only the
section inputs and hypotheses it uses, in their elaborated order; instance
inputs quantified after a hypothesis are `∀ [..]` binders at that position.
Representation: a Boolean in `Prop` position is `= true`; `tsk \in ts` is
`decide (tsk ∈ ts) = true`. -/

section AbstractRta

/-- Job `j` arrives exactly `A` time units after the start of its (unique)
busy interval. -/
def relative_arrival_time_of_job_is_A {Job : JobType} [DecidableEq Job] [JobArrival Job]
    [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState)
    [Interference Job] [InterferingWorkload Job] (j : Job) (A : duration) : Prop :=
  ∀ t1 t2 : instant, busy_interval sched j t1 t2 → A = job_arrival j - t1

/-- By `t1 + F` job `j` has solved the first-stage recurrence and received
`task_rtct tsk` units of service. -/
def relative_time_to_reach_rtct {Task : TaskType} [DecidableEq Task]
    [TaskRunToCompletionThreshold Task] {Job : JobType} [DecidableEq Job] [JobArrival Job]
    [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState) (tsk : Task)
    [Interference Job] [InterferingWorkload Job] (IBF_P : duration → duration → duration)
    (j : Job) (F : duration) : Prop :=
  ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
    task_rtct tsk + IBF_P (job_arrival j - t1) F ≤ F ∧ task_rtct tsk ≤ service sched j (t1 + F)

theorem job_arrival_eq_t1_plus_A {Job : JobType} [DecidableEq Job] [JobArrival Job]
    [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState)
    [Interference Job] [InterferingWorkload Job] (j : Job) (t1 t2 : instant) :
    busy_interval sched j t1 t2 → job_arrival j = t1 + (job_arrival j - t1) := by
  rintro ⟨⟨⟨hle, _⟩, _, _⟩, _⟩
  omega'

/-- The busy interval of `j` is the one given by the bound `L`. -/
private theorem bounded_busy_interval {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (tsk : Task) [Interference Job] [InterferingWorkload Job] (L : duration)
    (hL : busy_intervals_are_bounded_by arr_seq sched tsk L) (j : Job)
    (ha : arrives_in arr_seq j) (hjt : job_of_task tsk j = true)
    (hpos : job_cost_positive j = true) (t1 t2 : instant) (hbi : busy_interval sched j t1 t2) :
    t2 ≤ t1 + L := by
  obtain ⟨t1', t2', _, hle, hbi'⟩ := hL j ha hjt (of_decide_eq_true hpos)
  obtain ⟨rfl, rfl⟩ := busy_interval_is_unique sched j t1 t2 t1' t2' hbi hbi'
  exact hle

theorem relative_arrival_is_bounded {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (tsk : Task) [Interference Job] [InterferingWorkload Job] (L : duration) :
    busy_intervals_are_bounded_by arr_seq sched tsk L →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
      ∀ t1 t2 : instant, busy_interval sched j t1 t2 → job_arrival j - t1 < L := by
  intro hL j ha hjt hpos t1 t2 hbi
  have h := bounded_busy_interval arr_seq sched tsk L hL j ha hjt hpos t1 t2 hbi
  obtain ⟨⟨⟨hle, hlt⟩, _, _⟩, _⟩ := hbi
  omega'

theorem t2_le_arrival_plus_R_1 {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (sched : schedule PState) (tsk : Task)
    [Interference Job] [InterferingWorkload Job] (IBF_NP : duration → duration → duration) :
    (∀ (F : Nat) (Δ : duration), F ≤ task_cost tsk + IBF_NP F Δ) →
    ∀ (R : duration) (j : Job) (t1 t2 : instant), busy_interval sched j t1 t2 →
      ∀ A_sp : duration, A_sp ≤ job_arrival j - t1 →
        ∀ F : duration, task_cost tsk + IBF_NP F (A_sp + R) ≤ A_sp + R →
          t2 ≤ t1 + F → t2 ≤ job_arrival j + R := by
  intro hge R j t1 t2 hbi A_sp hA F hfix hbig
  have h1 := hge F (A_sp + R)
  obtain ⟨⟨⟨hle, _⟩, _, _⟩, _⟩ := hbi
  omega'

theorem job_completed_by_arrival_plus_R_1 {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (sched : schedule PState) (tsk : Task)
    [Interference Job] [InterferingWorkload Job] (IBF_NP : duration → duration → duration) :
    (∀ (F : Nat) (Δ : duration), F ≤ task_cost tsk + IBF_NP F Δ) →
    ∀ (R : duration) (j : Job) (t1 t2 : instant), busy_interval sched j t1 t2 →
      ∀ A_sp : duration, A_sp ≤ job_arrival j - t1 →
        ∀ F : duration, task_cost tsk + IBF_NP F (A_sp + R) ≤ A_sp + R →
          t2 ≤ t1 + F → completed_by sched j (job_arrival j + R) = true := by
  intro hge R j t1 t2 hbi A_sp hA F hfix hbig
  exact completion_monotonic sched j t2 _
    (t2_le_arrival_plus_R_1 sched tsk IBF_NP hge R j t1 t2 hbi A_sp hA F hfix hbig)
    (job_completes_within_busy_interval sched j t1 t2 hbi)

theorem t2_le_arrival_plus_R_2 {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    [Interference Job] [InterferingWorkload Job] (R : duration) (j : Job) (t1 t2 : instant) :
    busy_interval sched j t1 t2 →
      ∀ A_sp : duration, A_sp ≤ job_arrival j - t1 →
        t2 ≤ t1 + (A_sp + R) → t2 ≤ job_arrival j + R := by
  intro hbi A_sp hA hbig
  obtain ⟨⟨⟨hle, _⟩, _, _⟩, _⟩ := hbi
  omega'

theorem job_completed_by_arrival_plus_R_2 {Job : JobType} [DecidableEq Job] [JobArrival Job]
    [JobCost Job] {PState : ProcessorState Job} (sched : schedule PState)
    [Interference Job] [InterferingWorkload Job] (R : duration) (j : Job) (t1 t2 : instant) :
    busy_interval sched j t1 t2 →
      ∀ A_sp : duration, A_sp ≤ job_arrival j - t1 →
        t2 ≤ t1 + (A_sp + R) → completed_by sched j (job_arrival j + R) = true := by
  intro hbi A_sp hA hbig
  exact completion_monotonic sched j t2 _ (t2_le_arrival_plus_R_2 sched R j t1 t2 hbi A_sp hA hbig)
    (job_completes_within_busy_interval sched j t1 t2 hbi)

theorem relative_rtc_time_is_bounded {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (tsk : Task) [Interference Job] [InterferingWorkload Job] (L : duration) :
    busy_intervals_are_bounded_by arr_seq sched tsk L →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
      ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
        ∀ F : duration, t1 + F < t2 → F < L := by
  intro hL j ha hjt hpos t1 t2 hbi F hF
  have h := bounded_busy_interval arr_seq sched tsk L hL j ha hjt hpos t1 t2 hbi
  omega'

/-- The first-stage interference of `j` up to `t1 + F` is bounded by
`IBF_P A_sp F`. -/
private theorem first_stage_interference {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (tsk : Task) [Interference Job] [InterferingWorkload Job] (L : duration)
    (hL : busy_intervals_are_bounded_by arr_seq sched tsk L)
    (IBF_P : duration → duration → duration)
    (hP : job_interference_is_bounded_by arr_seq sched tsk IBF_P
      (relative_arrival_time_of_job_is_A sched))
    (j : Job) (ha : arrives_in arr_seq j) (hjt : job_of_task tsk j = true)
    (hpos : job_cost_positive j = true) (t1 t2 : instant) (hbi : busy_interval sched j t1 t2)
    (A_sp : duration)
    (heq : are_equivalent_at_values_less_than (IBF_P (job_arrival j - t1)) (IBF_P A_sp) L)
    (F : duration) (hF : t1 + F < t2) (hnc : (!completed_by sched j (t1 + F)) = true) :
    cumulative_interference j t1 (t1 + F) ≤ IBF_P A_sp F := by
  have hFL := relative_rtc_time_is_bounded arr_seq sched tsk L hL j ha hjt hpos t1 t2 hbi F hF
  rw [← heq F hFL]
  refine hP t1 t2 F j ha hjt hbi hF hnc (job_arrival j - t1) ?_
  intro t1' t2' hbi'
  obtain ⟨rfl, rfl⟩ := busy_interval_is_unique sched j t1 t2 t1' t2' hbi hbi'
  rfl

private theorem not_completed_of_lt {Job : JobType} [DecidableEq Job] [JobCost Job]
    {PState : ProcessorState Job} (sched : schedule PState) (j : Job) (t : instant)
    (h : service sched j t < job_cost j) : (!completed_by sched j t) = true := by
  unfold completed_by
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  omega'

theorem job_receives_enough_service_1 {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [TaskRunToCompletionThreshold Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true →
    ∀ [Interference Job] [InterferingWorkload Job],
    work_conserving arr_seq sched →
    ∀ L : duration, busy_intervals_are_bounded_by arr_seq sched tsk L →
    ∀ IBF_P : duration → duration → duration,
      job_interference_is_bounded_by arr_seq sched tsk IBF_P
        (relative_arrival_time_of_job_is_A sched) →
    ∀ (IBF_NP : duration → duration → duration) (R : duration) (j : Job),
      arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
    ∀ A_sp : duration, A_sp ≤ job_arrival j - t1 →
      are_equivalent_at_values_less_than (IBF_P (job_arrival j - t1)) (IBF_P A_sp) L →
    ∀ F : duration, task_rtct tsk + IBF_P A_sp F ≤ F →
      task_cost tsk + IBF_NP F (A_sp + R) ≤ A_sp + R →
      t1 + F < t2 → t1 + (A_sp + R) < t2 →
      job_cost j ≤ task_rtct tsk → job_cost j ≤ service sched j (t1 + F) := by
  intro _ _ _ hwc L hL IBF_P hP IBF_NP R j ha hjt hpos t1 t2 hbi A_sp _ heq F hfix _ hF _ hsmall
  by_contra hlt
  have hnc := not_completed_of_lt sched j (t1 + F) (Nat.lt_of_not_le hlt)
  have hI := first_stage_interference arr_seq sched tsk L hL IBF_P hP j ha hjt hpos t1 t2 hbi
    A_sp heq F hF hnc
  exact hlt (j_receives_enough_service arr_seq sched tsk hwc j ha hjt hpos t1 t2 hbi
    (job_cost j) (Nat.le_refl _) F (by omega'))

theorem job_receives_enough_service_2 {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [TaskRunToCompletionThreshold Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true →
    ∀ [Interference Job] [InterferingWorkload Job],
    work_conserving arr_seq sched →
    ∀ L : duration, busy_intervals_are_bounded_by arr_seq sched tsk L →
    ∀ IBF_P : duration → duration → duration,
      job_interference_is_bounded_by arr_seq sched tsk IBF_P
        (relative_arrival_time_of_job_is_A sched) →
    ∀ (IBF_NP : duration → duration → duration) (R : duration) (j : Job),
      arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
    ∀ A_sp : duration, A_sp ≤ job_arrival j - t1 →
      are_equivalent_at_values_less_than (IBF_P (job_arrival j - t1)) (IBF_P A_sp) L →
    ∀ F : duration, task_rtct tsk + IBF_P A_sp F ≤ F →
      task_cost tsk + IBF_NP F (A_sp + R) ≤ A_sp + R →
      t1 + F < t2 → t1 + (A_sp + R) < t2 →
      task_rtct tsk ≤ job_cost j → task_rtct tsk ≤ service sched j (t1 + F) := by
  intro _ _ _ hwc L hL IBF_P hP IBF_NP R j ha hjt hpos t1 t2 hbi A_sp _ heq F hfix _ hF _ hbig
  by_contra hlt
  have hnc := not_completed_of_lt sched j (t1 + F) (by omega')
  have hI := first_stage_interference arr_seq sched tsk L hL IBF_P hP j ha hjt hpos t1 t2 hbi
    A_sp heq F hF hnc
  exact hlt (j_receives_enough_service arr_seq sched tsk hwc j ha hjt hpos t1 t2 hbi
    (task_rtct tsk) hbig F (by omega'))

theorem job_receives_enough_service_3 {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [TaskRunToCompletionThreshold Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
    ∀ [Interference Job] [InterferingWorkload Job],
    work_conserving arr_seq sched →
    ∀ L : duration, busy_intervals_are_bounded_by arr_seq sched tsk L →
    ∀ IBF_P : duration → duration → duration,
      job_interference_is_bounded_by arr_seq sched tsk IBF_P
        (relative_arrival_time_of_job_is_A sched) →
    ∀ IBF_NP : duration → duration → duration,
      job_interference_is_bounded_by arr_seq sched tsk IBF_NP
        (relative_time_to_reach_rtct sched tsk IBF_P) →
    ∀ (R : duration) (j : Job),
      arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
    ∀ A_sp : duration, A_sp ≤ job_arrival j - t1 →
      are_equivalent_at_values_less_than (IBF_P (job_arrival j - t1)) (IBF_P A_sp) L →
    ∀ F : duration, task_rtct tsk + IBF_P A_sp F ≤ F →
      task_cost tsk + IBF_NP F (A_sp + R) ≤ A_sp + R →
      t1 + F < t2 → t1 + (A_sp + R) < t2 →
      task_rtct tsk ≤ job_cost j → job_cost j ≤ service sched j (t1 + (A_sp + R)) := by
  intro hvalid ts tsk hts _ _ hwc L hL IBF_P hP IBF_NP hNP R j ha hjt hpos t1 t2 hbi A_sp hA heq
    F hfix hfix2 hF hF2 hbig
  by_contra hlt
  have hnc := not_completed_of_lt sched j (t1 + (A_sp + R)) (Nat.lt_of_not_le hlt)
  have hcost : job_cost j ≤ task_cost tsk := by
    have hv := of_decide_eq_true (hvalid j ha)
    have ht : job_task j = tsk := of_decide_eq_true hjt
    rw [ht] at hv
    exact hv
  have hFL := relative_rtc_time_is_bounded arr_seq sched tsk L hL j ha hjt hpos t1 t2 hbi F hF
  have h2 := job_receives_enough_service_2 arr_seq sched ts tsk hts hwc L hL IBF_P hP IBF_NP R j
    ha hjt hpos t1 t2 hbi A_sp hA heq F hfix hfix2 hF hF2 hbig
  have hI : cumulative_interference j t1 (t1 + (A_sp + R)) ≤ IBF_NP F (A_sp + R) := by
    refine hNP t1 t2 (A_sp + R) j ha hjt hbi hF2 hnc F ?_
    intro t1' t2' hbi'
    obtain ⟨rfl, rfl⟩ := busy_interval_is_unique sched j t1 t2 t1' t2' hbi hbi'
    refine ⟨?_, h2⟩
    rw [heq F hFL]
    exact hfix
  exact hlt (j_receives_enough_service arr_seq sched tsk hwc j ha hjt hpos t1 t2 hbi
    (job_cost j) (Nat.le_refl _) (A_sp + R) (by omega'))

theorem job_is_completed_by_arrival_plus_R {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [TaskRunToCompletionThreshold Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
    ∀ [Interference Job] [InterferingWorkload Job],
    work_conserving arr_seq sched →
    ∀ L : duration, busy_intervals_are_bounded_by arr_seq sched tsk L →
    ∀ IBF_P : duration → duration → duration,
      job_interference_is_bounded_by arr_seq sched tsk IBF_P
        (relative_arrival_time_of_job_is_A sched) →
    ∀ IBF_NP : duration → duration → duration,
      job_interference_is_bounded_by arr_seq sched tsk IBF_NP
        (relative_time_to_reach_rtct sched tsk IBF_P) →
      (∀ (F : Nat) (Δ : duration), F ≤ task_cost tsk + IBF_NP F Δ) →
    ∀ (R : duration) (j : Job),
      arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
    ∀ A_sp : duration, A_sp ≤ job_arrival j - t1 →
      are_equivalent_at_values_less_than (IBF_P (job_arrival j - t1)) (IBF_P A_sp) L →
    ∀ F : duration, task_rtct tsk + IBF_P A_sp F ≤ F →
      task_cost tsk + IBF_NP F (A_sp + R) ≤ A_sp + R →
      t1 + F < t2 → t1 + (A_sp + R) < t2 →
      completed_by sched j (job_arrival j + R) = true := by
  intro hvalid ts tsk hts _ _ hwc L hL IBF_P hP IBF_NP hNP hge R j ha hjt hpos t1 t2 hbi A_sp hA
    heq F hfix hfix2 hF hF2
  have harr := job_arrival_eq_t1_plus_A sched j t1 t2 hbi
  rcases Nat.le_total (job_cost j) (task_rtct tsk) with hsmall | hbig
  · have h1 := job_receives_enough_service_1 arr_seq sched ts tsk hts hwc L hL IBF_P hP IBF_NP R j
      ha hjt hpos t1 t2 hbi A_sp hA heq F hfix hfix2 hF hF2 hsmall
    have hg := hge F (A_sp + R)
    refine completion_monotonic sched j (t1 + F) _ (by omega') ?_
    unfold completed_by
    exact decide_eq_true h1
  · have h3 := job_receives_enough_service_3 arr_seq sched hvalid ts tsk hts hwc L hL IBF_P hP
      IBF_NP hNP R j ha hjt hpos t1 t2 hbi A_sp hA heq F hfix hfix2 hF hF2 hbig
    refine completion_monotonic sched j (t1 + (A_sp + R)) _ (by omega') ?_
    unfold completed_by
    exact decide_eq_true h3

theorem uniprocessor_response_time_bound {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [TaskRunToCompletionThreshold Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
    ∀ [Interference Job] [InterferingWorkload Job],
    work_conserving arr_seq sched →
    ∀ L : duration, busy_intervals_are_bounded_by arr_seq sched tsk L →
    ∀ IBF_P : duration → duration → duration,
      job_interference_is_bounded_by arr_seq sched tsk IBF_P
        (relative_arrival_time_of_job_is_A sched) →
    ∀ IBF_NP : duration → duration → duration,
      job_interference_is_bounded_by arr_seq sched tsk IBF_NP
        (relative_time_to_reach_rtct sched tsk IBF_P) →
      (∀ (F : Nat) (Δ : duration), F ≤ task_cost tsk + IBF_NP F Δ) →
    ∀ R : duration,
      (∀ A : duration, is_in_search_space L IBF_P A →
        ∃ F : duration, task_rtct tsk + IBF_P A F ≤ F ∧
          task_cost tsk + IBF_NP F (A + R) ≤ A + R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hvalid ts tsk hts _ _ hwc L hL IBF_P hP IBF_NP hNP hge R hmax j ha hjt
  unfold job_response_time_bound
  rcases Nat.eq_zero_or_pos (job_cost j) with hzero | hpos'
  · unfold completed_by
    exact decide_eq_true (by omega')
  have hpos : job_cost_positive j = true := decide_eq_true hpos'
  obtain ⟨t1, t2, _, _, hbi⟩ := hL j ha hjt hpos'
  have hAL := relative_arrival_is_bounded arr_seq sched tsk L hL j ha hjt hpos t1 t2 hbi
  obtain ⟨A_sp, hA, heq, hsp⟩ := representative_exists L IBF_P (job_arrival j - t1) hAL
  obtain ⟨F, hfix, hfix2⟩ := hmax A_sp hsp
  rcases Nat.lt_or_ge (t1 + F) t2 with hF | hF
  · rcases Nat.lt_or_ge (t1 + (A_sp + R)) t2 with hF2 | hF2
    · exact job_is_completed_by_arrival_plus_R arr_seq sched hvalid ts tsk hts hwc L hL IBF_P hP
        IBF_NP hNP hge R j ha hjt hpos t1 t2 hbi A_sp hA heq F hfix hfix2 hF hF2
    · exact job_completed_by_arrival_plus_R_2 sched R j t1 t2 hbi A_sp hA hF2
  · exact job_completed_by_arrival_plus_R_1 sched tsk IBF_NP hge R j t1 t2 hbi A_sp hA F hfix2 hF

end AbstractRta

end Prosa.Analysis.Abstract.AbstractRta
