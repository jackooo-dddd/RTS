-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ideal/edf/bounded_nps.v

import Prosa.Model.Readiness.Basic
import Prosa.Analysis.Facts.BusyInterval.PiBound
import Prosa.Analysis.Facts.BusyInterval.Arrival
import Prosa.Results.Rta.Ideal.Edf.BoundedPi
import Prosa.Model.Schedule.WorkConserving
import Prosa.Analysis.Definitions.BusyInterval.Classical
import Prosa.Analysis.Facts.BlockingBound.Edf
import Prosa.Analysis.Facts.Workload.EdfAthepBound

namespace Prosa.Results.Rta.Ideal.Edf.BoundedNps

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.AbsoluteDeadline
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Edf
open Prosa.Model.Processor.Ideal
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Util.Minmax
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.BlockingBound.Edf
open Prosa.Analysis.Definitions.Workload.EdfAthepBound
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Arrivals

/-! RTA for EDF schedulers with bounded nonpreemptive segments on ideal uniprocessors.

Binders follow the elaborated source types: every declaration takes only the section inputs and hypotheses it uses,
in their elaborated order; instance inputs quantified after a hypothesis are `∀ [..]` binders at that position. The
section's readiness (the accepted `basic_ready_instance`) and the EDF policy (the accepted `EDF` instance over the
accepted `job_deadline_from_task_deadline`) are passed explicitly where the elaborated statements use them
implicitly. The section-local `D`, `EDF`, `rbf`, `task_rbf`, `total_rbf` and `response_time_bounded_by` are inlined;
`edf.bounded_pi.*` are the accepted definitions of `Prosa.Results.Rta.Ideal.Edf.BoundedPi`, `edf.blocking_bound` the
accepted EDF blocking bound and `edf_athep_bound.bound_on_athep_workload` the accepted EDF athep bound.
Representation: `ε` is `1`; a Boolean in `Prop` position is `= true`; `a != b` is `decide (a ≠ b)`; `a == b` is
`decide (a = b)`; `x \in xs` is `decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- The EDF search space with bounded nonpreemptive segments: offsets below `L` at which the RBF of `tsk` or the
bound on the higher-or-equal-priority workload changes. -/
def is_in_search_space [TaskCost Task] [TaskDeadline Task] (ts : List Task) [MaxArrivals Task] (tsk : Task)
    (L A : duration) : Bool :=
  decide (A < L) &&
    (Prosa.Results.Rta.Ideal.Edf.BoundedPi.task_rbf_changes_at tsk A ||
      Prosa.Results.Rta.Ideal.Edf.BoundedPi.bound_on_total_hep_workload_changes_at ts tsk A)

/-- The EDF blocking bound is non-increasing in the offset. -/
theorem blocking_bound_decreasing [TaskCost Task] [TaskDeadline Task] [TaskMaxNonpreemptiveSegment Task]
    (ts : List Task) [MaxArrivals Task] (tsk : Task) :
    decide (tsk ∈ ts) = true →
    ∀ A1 A2 : Nat, A1 ≤ A2 → blocking_bound ts tsk A2 ≤ blocking_bound ts tsk A1 := by
  intro _ A1 A2 hle
  unfold blocking_bound
  apply bigmax_subset
  intro x _ hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
  exact ⟨hx.1, by omega'⟩

/-- A change of the blocking bound at `A` is caused by a relevant task whose deadline is exactly `A` later. -/
theorem task_with_equal_deadline_exists [TaskCost Task] [TaskDeadline Task] [TaskMaxNonpreemptiveSegment Task]
    (ts : List Task) [MaxArrivals Task] (tsk : Task) :
    decide (tsk ∈ ts) = true →
    ∀ A : duration,
      Prosa.Results.Rta.Ideal.Edf.BoundedPi.priority_inversion_changes_at (blocking_bound ts tsk) A = true →
      ∃ tsk_o : Task,
        (decide (tsk_o ∈ ts) && blocking_relevant tsk_o && decide (tsk_o ≠ tsk) &&
          decide (task_deadline tsk_o = task_deadline tsk + A)) = true := by
  intro hin A hch
  unfold Prosa.Results.Rta.Ideal.Edf.BoundedPi.priority_inversion_changes_at at hch
  have hne := of_decide_eq_true hch
  have hA : 0 < A := by
    rcases Nat.eq_zero_or_pos A with h0 | h
    · exfalso; apply hne; rw [h0]
    · exact h
  have hle := blocking_bound_decreasing ts tsk hin (A - 1) A (by omega')
  have hlt : blocking_bound ts tsk A < blocking_bound ts tsk (A - 1) := by
    have : blocking_bound ts tsk A ≠ blocking_bound ts tsk (A - 1) := fun h => hne h.symm
    omega'
  unfold blocking_bound at hlt
  obtain ⟨x, hx, hP1, hP2⟩ := bigmax_witness_diff hlt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP2
  have hrel := hP2.1
  have hD : task_deadline x = task_deadline tsk + A := by
    have : ¬ task_deadline tsk + A < task_deadline x := by
      intro h; rw [hrel] at hP1; simp only [Bool.true_and, decide_eq_false_iff_not] at hP1; exact hP1 h
    have := hP2.2
    omega'
  refine ⟨x, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hx, hrel⟩, ?_⟩, hD⟩
  intro hxt
  rw [hxt] at hD
  omega'

/-- The accepted EDF bounded-priority-inversion search space at the blocking bound is included in this search
space. -/
theorem search_space_inclusion [TaskCost Task] [TaskDeadline Task] [TaskMaxNonpreemptiveSegment Task]
    (ts : List Task) [MaxArrivals Task] :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ A L : duration,
      Prosa.Results.Rta.Ideal.Edf.BoundedPi.is_in_search_space ts tsk (blocking_bound ts tsk) L A = true →
      is_in_search_space ts tsk L A = true := by
  intro hv tsk hin A L h
  unfold Prosa.Results.Rta.Ideal.Edf.BoundedPi.is_in_search_space at h
  unfold is_in_search_space
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨hAL, hstep⟩ := h
  refine ⟨hAL, ?_⟩
  rcases hstep with (hpi | hrbf) | hbnd
  · right
    obtain ⟨tsk_o, ho⟩ := task_with_equal_deadline_exists ts tsk hin A hpi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨⟨⟨hin_o, hrel⟩, hne⟩, hD⟩ := ho
    unfold blocking_relevant at hrel
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrel
    unfold Prosa.Results.Rta.Ideal.Edf.BoundedPi.bound_on_total_hep_workload_changes_at
    rw [List.any_eq_true]
    refine ⟨tsk_o, hin_o, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨fun e => hne e.symm, ?_⟩
    have h0 : A + task_deadline tsk - task_deadline tsk_o = 0 := by omega'
    have h1 : A + 1 + task_deadline tsk - task_deadline tsk_o = 1 := by omega'
    rw [h0, h1]
    unfold task_request_bound_function
    rw [(hv tsk_o (decide_eq_true hin_o)).1, Nat.mul_zero]
    exact Nat.ne_of_lt (Nat.mul_pos hrel.2 hrel.1)
  · exact Or.inl hrbf
  · exact Or.inr hbnd

/-- Response-time bound for EDF schedulers with bounded nonpreemptive segments on ideal uniprocessors. -/
theorem uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments [TaskCost Task]
    [TaskDeadline Task] [TaskRunToCompletionThreshold Task] [TaskMaxNonpreemptiveSegment Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
    ∀ [JobPreemptable Job], valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ [MaxArrivals Task], valid_taskset_arrival_curve ts max_arrivals → taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
      valid_preemption_model arr_seq sched →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ L : duration, 0 < L → L = total_request_bound_function ts L →
    ∀ R : duration,
      (∀ A : duration, is_in_search_space ts tsk L A = true →
        ∃ F : duration,
          blocking_bound ts tsk A + (task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk)) +
              bound_on_athep_workload ts tsk A (A + F) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hva sched hvs _ hvm hwc hrespE ts hall hvjc _ hvalid hresp tsk hin hvpm hrtct L hL hfix R hR
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  have hreflE : reflexive_job_priorities (@EDF Job _ (job_deadline_from_task_deadline Job Task)) :=
    EDF_is_reflexive
  have htransE : transitive_job_priorities (@EDF Job _ (job_deadline_from_task_deadline Job Task)) :=
    EDF_is_transitive
  have hwb := basic_readiness_is_work_bearing_readiness arr_seq sched hreflE
  have hpib := Prosa.Analysis.Facts.BusyInterval.PiBound.priority_inversion_is_bounded (Task := Task) arr_seq hva
    sched (@EDF Job _ (job_deadline_from_task_deadline Job Task)) htransE hvm hwb hvs hrespE hvpm tsk
    (blocking_bound ts tsk) (ideal_proc_model_is_a_uniprocessor_model Job)
    (ideal_proc_model_provides_unit_service Job) (ideal_proc_model_ensures_ideal_progress Job)
    (fun j t1 t2 _ hjt hbip =>
      Prosa.Analysis.Facts.BlockingBound.Edf.nonpreemptive_segments_bounded_by_blocking arr_seq hva sched hvjc
        hvm ts hall tsk hin hresp j hjt t1 t2 hbip)
  exact Prosa.Results.Rta.Ideal.Edf.BoundedPi.uniprocessor_response_time_bound_edf arr_seq hva sched hvs hrespE hwc
    hvjc ts hall hvalid hresp tsk hin hvpm hrtct (blocking_bound ts tsk) hpib L hL hfix R
    (fun A hA => hR A (search_space_inclusion ts hvalid tsk hin A L hA))

end Prosa.Results.Rta.Ideal.Edf.BoundedNps
