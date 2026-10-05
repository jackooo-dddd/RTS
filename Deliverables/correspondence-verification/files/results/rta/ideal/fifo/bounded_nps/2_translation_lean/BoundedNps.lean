-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ideal/fifo/bounded_nps.v

import Prosa.Model.Readiness.Basic
import Prosa.Analysis.Facts.Priority.Fifo
import Prosa.Analysis.Facts.Priority.FifoAhepBound
import Prosa.Analysis.Abstract.Ideal.CumulativeBounds
import Prosa.Analysis.Abstract.Ideal.AbstractRta
import Prosa.Analysis.Facts.Model.TaskCost
import Prosa.Analysis.Facts.Readiness.Basic

namespace Prosa.Results.Rta.Ideal.Fifo.BoundedNps

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Fifo
open Prosa.Model.Processor.Ideal
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Util.Sum
open Prosa.Util.Notation
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.Priority.Fifo
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.AbstractRta
open Prosa.Analysis.Abstract.Ideal.IwInstantiation
open Prosa.Analysis.Abstract.Ideal.AbstractRta

/-! Abstract RTA for FIFO schedulers on ideal uniprocessors.

Binders follow the elaborated source types: every declaration takes only the section inputs and hypotheses it uses,
in their elaborated order; instance inputs quantified after a hypothesis are `∀ [..]` binders at that position. The
section's readiness (the accepted `basic_ready_instance`) and the FIFO policy (the accepted `FIFO` instance) are passed
explicitly where the elaborated statements use them implicitly; the section-local instances
`ideal_jlfp_interference` / `ideal_jlfp_interfering_workload` are the accepted `iw_instantiation` definitions at that
policy. The section-local `work_conserving_ab`, `busy_windows_are_bounded_by`, `IBF`, `bound_on_hep_workload` and
`is_in_abstract_search_space` are inlined; `\sum_(tsko <- ts) F tsko` is the accepted `sumSeq ts F`. Representation:
`ε` is `1`; a Boolean in `Prop` position is `= true`; `a != b` is `decide (a ≠ b)`; `has p xs` is `xs.any p`;
`tsk \in ts` is `decide (tsk ∈ ts) = true`; `search_space.is_in_search_space` is the accepted abstract search-space
predicate. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- The instantiated interference and interfering workload are abstractly work-conserving. -/
theorem abstractly_work_conserving [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
      @Prosa.Analysis.Abstract.Definitions.work_conserving Job _
        (@ideal_jlfp_interference Job _ arr_seq sched (FIFO Job))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (FIFO Job)) _ _ (processor_state Job) arr_seq sched := by
  intro hva sched hvs hwc
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  have hrefl : reflexive_job_priorities (FIFO Job) := FIFO_is_reflexive
  exact instantiated_i_and_w_are_coherent_with_schedule arr_seq hva sched hvs.1
    (jobs_must_arrive_to_be_ready sched hvs.2) (completed_jobs_are_not_ready sched hvs.2) hrefl
    (basic_readiness_is_work_bearing_readiness arr_seq sched hrefl) hwc hrefl

/-- Every busy window is bounded by `L`. -/
theorem busy_windows_are_bounded [TaskCost Task] [MaxArrivals Task] [JobTask Job Task] [JobArrival Job]
    [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
    ∀ (tsk : Task) (sched : schedule (processor_state Job)),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
    ∀ L : duration, 0 < L → L = total_request_bound_function ts L →
      @busy_intervals_are_bounded_by Job _ (@ideal_jlfp_interference Job _ arr_seq sched (FIFO Job))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (FIFO Job)) _ _ (processor_state Job)
        arr_seq sched Task _ _ tsk L := by
  intro hva hvjc ts hall hresp tsk sched hvs hwc L hL hfix
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  have hrefl : reflexive_job_priorities (FIFO Job) := FIFO_is_reflexive
  exact Prosa.Analysis.Abstract.Ideal.IwInstantiation.instantiated_busy_intervals_are_bounded arr_seq hva sched hvs.1
    (jobs_must_arrive_to_be_ready sched hvs.2) (completed_jobs_are_not_ready sched hvs.2) hrefl tsk
    (basic_readiness_is_work_bearing_readiness arr_seq sched hrefl) hwc ts hresp hall L hL hfix hvjc

/-- FIFO incurs no priority inversion inside the busy interval. -/
theorem no_priority_inversion [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ (tsk : Task) (sched : schedule (processor_state Job)),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq sched
        (FIFO Job) →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : duration,
      @Prosa.Analysis.Abstract.Definitions.busy_interval Job _
        (@ideal_jlfp_interference Job _ arr_seq sched (FIFO Job))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (FIFO Job)) _ _ (processor_state Job) sched j t1 t2 →
    ∀ Δ : duration, t1 + Δ < t2 →
      @cumulative_priority_inversion Job _ (processor_state Job) arr_seq sched (FIFO Job) j t1 (t1 + Δ) = 0 := by
  intro hva tsk sched hvs hvpm hresp j hj htsk hcp t1 t2 hbi Δ hlt
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  have hrefl : reflexive_job_priorities (FIFO Job) := FIFO_is_reflexive
  have h := Prosa.Analysis.Abstract.Ideal.CumulativeBounds.cumulative_priority_inversion_is_bounded (Task := Task)
    hrefl arr_seq hva sched hvs tsk j hj htsk hcp t1 t2 hbi Δ (Nat.le_of_lt hlt) (constant 0)
    (FIFO_implies_no_pi arr_seq hva (processor_state Job) (ideal_proc_model_is_a_uniprocessor_model Job) sched hvs
      hvpm hresp tsk hvs)
  exact Nat.le_zero.mp h

/-- The FIFO interference bound. -/
theorem IBF_correct [TaskCost Task] [MaxArrivals Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    [JobPreemptable Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
      valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq sched
        (FIFO Job) →
    ∀ L : duration, 0 < L → L = total_request_bound_function ts L →
      @job_interference_is_bounded_by Job _ (@ideal_jlfp_interference Job _ arr_seq sched (FIFO Job))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (FIFO Job)) _ _ (processor_state Job) arr_seq sched
        Task _ _ tsk
        (fun A _ => sumSeq ts (fun tsko => task_request_bound_function tsko (A + 1)) - task_cost tsk)
        (@relative_arrival_time_of_job_is_A Job _ _ _ (processor_state Job) sched
          (@ideal_jlfp_interference Job _ arr_seq sched (FIFO Job))
          (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (FIFO Job))) := by
  intro hva hvjc ts hall hresp hvalid tsk hin sched hvs hvpm hrespF L _ _ t1 t2 Δ j hj htsk hbi hlt hncomp A hA
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := FIFO Job
  have hrefl : reflexive_job_priorities (FIFO Job) := FIFO_is_reflexive
  have hfrom := hvs.1
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hpos : 0 < job_cost j := by
    rcases Nat.eq_zero_or_pos (job_cost j) with h0 | h
    · exfalso
      unfold completed_by at hncomp
      rw [h0] at hncomp
      simp at hncomp
    · exact h
  have hcp : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hpos
  have hA' : A = job_arrival j - t1 := hA t1 t2 hbi
  subst hA'
  have hsplit := cumulative_interference_split arr_seq hva sched hfrom hmust hrefl j t1 (t1 + Δ)
  have hpi := no_priority_inversion arr_seq hva tsk sched hvs hvpm hrespF j hj htsk hcp t1 t2 hbi Δ hlt
  have hcl := (instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hfrom hmust hcde hrefl j hj hcp
    t1 t2).mpr hbi
  have hbd := Prosa.Analysis.Facts.Priority.FifoAhepBound.bound_on_hep_workload
    (ideal_proc_model_is_a_uniprocessor_model Job) (ideal_proc_model_provides_unit_supply Job) arr_seq hva hvjc ts
    hall hresp hvalid tsk hin sched hmust hcde j htsk hj hcp t1 t2 hcl Δ hlt
  show @cumulative_interference Job _ (ideal_jlfp_interference arr_seq sched) j t1 (t1 + Δ) ≤ _
  rw [hsplit, hpi, Nat.zero_add]
  exact hbd

/-- The concrete FIFO search space: offsets below `L` at which the RBF of some task steps. -/
def is_in_concrete_search_space [TaskCost Task] [MaxArrivals Task] (ts : List Task) (L A : duration) : Bool :=
  decide (A < L) &&
    ts.any (fun tsk' => decide (task_request_bound_function tsk' A ≠ task_request_bound_function tsk' (A + 1)))

/-- Any offset of the abstract search space is in the concrete FIFO search space. -/
theorem search_space_refinement [TaskCost Task] [MaxArrivals Task] (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ L : duration, 0 < L → 0 < task_cost tsk → 0 < max_arrivals tsk 1 →
    ∀ A : Nat,
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
          (fun A0 _ => sumSeq ts (fun tsko => task_request_bound_function tsko (A0 + 1)) - task_cost tsk) A →
        is_in_concrete_search_space ts L A = true := by
  intro hv tsk hin L hL hc hpos A h
  unfold is_in_concrete_search_space
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rcases h with hA | ⟨hA0, hAL, x, _, hne⟩
  · subst hA
    refine ⟨hL, ?_⟩
    rw [List.any_eq_true]
    refine ⟨tsk, of_decide_eq_true hin, ?_⟩
    have h0 := task_rbf_0_zero tsk (hv tsk hin)
    have h1 := task_rbf_epsilon_gt_0 tsk hc hpos
    apply decide_eq_true
    rw [h0, Nat.zero_add]
    exact Nat.ne_of_lt h1
  · refine ⟨hAL, ?_⟩
    by_contra hcon
    rw [Bool.not_eq_true, List.any_eq_false] at hcon
    apply hne
    have hA1 : A - 1 + 1 = A := Nat.sub_add_cancel hA0
    show sumSeq ts (fun tsko => task_request_bound_function tsko (A - 1 + 1)) - task_cost tsk =
      sumSeq ts (fun tsko => task_request_bound_function tsko (A + 1)) - task_cost tsk
    rw [hA1]
    congr 1
    unfold sumSeq
    congr 1
    apply List.map_congr_left
    intro t ht
    have := hcon t ht
    simp only [decide_eq_true_eq, not_not] at this
    exact this

/-- Every offset of the abstract search space has a solution of the response-time recurrence. -/
theorem soln_abstract_response_time_recurrence [TaskCost Task] [MaxArrivals Task] [TaskRunToCompletionThreshold Task]
    [JobTask Job Task] [JobCost Job] [JobPreemptable Job] (arr_seq : arrival_sequence Job) (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ L : duration, 0 < L → L = total_request_bound_function ts L →
    ∀ R : duration,
      (∀ A : duration, is_in_concrete_search_space ts L A = true →
        ∃ F : Nat, sumSeq ts (fun tsko => task_request_bound_function tsko (A + 1)) ≤ A + F ∧ F ≤ R) →
      0 < task_cost tsk → 0 < max_arrivals tsk 1 →
    ∀ A : Nat,
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
          (fun A0 _ => sumSeq ts (fun tsko => task_request_bound_function tsko (A0 + 1)) - task_cost tsk) A →
        ∃ F : Nat,
          task_rtct tsk + (sumSeq ts (fun tsko => task_request_bound_function tsko (A + 1)) - task_cost tsk) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R := by
  intro hv tsk hin hrtct L hL _ R hR hc hpos A hA
  obtain ⟨F, hF, hFR⟩ := hR A (search_space_refinement ts hv tsk hin L hL hc hpos A hA)
  obtain ⟨F0, hF0, hF0R⟩ := hR 0 (search_space_refinement ts hv tsk hin L hL hc hpos 0 (Or.inl rfl))
  have hsum0 := task_cost_le_sum_rbf tsk (hv tsk hin) hpos ts hin (0 + 1) (by omega)
  have hsum := task_cost_le_sum_rbf tsk (hv tsk hin) hpos ts hin (A + 1) (by omega)
  have hrt : task_rtct tsk ≤ task_cost tsk := of_decide_eq_true hrtct.1
  unfold total_request_bound_function at hsum0 hsum
  refine ⟨R - (task_cost tsk - task_rtct tsk), ?_, ?_⟩ <;> omega'

/-- Response-time bound for FIFO schedulers on ideal uniprocessors. -/
theorem uniprocessor_response_time_bound_FIFO [TaskCost Task] [MaxArrivals Task] [TaskRunToCompletionThreshold Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
      valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true → valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq sched
        (FIFO Job) →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
    ∀ L : duration, 0 < L → L = total_request_bound_function ts L →
    ∀ R : duration,
      (∀ A : duration, is_in_concrete_search_space ts L A = true →
        ∃ F : Nat, sumSeq ts (fun tsko => task_request_bound_function tsko (A + 1)) ≤ A + F ∧ F ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hva hvjc ts hall hresp hvalid tsk hin hrtct sched hvs hvpm hrespF hwc L hL hfix R hR js harrs htsks
  rcases Nat.eq_zero_or_pos (job_cost js) with h0 | hjpos
  · unfold job_response_time_bound completed_by
    apply decide_eq_true; rw [h0]; exact Nat.zero_le _
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := FIFO Job
  have htsk : job_task (Task := Task) js = tsk := of_decide_eq_true htsks
  have hma := non_pathological_max_arrivals tsk arr_seq (hresp tsk hin) js htsks harrs
  have hcpos : 0 < task_cost tsk := by
    have hv := hvjc js harrs
    unfold valid_job_cost at hv
    rw [htsk] at hv
    exact Nat.lt_of_lt_of_le hjpos (of_decide_eq_true hv)
  let _ := ideal_jlfp_interference arr_seq sched
  let _ := ideal_jlfp_interfering_workload arr_seq sched
  exact uniprocessor_response_time_bound_ideal (ideal_proc_model_ensures_ideal_progress Job)
    (ideal_proc_model_provides_unit_service Job) arr_seq sched (jobs_must_arrive_to_be_ready sched hvs.2)
    (completed_jobs_are_not_ready sched hvs.2) hvjc ts tsk hin hvpm hrtct
    (abstractly_work_conserving arr_seq hva sched hvs hwc) L
    (busy_windows_are_bounded arr_seq hva hvjc ts hall hresp tsk sched hvs hwc L hL hfix) _
    (IBF_correct arr_seq hva hvjc ts hall hresp hvalid tsk hin sched hvs hvpm hrespF L hL hfix) R
    (fun A hA => soln_abstract_response_time_recurrence arr_seq ts hvalid tsk hin hrtct L hL hfix R hR hcpos hma A hA)
    js harrs htsks

end Prosa.Results.Rta.Ideal.Fifo.BoundedNps
