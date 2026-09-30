-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ideal/edf/bounded_pi.v

import Prosa.Analysis.Facts.Priority.Edf
import Prosa.Analysis.Definitions.Schedulability
import Prosa.Model.Readiness.Basic
import Prosa.Model.Priority.Edf
import Prosa.Model.Task.AbsoluteDeadline
import Prosa.Analysis.Abstract.Ideal.CumulativeBounds
import Prosa.Analysis.Facts.BusyInterval.CarryIn
import Prosa.Analysis.Facts.Readiness.Basic
import Prosa.Analysis.Abstract.Ideal.AbstractSeqRta
import Prosa.Analysis.Facts.Model.TaskCost
import Prosa.Analysis.Facts.Workload.EdfAthepBound

namespace Prosa.Results.Rta.Ideal.Edf.BoundedPi

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Task.AbsoluteDeadline
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Edf
open Prosa.Model.Processor.Ideal
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.Workload.EdfAthepBound
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.Priority.Edf
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.IBF.Task
open Prosa.Analysis.Abstract.Ideal.IwInstantiation
open Prosa.Analysis.Abstract.Ideal.AbstractSeqRta

/-! Abstract RTA for EDF schedulers with bounded priority inversion on ideal uniprocessors.

Binders follow the elaborated source types: every declaration takes only the section inputs and hypotheses it uses,
in their elaborated order; instance inputs quantified after a hypothesis are `∀ [..]` binders at that position. The
section's readiness (the accepted `basic_ready_instance`) and the EDF policy (the accepted `EDF` instance over the
accepted `job_deadline_from_task_deadline`) are passed explicitly where the elaborated statements use them
implicitly; the section-local instances `ideal_jlfp_interference` / `ideal_jlfp_interfering_workload` are the accepted
`iw_instantiation` definitions at that policy. The section-local `D`, `EDF`, `rbf`, `task_rbf`, `total_rbf`,
`task_IBF` and `total_interference_bound` are inlined. Representation: `ε` is `1`; a Boolean in `Prop` position is
`= true`; `a != b` is `decide (a ≠ b)`; `has p xs` is `xs.any p`; `tsk \in ts` is `decide (tsk ∈ ts) = true`;
`search_space.is_in_search_space` is the accepted abstract search-space predicate and `bound_on_athep_workload` the
accepted EDF athep bound. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- The RBF of `tsk` steps at `A`. -/
def task_rbf_changes_at [TaskCost Task] [MaxArrivals Task] (tsk : Task) (A : duration) : Bool :=
  decide (task_request_bound_function tsk A ≠ task_request_bound_function tsk (A + 1))

/-- The bound on the higher-or-equal-priority workload of another task steps at `A`. -/
def bound_on_total_hep_workload_changes_at [TaskCost Task] [TaskDeadline Task] (ts : List Task) [MaxArrivals Task]
    (tsk : Task) (A : Nat) : Bool :=
  ts.any (fun tsko => decide (tsk ≠ tsko) &&
    decide (task_request_bound_function tsko (A + task_deadline tsk - task_deadline tsko) ≠
      task_request_bound_function tsko (A + 1 + task_deadline tsk - task_deadline tsko)))

/-- The priority-inversion bound steps at `A`. -/
def priority_inversion_changes_at (priority_inversion_bound : duration → duration) (A : duration) : Bool :=
  decide (priority_inversion_bound (A - 1) ≠ priority_inversion_bound A)

/-- The EDF search space: offsets below `L` at which the priority-inversion bound, the RBF of `tsk` or the bound on
the higher-or-equal-priority workload changes. -/
def is_in_search_space [TaskCost Task] [TaskDeadline Task] (ts : List Task) [MaxArrivals Task] (tsk : Task)
    (priority_inversion_bound : duration → duration) (L A : duration) : Bool :=
  decide (A < L) &&
    (priority_inversion_changes_at priority_inversion_bound A || task_rbf_changes_at tsk A ||
      bound_on_total_hep_workload_changes_at ts tsk A)

/-- The priority-inversion bound plus the EDF athep bound bounds the task interference. -/
theorem instantiated_task_interference_is_bounded [TaskCost Task] [TaskDeadline Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
    ∀ [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
    ∀ (tsk : Task) (priority_inversion_bound : duration → duration),
      @priority_inversion_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) tsk priority_inversion_bound →
      @task_interference_is_bounded_by Job _ Task _ _ _ _ (processor_state Job) arr_seq sched tsk
        (@ideal_jlfp_interference Job _ arr_seq sched (@EDF Job _ (job_deadline_from_task_deadline Job Task)))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (@EDF Job _ (job_deadline_from_task_deadline Job Task)))
        (fun A R => priority_inversion_bound A + bound_on_athep_workload ts tsk A R) := by
  intro hva sched hvs hvjc ts hall _ hresp tsk pib hpib t1 t2 Δ j hj htsk hbi hlt hncomp A hA
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := @EDF Job _ (job_deadline_from_task_deadline Job Task)
  have hreflE : reflexive_job_priorities (@EDF Job _ (job_deadline_from_task_deadline Job Task)) :=
    EDF_is_reflexive
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
  have hcl := (instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hfrom hmust hcde hreflE j hj
    hcp t1 t2).mpr hbi
  have hsplit := cumulative_task_interference_split arr_seq hva sched hfrom hmust hreflE tsk j t1 (t1 + Δ) hj htsk
    hncomp
  have hpi := Prosa.Analysis.Abstract.Ideal.CumulativeBounds.cumulative_priority_inversion_is_bounded hreflE arr_seq
    hva sched hvs tsk j hj htsk hcp t1 t2 hbi Δ (Nat.le_of_lt hlt) pib hpib
  have hsvc := Prosa.Analysis.Abstract.Ideal.CumulativeBounds.cumulative_interference_is_bounded_by_total_service
    hreflE arr_seq hva sched hvs tsk j hj htsk hcp t1 t2 hbi Δ
  have hwl := service_of_jobs_le_workload (ideal_proc_model_provides_unit_service Job) sched hcde
    (fun jo => another_task_hep_job (Task := Task) jo j) (arrivals_between arr_seq t1 (t1 + Δ)) t1 (t1 + Δ)
  have hbd := Prosa.Analysis.Facts.Workload.EdfAthepBound.bound_on_athep_workload_is_valid arr_seq hva hvjc ts hall
    hresp tsk sched j t1 Δ hcp htsk hcl.1.2.1
  refine Nat.le_trans hsplit ?_
  show _ ≤ pib (job_arrival j - t1) + bound_on_athep_workload ts tsk (job_arrival j - t1) Δ
  omega'

/-- Any offset of the abstract search space is in the concrete EDF search space. -/
theorem A_is_in_concrete_search_space [TaskCost Task] [TaskDeadline Task] (ts : List Task) [MaxArrivals Task] :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ (priority_inversion_bound : duration → duration) (L : duration), 0 < L →
      L = total_request_bound_function ts L → 0 < task_cost tsk → 0 < max_arrivals tsk 1 →
    ∀ A : duration,
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
          (fun A0 Δ : duration =>
            task_request_bound_function tsk (A0 + 1) - task_cost tsk +
              (priority_inversion_bound A0 + bound_on_athep_workload ts tsk A0 Δ)) A →
        is_in_search_space ts tsk priority_inversion_bound L A = true := by
  intro hv tsk hin pib L hL _ hc hpos A h
  unfold is_in_search_space priority_inversion_changes_at task_rbf_changes_at
    bound_on_total_hep_workload_changes_at
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  rcases h with hA | ⟨hA0, hAL, x, _, hne⟩
  · subst hA
    have h0 := task_rbf_0_zero tsk (hv tsk hin)
    have h1 := task_rbf_epsilon_gt_0 tsk hc hpos
    refine ⟨hL, Or.inl (Or.inr ?_)⟩
    rw [h0, Nat.zero_add]
    exact Nat.ne_of_lt h1
  · refine ⟨hAL, ?_⟩
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨⟨hpi, hrbf⟩, hany⟩ := hcon
    apply hne
    have hA1 : A - 1 + 1 = A := Nat.sub_add_cancel hA0
    show task_request_bound_function tsk (A - 1 + 1) - task_cost tsk +
        (pib (A - 1) + bound_on_athep_workload ts tsk (A - 1) x) =
      task_request_bound_function tsk (A + 1) - task_cost tsk +
        (pib A + bound_on_athep_workload ts tsk A x)
    rw [hA1, hrbf, hpi]
    congr 2
    unfold bound_on_athep_workload
    apply eq_sum_seq
    intro tsko hin' hneq
    apply decide_eq_true
    have hne' : tsk ≠ tsko := fun e => (of_decide_eq_true hneq) e.symm
    have heq : task_request_bound_function tsko (A + task_deadline tsk - task_deadline tsko) =
        task_request_bound_function tsko (A + 1 + task_deadline tsk - task_deadline tsko) := by
      by_contra hd
      apply hany
      rw [List.any_eq_true]
      exact ⟨tsko, hin', by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hne', hd⟩⟩
    rw [hA1]
    by_cases hx1 : x ≤ A + task_deadline tsk - task_deadline tsko
    · rw [Nat.min_eq_right hx1, Nat.min_eq_right (by omega')]
    · by_cases hx2 : A + 1 + task_deadline tsk - task_deadline tsko ≤ x
      · rw [Nat.min_eq_left (by omega'), Nat.min_eq_left hx2]
        exact heq
      · exfalso
        omega'

/-- Every offset of the abstract search space has a solution of the response-time recurrence. -/
theorem correct_search_space [TaskCost Task] [TaskDeadline Task] [TaskRunToCompletionThreshold Task]
    (ts : List Task) [MaxArrivals Task] :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ (priority_inversion_bound : duration → duration) (L : duration), 0 < L →
      L = total_request_bound_function ts L →
    ∀ R : duration,
      (∀ A : duration, is_in_search_space ts tsk priority_inversion_bound L A = true →
        ∃ F : duration,
          priority_inversion_bound A + (task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk)) +
              bound_on_athep_workload ts tsk A (A + F) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R) →
      0 < task_cost tsk → 0 < max_arrivals tsk 1 →
    ∀ A : duration,
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
          (fun A0 Δ : duration =>
            task_request_bound_function tsk (A0 + 1) - task_cost tsk +
              (priority_inversion_bound A0 + bound_on_athep_workload ts tsk A0 Δ)) A →
        ∃ F : Nat,
          task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk) +
              (priority_inversion_bound A + bound_on_athep_workload ts tsk A (A + F)) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R := by
  intro hv tsk hin pib L hL hfix R hR hc hpos A hA
  obtain ⟨F, hF, hFR⟩ := hR A (A_is_in_concrete_search_space ts hv tsk hin pib L hL hfix hc hpos A hA)
  exact ⟨F, by omega', hFR⟩

/-- Response-time bound for EDF schedulers with bounded priority inversion on ideal uniprocessors. -/
theorem uniprocessor_response_time_bound_edf [TaskCost Task] [TaskDeadline Task] [TaskRunToCompletionThreshold Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
    ∀ [MaxArrivals Task], valid_taskset_arrival_curve ts max_arrivals → taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
      valid_preemption_model arr_seq sched →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ priority_inversion_bound : duration → duration,
      @priority_inversion_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) tsk priority_inversion_bound →
    ∀ L : duration, 0 < L → L = total_request_bound_function ts L →
    ∀ R : duration,
      (∀ A : duration, is_in_search_space ts tsk priority_inversion_bound L A = true →
        ∃ F : duration,
          priority_inversion_bound A + (task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk)) +
              bound_on_athep_workload ts tsk A (A + F) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hva sched hvs hrespE hwc hvjc ts hall _ hvalid hresp tsk hin hvpm hrtct pib hpib L hL hfix R hR js harrs htsks
  rcases Nat.eq_zero_or_pos (job_cost js) with h0 | hjpos
  · unfold job_response_time_bound completed_by
    apply decide_eq_true; rw [h0]; exact Nat.zero_le _
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JLFP_policy Job := @EDF Job _ (job_deadline_from_task_deadline Job Task)
  have hreflE : reflexive_job_priorities (@EDF Job _ (job_deadline_from_task_deadline Job Task)) :=
    EDF_is_reflexive
  have hfrom := hvs.1
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have htsk : job_task (Task := Task) js = tsk := of_decide_eq_true htsks
  have hma := non_pathological_max_arrivals tsk arr_seq (hresp tsk hin) js htsks harrs
  have hcpos : 0 < task_cost tsk := by
    have hv := hvjc js harrs
    unfold valid_job_cost at hv
    rw [htsk] at hv
    exact Nat.lt_of_lt_of_le hjpos (of_decide_eq_true hv)
  have hwb := basic_readiness_is_work_bearing_readiness arr_seq sched hreflE
  let _ := ideal_jlfp_interference arr_seq sched
  let _ := ideal_jlfp_interfering_workload arr_seq sched
  have hwcA := instantiated_i_and_w_are_coherent_with_schedule arr_seq hva sched hfrom hmust hcde hreflE hwb hwc
    hreflE
  have hseq := EDF_implies_sequential_tasks (Task := Task) (ideal_proc_model_is_a_uniprocessor_model Job) arr_seq hva
    sched hwb hvs hvpm hrespE
  have hcons := instantiated_interference_and_workload_consistent_with_sequential_tasks arr_seq hva sched hfrom hmust
    hcde hreflE tsk EDF_respects_sequential_tasks
  have hbounded := Prosa.Analysis.Abstract.Ideal.IwInstantiation.instantiated_busy_intervals_are_bounded arr_seq hva
    sched hfrom hmust hcde hreflE tsk hwb hwc ts hresp hall L hL hfix hvjc
  have hibf := instantiated_task_interference_is_bounded arr_seq hva sched hvs hvjc ts hall hresp tsk pib hpib
  exact uniprocessor_response_time_bound_seq (ideal_proc_model_is_a_uniprocessor_model Job)
    (ideal_proc_model_provides_unit_service Job) (ideal_proc_model_ensures_ideal_progress Job) arr_seq hva sched
    hfrom (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs)
    (valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs) hvjc ts tsk hin hvpm hrtct hvalid hresp
    hwcA hseq hcons L hbounded _ hibf R
    (fun A hA => correct_search_space ts hvalid tsk hin pib L hL hfix R hR hcpos hma A hA) js harrs htsks

end Prosa.Results.Rta.Ideal.Edf.BoundedPi
