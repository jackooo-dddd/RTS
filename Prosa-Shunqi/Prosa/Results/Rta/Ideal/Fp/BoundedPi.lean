-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ideal/fp/bounded_pi.v

import Prosa.Model.Schedule.PriorityDriven
import Prosa.Analysis.Abstract.Ideal.IwInstantiation
import Prosa.Analysis.Facts.BusyInterval.Existence
import Prosa.Analysis.Abstract.Ideal.AbstractSeqRta
import Prosa.Analysis.Facts.Model.TaskCost

namespace Prosa.Results.Rta.Ideal.Fp.BoundedPi

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
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Processor.Ideal
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.Priority.Classes
open Prosa.Analysis.Facts.Interference
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.BusyInterval.Existence
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.IBF.Task
open Prosa.Analysis.Abstract.Ideal.IwInstantiation
open Prosa.Analysis.Abstract.Ideal.AbstractSeqRta
open Prosa.Util.Notation

/-! Abstract RTA for FP schedulers with bounded priority inversion on ideal uniprocessors.

Binders follow the elaborated source types: every declaration takes only the section inputs and hypotheses it uses,
in their elaborated order; instance inputs quantified after a hypothesis are `∀ [..]` binders at that position. The
section-local instances `ideal_jlfp_interference` / `ideal_jlfp_interfering_workload` re-expose the accepted
instantiation of `iw_instantiation` at the section's arrival sequence and schedule, with the JLFP policy induced by
the FP policy (`FP_to_JLFP`); they are passed explicitly, as are the policy-dependent definitions. The section-local
`task_rbf`, `total_hep_rbf`, `total_ohep_rbf`, `task_IBF` and `total_interference_bound` are inlined. Representation:
`ε` is `1`; a Boolean in `Prop` position is `= true`; `a != b` is `decide (a ≠ b)`; `tsk \in ts` is
`decide (tsk ∈ ts) = true`; `search_space.is_in_search_space` is the accepted abstract search-space predicate. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- The concrete FP search space: offsets below `L` at which the RBF of `tsk` steps. -/
def is_in_search_space [TaskCost Task] [MaxArrivals Task] (tsk : Task) (L : duration) (A : Nat) : Bool :=
  decide (A < L) &&
    decide (task_request_bound_function tsk A ≠ task_request_bound_function tsk (A + 1))

/-- A positive fixed point of the busy-interval recurrence bounds every (abstract) busy interval. -/
theorem instantiated_busy_intervals_are_bounded [TaskCost Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    [FP : FP_policy Task] :
    reflexive_task_priorities FP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule (processor_state Job)) [JobReady Job (processor_state Job)],
      @work_bearing_readiness Job _ _ _ (processor_state Job) _ arr_seq sched (FP_to_JLFP FP) →
      valid_schedule sched arr_seq →
      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
    ∀ [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
    ∀ (tsk : Task) (priority_inversion_bound : duration),
      @priority_inversion_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched (FP_to_JLFP FP) tsk
        (constant priority_inversion_bound) →
    ∀ L : duration, 0 < L →
      L = priority_inversion_bound + total_hep_request_bound_function_FP ts (FP := FP) tsk L →
      @busy_intervals_are_bounded_by Job _ (@ideal_jlfp_interference Job _ arr_seq sched (FP_to_JLFP FP))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (FP_to_JLFP FP)) _ _ (processor_state Job)
        arr_seq sched Task _ _ tsk L := by
  intro hrefl arr_seq hva sched _ hwbr hvs hwc hvjc ts hall _ hresp tsk pib hpib L hL hfix j hj htsk hpos
  let _ : JLFP_policy Job := FP_to_JLFP FP
  have hfrom := hvs.1
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hreflJ := reflexive_priorities_FP_implies_JLFP (Job := Job) FP hrefl
  have hcp : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hpos
  have htskj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  obtain ⟨t1, t2, hin, hle, hbi⟩ := exists_busy_interval arr_seq hva sched hfrom hmust hcde (FP_to_JLFP FP) hwbr
    tsk j hj htsk hcp hwc hva.2 hreflJ (ideal_proc_model_is_a_uniprocessor_model Job)
    (ideal_proc_model_provides_unit_service Job) (ideal_proc_model_ensures_ideal_progress Job)
    (fun _ => pib) (hpib j hj htsk hpos) L hL
    (by
      intro t
      have hw := workload_of_jobs_bounded arr_seq hvjc ts hall hresp
        (fun jo => (FP_to_JLFP FP).hep_job jo j) (fun tsk' => FP.hep_task tsk' tsk)
        (by intro jo h; show FP.hep_task (job_task jo) tsk = true; rw [← htskj]; exact h) t L
      have hw' : @workload_of_hep_jobs Job _ _ arr_seq (FP_to_JLFP FP) j t (t + L) ≤
          total_hep_request_bound_function_FP ts (FP := FP) tsk L := hw
      show pib + @workload_of_hep_jobs Job _ _ arr_seq (FP_to_JLFP FP) j t (t + L) ≤ L
      omega')
    hpos
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
  exact ⟨t1, t2, hin, hle, (instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hfrom hmust hcde
    hreflJ j hj hcp t1 t2).mp hbi⟩

/-- The priority-inversion bound plus the RBF of the other higher-or-equal-priority tasks bounds the task
interference. -/
theorem instantiated_task_interference_is_bounded [TaskCost Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    [FP : FP_policy Task] :
    reflexive_task_priorities FP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule (processor_state Job)) [JobReady Job (processor_state Job)],
      valid_schedule sched arr_seq →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
    ∀ [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
    ∀ (tsk : Task) (priority_inversion_bound : duration),
      @priority_inversion_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched (FP_to_JLFP FP) tsk
        (constant priority_inversion_bound) →
      @task_interference_is_bounded_by Job _ Task _ _ _ _ (processor_state Job) arr_seq sched tsk
        (@ideal_jlfp_interference Job _ arr_seq sched (FP_to_JLFP FP))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (FP_to_JLFP FP))
        (fun _ R => priority_inversion_bound + total_ohep_request_bound_function_FP ts (FP := FP) tsk R) := by
  intro hrefl arr_seq hva sched _ hvs hvjc ts hall _ hresp tsk pib hpib t1 t2 Δ j hj htsk hbi hlt hncomp _ _
  let _ : JLFP_policy Job := FP_to_JLFP FP
  have hfrom := hvs.1
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hreflJ := reflexive_priorities_FP_implies_JLFP (Job := Job) FP hrefl
  have htskj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  have hpos : 0 < job_cost j := by
    rcases Nat.eq_zero_or_pos (job_cost j) with h0 | h
    · exfalso
      unfold completed_by at hncomp
      rw [h0] at hncomp
      simp at hncomp
    · exact h
  have hcp : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hpos
  have hcl := (instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hfrom hmust hcde hreflJ j hj
    hcp t1 t2).mpr hbi
  have hsplit := cumulative_task_interference_split arr_seq hva sched hfrom hmust (JLFP := FP_to_JLFP FP) hreflJ
    tsk j t1 (t1 + Δ) hj htsk hncomp
  -- priority inversion
  have hpi : cumulative_priority_inversion arr_seq sched j t1 (t1 + Δ) ≤ pib := by
    have hle : cumulative_priority_inversion arr_seq sched j t1 (t1 + Δ) ≤
        cumulative_priority_inversion arr_seq sched j t1 t2 := by
      unfold cumulative_priority_inversion
      exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right (by omega'))
    exact Nat.le_trans hle (hpib j hj htsk hpos t1 t2 hcl.1)
  -- other higher-or-equal-priority tasks
  have hathep : cumulative_another_task_hep_job_interference (Task := Task) arr_seq sched j
      t1 (t1 + Δ) ≤ total_ohep_request_bound_function_FP ts (FP := FP) tsk Δ := by
    rw [cumulative_i_thep_eq_service_of_othep (ideal_proc_model_is_a_uniprocessor_model Job) arr_seq hva sched hmust
      hcde (FP_to_JLFP FP) (ideal_proc_model_provides_unit_service Job) j t1 (t1 + Δ) hcl.1.2.1]
    unfold service_of_other_task_hep_jobs
    refine Nat.le_trans (service_of_jobs_le_workload (ideal_proc_model_provides_unit_service Job) sched hcde _ _ _ _) ?_
    exact workload_of_jobs_bounded arr_seq hvjc ts hall hresp _
      (fun tsk' => FP.hep_task tsk' tsk && decide (tsk' ≠ tsk))
      (by
        intro jo h
        change (FP.hep_task (job_task jo) (job_task (Task := Task) j) &&
          decide (job_task (Task := Task) jo ≠ job_task (Task := Task) j)) = true at h
        rw [htskj] at h
        exact h) t1 Δ
  refine Nat.le_trans hsplit ?_
  show _ ≤ pib + total_ohep_request_bound_function_FP ts (FP := FP) tsk Δ
  omega'

/-- Any offset of the abstract search space is in the concrete FP search space. -/
theorem A_is_in_concrete_search_space [TaskCost Task] [FP : FP_policy Task] (ts : List Task) [MaxArrivals Task] :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ priority_inversion_bound L : duration, 0 < L → 0 < task_cost tsk → 0 < max_arrivals tsk 1 →
    ∀ A : duration,
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
          (fun (A0 : Nat) (Δ : duration) =>
            task_request_bound_function tsk (A0 + 1) - task_cost tsk +
              (priority_inversion_bound + total_ohep_request_bound_function_FP ts (FP := FP) tsk Δ)) A →
        is_in_search_space tsk L A = true := by
  intro hv tsk hin pib L hL hc hpos A h
  unfold is_in_search_space
  rcases h with hA | ⟨hA0, hAL, x, _, hne⟩
  · subst hA
    have h0 := task_rbf_0_zero tsk (hv tsk hin)
    have h1 := task_rbf_epsilon_gt_0 tsk hc hpos
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hL, ?_⟩
    rw [h0, Nat.zero_add]
    exact Nat.ne_of_lt h1
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hAL, ?_⟩
    intro heq
    apply hne
    have hA1 : A - 1 + 1 = A := Nat.sub_add_cancel hA0
    simp only [hA1, heq]

/-- Every offset of the abstract search space has a solution of the response-time recurrence. -/
theorem correct_search_space [TaskCost Task] [TaskRunToCompletionThreshold Task] [FP : FP_policy Task]
    (ts : List Task) [MaxArrivals Task] :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ priority_inversion_bound L : duration, 0 < L →
    ∀ R : duration,
      (∀ A : duration, is_in_search_space tsk L A = true →
        ∃ F : duration,
          priority_inversion_bound + (task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk)) +
              total_ohep_request_bound_function_FP ts (FP := FP) tsk (A + F) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R) →
      0 < task_cost tsk → 0 < max_arrivals tsk 1 →
    ∀ A : duration,
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
          (fun (A0 : Nat) (Δ : duration) =>
            task_request_bound_function tsk (A0 + 1) - task_cost tsk +
              (priority_inversion_bound + total_ohep_request_bound_function_FP ts (FP := FP) tsk Δ)) A →
        ∃ F : duration,
          task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk) +
              (priority_inversion_bound + total_ohep_request_bound_function_FP ts (FP := FP) tsk (A + F)) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R := by
  intro hv tsk hin pib L hL R hR hc hpos A hA
  obtain ⟨F, hF, hFR⟩ := hR A (A_is_in_concrete_search_space ts hv tsk hin pib L hL hc hpos A hA)
  exact ⟨F, by omega', hFR⟩

/-- Response-time bound for FP schedulers with bounded priority inversion on ideal uniprocessors. -/
theorem uniprocessor_response_time_bound_fp [TaskCost Task] [TaskRunToCompletionThreshold Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] [JobPreemptable Job] [FP : FP_policy Task] :
    reflexive_task_priorities FP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule (processor_state Job)) [JobReady Job (processor_state Job)],
      @work_bearing_readiness Job _ _ _ (processor_state Job) _ arr_seq sched (FP_to_JLFP FP) →
      valid_schedule sched arr_seq →
      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
      sequential_tasks (Task := Task) arr_seq sched →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
    ∀ [MaxArrivals Task], valid_taskset_arrival_curve ts max_arrivals →
      taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
      valid_preemption_model arr_seq sched →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ priority_inversion_bound : duration,
      @priority_inversion_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched (FP_to_JLFP FP) tsk
        (constant priority_inversion_bound) →
    ∀ L : duration, 0 < L →
      L = priority_inversion_bound + total_hep_request_bound_function_FP ts (FP := FP) tsk L →
    ∀ R : duration,
      (∀ A : duration, is_in_search_space tsk L A = true →
        ∃ F : duration,
          priority_inversion_bound + (task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk)) +
              total_ohep_request_bound_function_FP ts (FP := FP) tsk (A + F) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hrefl arr_seq hva sched _ hwbr hvs hwc hseq hvjc ts hall _ hvalid hresp tsk hin hvpm hrtct pib hpib L hL
    hfix R hR js harrs htsks
  rcases Nat.eq_zero_or_pos (job_cost js) with h0 | hjpos
  · unfold job_response_time_bound completed_by
    apply decide_eq_true; rw [h0]; exact Nat.zero_le _
  have hfrom := hvs.1
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hreflJ := reflexive_priorities_FP_implies_JLFP (Job := Job) FP hrefl
  have htsk : job_task (Task := Task) js = tsk := of_decide_eq_true htsks
  have hma := non_pathological_max_arrivals tsk arr_seq (hresp tsk hin) js htsks harrs
  have hcpos : 0 < task_cost tsk := by
    have hv := hvjc js harrs
    unfold valid_job_cost at hv
    rw [htsk] at hv
    exact Nat.lt_of_lt_of_le hjpos (of_decide_eq_true hv)
  let _ : JLFP_policy Job := FP_to_JLFP FP
  let _ := ideal_jlfp_interference arr_seq sched
  let _ := ideal_jlfp_interfering_workload arr_seq sched
  have hwcA := instantiated_i_and_w_are_coherent_with_schedule arr_seq hva sched hfrom hmust hcde hreflJ hwbr hwc
    hreflJ
  have hcons := instantiated_interference_and_workload_consistent_with_sequential_tasks arr_seq hva sched hfrom hmust
    hcde hreflJ tsk (respects_sequential_tasks FP hrefl)
  have hbounded := instantiated_busy_intervals_are_bounded hrefl arr_seq hva sched hwbr hvs hwc hvjc ts hall hresp
    tsk pib hpib L hL hfix
  have hibf := instantiated_task_interference_is_bounded hrefl arr_seq hva sched hvs hvjc ts hall hresp tsk pib hpib
  exact uniprocessor_response_time_bound_seq (ideal_proc_model_is_a_uniprocessor_model Job)
    (ideal_proc_model_provides_unit_service Job) (ideal_proc_model_ensures_ideal_progress Job) arr_seq hva sched
    hfrom (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs)
    (valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs) hvjc ts tsk hin hvpm hrtct hvalid hresp
    hwcA hseq hcons L hbounded _ hibf R
    (fun A hA => correct_search_space ts hvalid tsk hin pib L hL R hR hcpos hma A hA) js harrs htsks

end Prosa.Results.Rta.Ideal.Fp.BoundedPi
