-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ideal/fp/nonseq/bounded_pi.v

import Prosa.Model.Schedule.PriorityDriven
import Prosa.Analysis.Abstract.Ideal.IwInstantiation
import Prosa.Analysis.Abstract.IBF.Task
import Prosa.Analysis.Facts.BusyInterval.Existence
import Prosa.Analysis.Abstract.Ideal.CumulativeBounds
import Prosa.Analysis.Abstract.Ideal.AbstractRta
import Prosa.Results.Rta.Ideal.Fp.BoundedPi

namespace Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi

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
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.Priority.Classes
open Prosa.Analysis.Facts.Interference
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.AbstractRta
open Prosa.Analysis.Abstract.Ideal.IwInstantiation
open Prosa.Analysis.Abstract.Ideal.CumulativeBounds
open Prosa.Analysis.Abstract.Ideal.AbstractRta
open Prosa.Util.Notation

/-! Abstract RTA for FP schedulers with bounded priority inversion on ideal uniprocessors, without the
sequential-tasks assumption (self-interference is accounted for explicitly).

Binders follow the elaborated source types: every declaration takes only the section inputs and hypotheses it uses,
in their elaborated order. The FP policy is quantified where the elaborated type quantifies it; the section-local
instances `ideal_jlfp_interference` / `ideal_jlfp_interfering_workload` re-expose the accepted instantiation of
`iw_instantiation` at the section's arrival sequence and schedule, with the JLFP policy induced by the FP policy
(`FP_to_JLFP`); they are passed explicitly. The section-local `task_rbf`, `total_hep_rbf` and `total_ohep_rbf` are
inlined; `IBF` takes the task set, the task and the priority-inversion bound it depends on. Representation: `ε` is
`1`; `maxn` is `Nat.max`; a Boolean in `Prop` position is `= true`; `a != b` is `decide (a ≠ b)`; `tsk \in ts` is
`decide (tsk ∈ ts) = true`; `f^~ j` is `fun x => f x j`; `search_space.is_in_search_space` is the accepted abstract
search-space predicate. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- A positive fixed point of the busy-interval recurrence bounds every (abstract) busy interval. -/
theorem instantiated_busy_intervals_are_bounded [TaskCost Task] [MaxArrivals Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] [JobReady Job (processor_state Job)] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP →
    ∀ sched : schedule (processor_state Job), valid_schedule sched arr_seq →
      @work_bearing_readiness Job _ _ _ (processor_state Job) _ arr_seq sched (FP_to_JLFP FP) →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
    ∀ (tsk : Task) (priority_inversion_bound : duration),
      @priority_inversion_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched (FP_to_JLFP FP) tsk
        (constant priority_inversion_bound) →
      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
    ∀ L : duration, 0 < L →
      L = priority_inversion_bound + total_hep_request_bound_function_FP ts (FP := FP) tsk L →
      @busy_intervals_are_bounded_by Job _ (@ideal_jlfp_interference Job _ arr_seq sched (FP_to_JLFP FP))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (FP_to_JLFP FP)) _ _ (processor_state Job)
        arr_seq sched Task _ _ tsk L := by
  intro hva hvjc FP hrefl sched hvs hwbr ts hall hresp tsk pib hpib hwc L hL hfix
  exact Prosa.Results.Rta.Ideal.Fp.BoundedPi.instantiated_busy_intervals_are_bounded (FP := FP) hrefl arr_seq hva
    sched hwbr hvs hwc hvjc ts hall hresp tsk pib hpib L hL hfix

/-- The interference bound function: the priority-inversion bound, the self-interference of the task in the longer
of `[A, A + ε)` and `Δ`, and the RBF of the other higher-or-equal-priority tasks. -/
def IBF [TaskCost Task] [MaxArrivals Task] [FP : FP_policy Task] (ts : List Task) (tsk : Task)
    (priority_inversion_bound : duration) (A : instant) (Δ : duration) : Nat :=
  priority_inversion_bound + (task_request_bound_function tsk (Nat.max (A + 1) Δ) - task_cost tsk) +
    total_ohep_request_bound_function_FP ts tsk Δ

/-- Under a reflexive FP policy, the other higher-or-equal-priority jobs of the task of `j` are the other jobs of
that task. -/
private theorem another_hep_job_of_same_task_eq [JobTask Job Task] (FP : FP_policy Task) :
    reflexive_task_priorities FP → ∀ (tsk : Task) (j : Job), job_of_task tsk j = true → ∀ x : Job,
      @another_hep_job_of_same_task Task _ Job _ _ (FP_to_JLFP FP) x j = (job_of_task tsk x && decide (x ≠ j)) := by
  intro hrefl tsk j htsk x
  have htskj : job_task (Task := Task) j = tsk := of_decide_eq_true htsk
  unfold another_hep_job_of_same_task another_hep_job job_of_task
  by_cases hx : job_task (Task := Task) x = tsk
  · have hhep : @hep_job Job _ (FP_to_JLFP FP) x j = true := by
      show FP.hep_task (job_task x) (job_task j) = true
      rw [hx, htskj]; exact hrefl tsk
    simp [hhep, hx, htskj]
  · simp [hx, htskj]

/-- The workload of the other higher-or-equal-priority jobs of the task of `j` among arrivals containing `j`. -/
private theorem self_workload_eq [TaskCost Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → ∀ FP : FP_policy Task, reflexive_task_priorities FP →
    ∀ (tsk : Task) (j : Job), job_of_task tsk j = true →
    ∀ t1 t2 : instant, decide (j ∈ arrivals_between arr_seq t1 t2) = true →
      workload_of_jobs (fun x => @another_hep_job_of_same_task Task _ Job _ _ (FP_to_JLFP FP) x j)
          (arrivals_between arr_seq t1 t2) =
        task_workload_between arr_seq tsk t1 t2 - job_cost j := by
  intro hva FP hrefl tsk j htsk t1 t2 hin
  rw [workload_of_jobs_equiv_pred _ _ (fun x => job_of_task tsk x && decide (x ≠ j))
    (fun x _ => another_hep_job_of_same_task_eq FP hrefl tsk j htsk x)]
  rw [workload_minus_job_cost' j _ (arrivals_uniq arr_seq hva.1 hva.2 t1 t2) hin (job_of_task tsk), htsk]
  rfl

/-- Self-interference when `j` arrives before the end of the interval. -/
theorem self_intf_bound_case1 [TaskCost Task] [MaxArrivals Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP →
    ∀ ts : List Task, taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ priority_inversion_bound L : duration, 0 < L →
      L = priority_inversion_bound + total_hep_request_bound_function_FP ts (FP := FP) tsk L →
    ∀ (t1 : instant) (Δ : duration) (j : Job), job_cost_positive j = true → job_of_task tsk j = true →
      arrives_in arr_seq j → t1 ≤ job_arrival j → job_arrival j < t1 + Δ →
      workload_of_jobs (fun x => @another_hep_job_of_same_task Task _ Job _ _ (FP_to_JLFP FP) x j)
          (arrivals_between arr_seq t1 (t1 + Δ)) ≤
        task_request_bound_function tsk Δ - task_cost tsk := by
  intro hva hvjc FP hrefl ts hresp tsk hin _ _ _ _ t1 Δ j _ htsk hj hle hlt
  have hmem : decide (j ∈ arrivals_between arr_seq t1 (t1 + Δ)) = true :=
    (job_arrival_in_bounds arr_seq hva.1 j t1 (t1 + Δ)).mpr
      ⟨hj, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hle, hlt⟩⟩
  rw [self_workload_eq arr_seq hva FP hrefl tsk j htsk t1 (t1 + Δ) hmem]
  exact task_rbf_without_job_under_analysis arr_seq hva.1 hvjc tsk (hresp tsk hin) j htsk hj t1 Δ hlt hle

/-- Self-interference when `j` arrives after the end of the interval. -/
theorem self_intf_bound_case2 [TaskCost Task] [MaxArrivals Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP →
    ∀ ts : List Task, taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ priority_inversion_bound L : duration, 0 < L →
      L = priority_inversion_bound + total_hep_request_bound_function_FP ts (FP := FP) tsk L →
    ∀ (t1 : instant) (Δ : duration) (j : Job), job_cost_positive j = true → job_of_task tsk j = true →
      arrives_in arr_seq j → t1 ≤ job_arrival j → t1 + Δ ≤ job_arrival j →
      workload_of_jobs (fun x => @another_hep_job_of_same_task Task _ Job _ _ (FP_to_JLFP FP) x j)
          (arrivals_between arr_seq t1 (t1 + Δ)) ≤
        task_request_bound_function tsk (job_arrival j - t1 + 1) - task_cost tsk := by
  intro hva hvjc FP hrefl ts hresp tsk hin _ _ _ _ t1 Δ j _ htsk hj hle hge
  have hend : t1 + (job_arrival j - t1 + 1) = job_arrival j + 1 := by omega'
  refine Nat.le_trans (workload_of_jobs_reduce_range arr_seq t1 (t1 + Δ) (job_arrival j + 1) _ (by omega')
    (by omega')) ?_
  have hmem : decide (j ∈ arrivals_between arr_seq t1 (job_arrival j + 1)) = true :=
    (job_arrival_in_bounds arr_seq hva.1 j t1 (job_arrival j + 1)).mpr
      ⟨hj, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hle, by omega'⟩⟩
  rw [self_workload_eq arr_seq hva FP hrefl tsk j htsk t1 (job_arrival j + 1) hmem, ← hend]
  exact task_rbf_without_job_under_analysis arr_seq hva.1 hvjc tsk (hresp tsk hin) j htsk hj t1
    (job_arrival j - t1 + 1) (by omega') hle

/-- Self-interference of any job `j` of `tsk` arriving no earlier than the start of the interval. -/
theorem self_intf_bound [TaskCost Task] [MaxArrivals Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP →
    ∀ ts : List Task, taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ priority_inversion_bound L : duration, 0 < L →
      L = priority_inversion_bound + total_hep_request_bound_function_FP ts (FP := FP) tsk L →
    ∀ (t1 : instant) (Δ : duration) (j : Job), job_cost_positive j = true → job_of_task tsk j = true →
      arrives_in arr_seq j → t1 ≤ job_arrival j →
      workload_of_jobs (fun x => @another_hep_job_of_same_task Task _ Job _ _ (FP_to_JLFP FP) x j)
          (arrivals_between arr_seq t1 (t1 + Δ)) ≤
        task_request_bound_function tsk (Nat.max (job_arrival j - t1 + 1) Δ) - task_cost tsk := by
  intro hva hvjc FP hrefl ts hresp tsk hin pib L hL hfix t1 Δ j hcp htsk hj hle
  simp only [Nat.max]
  by_cases hlt : job_arrival j < t1 + Δ
  · rw [Nat.max_eq_right (by omega')]
    exact self_intf_bound_case1 arr_seq hva hvjc FP hrefl ts hresp tsk hin pib L hL hfix t1 Δ j hcp htsk hj hle hlt
  · rw [Nat.max_eq_left (by omega')]
    exact self_intf_bound_case2 arr_seq hva hvjc FP hrefl ts hresp tsk hin pib L hL hfix t1 Δ j hcp htsk hj hle
      (by omega')

/-- `IBF` bounds the interference incurred by any job of `tsk`. -/
theorem instantiated_task_interference_is_bounded [TaskCost Task] [MaxArrivals Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] [JobReady Job (processor_state Job)] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP →
    ∀ sched : schedule (processor_state Job), valid_schedule sched arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ priority_inversion_bound : duration,
      @priority_inversion_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched (FP_to_JLFP FP) tsk
        (constant priority_inversion_bound) →
    ∀ L : duration, 0 < L →
      L = priority_inversion_bound + total_hep_request_bound_function_FP ts (FP := FP) tsk L →
      @job_interference_is_bounded_by Job _ (@ideal_jlfp_interference Job _ arr_seq sched (FP_to_JLFP FP))
        (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (FP_to_JLFP FP)) _ _ (processor_state Job) arr_seq
        sched Task _ _ tsk (IBF ts (FP := FP) tsk priority_inversion_bound)
        (@relative_arrival_time_of_job_is_A Job _ _ _ (processor_state Job) sched
          (@ideal_jlfp_interference Job _ arr_seq sched (FP_to_JLFP FP))
          (@ideal_jlfp_interfering_workload Job _ _ arr_seq sched (FP_to_JLFP FP))) := by
  intro hva hvjc FP hrefl sched hvs ts hall hresp tsk hin pib hpib L hL hfix t1 t2 Δ j hj htsk hbi hlt hncomp A hA
  let _ : JLFP_policy Job := FP_to_JLFP FP
  have hfrom := hvs.1
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hreflJ := reflexive_priorities_FP_implies_JLFP (Job := Job) FP hrefl
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
  have hcl := (instantiated_busy_interval_equivalent_busy_interval arr_seq hva sched hfrom hmust hcde hreflJ j hj hcp
    t1 t2).mpr hbi
  have hle : t1 ≤ job_arrival j := by
    have h := hcl.1.2.2.2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have hsplit := cumulative_interference_split arr_seq hva sched hfrom hmust hreflJ j t1 (t1 + Δ)
  -- priority inversion
  have hpi : cumulative_priority_inversion arr_seq sched j t1 (t1 + Δ) ≤ pib :=
    cumulative_priority_inversion_is_bounded hreflJ arr_seq hva sched hvs tsk j hj htsk hcp t1 t2 hbi Δ
      (Nat.le_of_lt hlt) (constant pib) hpib
  -- other higher-or-equal-priority jobs
  have hohep : cumulative_another_hep_job_interference arr_seq sched j t1 (t1 + Δ) ≤
      (task_request_bound_function tsk (Nat.max (job_arrival j - t1 + 1) Δ) - task_cost tsk) +
        total_ohep_request_bound_function_FP ts (FP := FP) tsk Δ := by
    rw [cumulative_i_ohep_eq_service_of_ohep (ideal_proc_model_is_a_uniprocessor_model Job) arr_seq hva sched hmust
      hcde (FP_to_JLFP FP) (ideal_proc_model_provides_unit_service Job) j t1 (t1 + Δ) hcl.1.2.1]
    unfold service_of_other_hep_jobs
    refine Nat.le_trans (service_of_jobs_le_workload (ideal_proc_model_provides_unit_service Job) sched hcde _ _ _ _) ?_
    rw [workload_of_other_jobs_split (Task := Task)]
    have hself := self_intf_bound arr_seq hva hvjc FP hrefl ts hresp tsk hin pib L hL hfix t1 Δ j hcp htsk hj hle
    have hother := ohep_workload_le_rbf ts FP arr_seq hall hvjc hresp j tsk htsk Δ t1
    omega'
  show @cumulative_interference Job _ (ideal_jlfp_interference arr_seq sched) j t1 (t1 + Δ) ≤ _
  rw [hsplit]
  unfold IBF
  omega'

/-- The concrete search space: offsets below `L` at which the RBF of `tsk` steps. -/
def is_in_concrete_search_space [TaskCost Task] [MaxArrivals Task] (tsk : Task) (L : duration) (A : Nat) : Bool :=
  decide (A < L) && decide (task_request_bound_function tsk A ≠ task_request_bound_function tsk (A + 1))

/-- Any offset of the abstract search space is in the concrete search space. -/
theorem A_is_in_concrete_search_space [TaskCost Task] [MaxArrivals Task] [FP : FP_policy Task] (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ priority_inversion_bound L : duration, 0 < L →
      L = priority_inversion_bound + total_hep_request_bound_function_FP ts tsk L →
      0 < task_cost tsk → 0 < max_arrivals tsk 1 →
    ∀ A : duration,
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L (IBF ts tsk priority_inversion_bound) A →
        is_in_concrete_search_space tsk L A = true := by
  intro hv tsk hin pib L hL _ hc hpos A h
  unfold is_in_concrete_search_space
  rcases h with hA | ⟨hA0, hAL, x, _, hne⟩
  · subst hA
    have h0 := task_rbf_0_zero tsk (hv tsk hin)
    have h1 := task_rbf_1_ge_task_cost tsk hpos
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hL, ?_⟩
    rw [h0, Nat.zero_add]
    omega'
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hAL, ?_⟩
    intro heq
    apply hne
    have hA1 : A - 1 + 1 = A := Nat.sub_add_cancel hA0
    unfold IBF
    simp only [Nat.max, hA1]
    by_cases hx : x ≤ A
    · rw [Nat.max_eq_left hx, Nat.max_eq_left (by omega'), heq]
    · rw [Nat.max_eq_right (by omega'), Nat.max_eq_right (by omega')]

/-- Every offset of the abstract search space has a solution of the response-time recurrence. -/
theorem correct_search_space [TaskCost Task] [TaskRunToCompletionThreshold Task] [MaxArrivals Task]
    [JobTask Job Task] [JobCost Job] [JobPreemptable Job] (arr_seq : arrival_sequence Job) (FP : FP_policy Task) :
    reflexive_task_priorities FP →
    ∀ ts : List Task, valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true → valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ priority_inversion_bound L : duration, 0 < L →
      L = priority_inversion_bound + total_hep_request_bound_function_FP ts (FP := FP) tsk L →
    ∀ R : duration,
      (∀ A : duration, is_in_concrete_search_space tsk L A = true →
        ∃ F : duration, 0 < F ∧
          priority_inversion_bound + total_hep_request_bound_function_FP ts (FP := FP) tsk (A + F) -
              (task_cost tsk - task_rtct tsk) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R) →
      0 < task_cost tsk → 0 < max_arrivals tsk 1 →
    ∀ A : Nat,
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L (IBF ts (FP := FP) tsk priority_inversion_bound) A →
        ∃ F : Nat, task_rtct tsk + IBF ts (FP := FP) tsk priority_inversion_bound A (A + F) ≤ A + F ∧
          F + (task_cost tsk - task_rtct tsk) ≤ R := by
  intro hrefl ts hv tsk hin hrtct pib L hL hfix R hR hc hpos A hA
  obtain ⟨F, hF0, hFix, hFR⟩ := hR A (A_is_in_concrete_search_space ts hv tsk hin pib L hL hfix hc hpos A hA)
  refine ⟨F, ?_, hFR⟩
  have hge := task_rbf_ge_task_cost tsk (hv tsk hin) hpos (A + F) (by omega')
  have hsplit := split_hep_rbf_weaken FP ts tsk hrefl (A + F) hin
  have hrc : task_rtct tsk ≤ task_cost tsk := of_decide_eq_true hrtct.1
  unfold IBF
  simp only [Nat.max]
  rw [Nat.max_eq_right (by omega')]
  omega'

/-- Response-time bound for FP schedulers with bounded priority inversion on ideal uniprocessors, without the
sequential-tasks assumption. -/
theorem uniprocessor_response_time_bound_fp [TaskCost Task] [TaskRunToCompletionThreshold Task] [MaxArrivals Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job] [JobReady Job (processor_state Job)]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP →
    ∀ sched : schedule (processor_state Job), valid_schedule sched arr_seq →
      @work_bearing_readiness Job _ _ _ (processor_state Job) _ arr_seq sched (FP_to_JLFP FP) →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → valid_taskset_arrival_curve ts max_arrivals →
      taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
      valid_preemption_model arr_seq sched →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ priority_inversion_bound : duration,
      @priority_inversion_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched (FP_to_JLFP FP) tsk
        (constant priority_inversion_bound) →
      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
    ∀ L : duration, 0 < L →
      L = priority_inversion_bound + total_hep_request_bound_function_FP ts (FP := FP) tsk L →
    ∀ R : duration,
      (∀ A : duration, is_in_concrete_search_space tsk L A = true →
        ∃ F : duration, 0 < F ∧
          priority_inversion_bound + total_hep_request_bound_function_FP ts (FP := FP) tsk (A + F) -
              (task_cost tsk - task_rtct tsk) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hva hvjc FP hrefl sched hvs hwbr ts hall hvalid hresp tsk hin hvpm hrtct pib hpib hwc L hL hfix R hR js
    harrs htsks
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
  exact uniprocessor_response_time_bound_ideal (ideal_proc_model_ensures_ideal_progress Job)
    (ideal_proc_model_provides_unit_service Job) arr_seq sched hmust hcde hvjc ts tsk hin hvpm hrtct hwcA L
    (instantiated_busy_intervals_are_bounded arr_seq hva hvjc FP hrefl sched hvs hwbr ts hall hresp tsk pib hpib hwc
      L hL hfix) _
    (instantiated_task_interference_is_bounded arr_seq hva hvjc FP hrefl sched hvs ts hall hresp tsk hin pib hpib L
      hL hfix) R
    (fun A hA => correct_search_space arr_seq FP hrefl ts hvalid tsk hin hrtct pib L hL hfix R hR hcpos hma A hA)
    js harrs htsks

end Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi
