-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/rs/edf/fully_nonpreemptive.v

import Prosa.Analysis.Facts.Readiness.Basic
import Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive
import Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive
import Prosa.Analysis.Abstract.RestrictedSupply.TaskIntraInterferenceBound
import Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Edf
import Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Edf
import Prosa.Analysis.Facts.Model.TaskCost
import Prosa.Analysis.Facts.Priority.Edf
import Prosa.Analysis.Facts.BlockingBound.Edf
import Prosa.Analysis.Facts.Workload.EdfAthepBound

namespace Prosa.Results.Rta.Rs.Edf.FullyNonpreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.AbsoluteDeadline
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.FullyNonpreemptive
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyNonpreemptive
open Prosa.Model.Schedule.Nonpreemptive
open Prosa.Analysis.Definitions.BusyInterval.EdfPiBound
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Edf
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Processor.PlatformProperties
open Prosa.Util.Minmax
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.BlockingBound.Edf
open Prosa.Analysis.Definitions.Workload.EdfAthepBound
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation
open Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Edf
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Priority.Edf
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive
open Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive
open Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive

/-! Response-time analysis for fully non-preemptive EDF scheduling of sporadic
tasks with arbitrary arrival curves on a uniprocessor with arbitrary supply
restrictions, by instantiating the accepted sequential abstract
restricted-supply analysis.

Binders follow the elaborated source types: each declaration takes the
section inputs and hypotheses it uses, in their elaborated order. The
source's section-local instances are passed explicitly where the elaborated
statements use them implicitly: the accepted `fully_nonpreemptive_job_model`,
`fully_nonpreemptive_task_model` and `fully_nonpreemptive_rtc_threshold` and the
accepted `basic_ready_instance`. The EDF policy is the accepted `EDF`
instance over the accepted `job_deadline_from_task_deadline` instance, named
explicitly. The busy-SBF validity is the classical one of
`analysis/definitions/sbf/busy.v`; the supply bound function is applied
through its accepted class field; `is_in_search_space` is the accepted EDF
search space and `bound_on_athep_workload` the accepted EDF athep bound.
Representation: a Boolean in `Prop` position is `= true`; `x \in xs` is
`decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`; `ε` is `1`. -/

/-- `L` is a positive solution of the busy-window recurrence, including the
longest busy interval starting with priority inversion. -/
def busy_window_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [TaskDeadline Task]
    [MaxArrivals Task] (ts : List Task) (tsk : Task) (SBF : SupplyBoundFunction) (L : duration) : Prop :=
  0 < L ∧ total_request_bound_function ts L ≤ SBF.supply_bound_function L ∧
    @longest_busy_interval_with_pi Task _ _ _ fully_nonpreemptive_task_model _ ts tsk ≤ SBF.supply_bound_function L

/-- `R` solves the response-time recurrence for every offset of the search space. -/
def rta_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [TaskDeadline Task]
    [MaxArrivals Task] (ts : List Task) (tsk : Task) (SBF : SupplyBoundFunction) (L : duration) (R : Nat) : Prop :=
  ∀ A : duration, @is_in_search_space Task _ _ _ fully_nonpreemptive_task_model ts _ tsk L A = true →
    ∃ F : duration,
      @blocking_bound Task _ _ _ fully_nonpreemptive_task_model ts _ tsk A +
          (task_request_bound_function tsk (A + 1) - (task_cost tsk - 1)) +
          bound_on_athep_workload ts tsk A F ≤ SBF.supply_bound_function F ∧
      SBF.supply_bound_function F + (task_cost tsk - 1) ≤ SBF.supply_bound_function (A + R) ∧
      F ≤ A + R

theorem uniprocessor_response_time_bound_fully_nonpreemptive_edf {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [TaskDeadline Task] [MaxArrivals Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] [JobArrival Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState → fully_consuming_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
      valid_taskset_arrival_curve ts max_arrivals →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ sched : schedule PState,
      @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ PState basic_ready_instance arr_seq sched →
      nonpreemptive_schedule sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ PState fully_nonpreemptive_job_model
        basic_ready_instance arr_seq sched (@EDF Job _ (job_deadline_from_task_deadline Job Task)) →
    ∀ SBF : SupplyBoundFunction, unit_supply_bound_function SBF.supply_bound_function →
      @Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf Task _ Job _ _ _ _ PState arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) tsk SBF.supply_bound_function →
    ∀ L : duration, busy_window_recurrence_solution ts tsk SBF L →
    ∀ R : duration, rta_recurrence_solution ts tsk SBF L R →
      task_response_time_bound arr_seq sched tsk R := by
  intro huni hsup hcons arr_seq hva hcost ts hall hresp hvalid tsk hin sched hvs hwc hnps hrespE
    SBF hunit hsbf L hbw R hsol
  obtain ⟨hL, hfix, hpi⟩ := hbw
  intro js harrs hjobs
  by_cases hzero : job_cost js = 0
  · unfold job_response_time_bound completed_by
    apply decide_eq_true; rw [hzero]; exact Nat.zero_le _
  have hjpos : 0 < job_cost js := Nat.pos_of_ne_zero hzero
  let _ : JobReady Job PState := basic_ready_instance
  let _ : JobPreemptable Job := fully_nonpreemptive_job_model
  let _ : TaskMaxNonpreemptiveSegment Task := fully_nonpreemptive_task_model
  let _ : TaskRunToCompletionThreshold Task := fully_nonpreemptive_rtc_threshold
  let _ : JLFP_policy Job := @EDF Job _ (job_deadline_from_task_deadline Job Task)
  let _ := rs_jlfp_interference arr_seq sched
  let _ := rs_jlfp_interfering_workload arr_seq sched
  have hu := unit_supply_is_unit_service PState hsup
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hfrom := valid_schedule_jobs_come_from_arrival_sequence sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hreflJ : reflexive_job_priorities (@EDF Job _ (job_deadline_from_task_deadline Job Task)) :=
    EDF_is_reflexive
  have htransJ : transitive_job_priorities (@EDF Job _ (job_deadline_from_task_deadline Job Task)) :=
    EDF_is_transitive
  have hwb := basic_readiness_is_work_bearing_readiness arr_seq sched hreflJ
  have hvpm := valid_fully_nonpreemptive_model arr_seq hu sched hnps hcde
  have hvm : valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched :=
    ⟨hvpm, fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions arr_seq hcost⟩
  have hwcA := instantiated_i_and_w_are_coherent_with_schedule huni hsup hcons arr_seq hva sched hfrom hmust hcde
    hreflJ hwb hvs hwc
  have htsk : job_task (Task := Task) js = tsk := of_decide_eq_true hjobs
  have hresp_tsk := hresp tsk hin
  have hma := non_pathological_max_arrivals tsk arr_seq hresp_tsk js hjobs harrs
  have hcpos : 0 < task_cost tsk := by
    have hv := hcost js harrs
    unfold valid_job_cost at hv
    rw [htsk] at hv
    exact Nat.lt_of_lt_of_le hjpos (of_decide_eq_true hv)
  have hSIB := Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_is_bounded
    huni hsup _ hreflJ htransJ arr_seq hva sched hwb hvs hvpm hvm hrespE tsk
    (fun A => blocking_bound ts tsk A)
    (fun j t1 t2 _ hjob hpref =>
      Prosa.Analysis.Facts.BlockingBound.Edf.nonpreemptive_segments_bounded_by_blocking arr_seq hva sched hcost
        hvm ts hall tsk hin hresp j hjob t1 t2 hpref)
  have hintra := Prosa.Analysis.Abstract.RestrictedSupply.TaskIntraInterferenceBound.instantiated_task_intra_interference_is_bounded
    huni hsup hcons hreflJ arr_seq hva sched hfrom hmust hcde tsk _ hSIB
    (bound_on_athep_workload ts tsk)
    (Prosa.Analysis.Facts.Workload.EdfAthepBound.bound_on_athep_workload_is_valid arr_seq hva hcost ts hall hresp
      tsk sched)
  have hbounded := Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Edf.busy_intervals_are_bounded_rs_edf
    huni hsup hcons arr_seq hva sched hwb hvs hvpm hvm hrespE hwcA ts hall hcost hresp tsk hin SBF hsbf hunit
    L hL hpi hfix
  have hsbfA : Prosa.Analysis.Abstract.RestrictedSupply.BusySbf.valid_busy_sbf arr_seq sched tsk
      SBF.supply_bound_function :=
    Prosa.Analysis.Facts.SBF.valid_pred_sbf_switch_predicate arr_seq sched _ _
      (fun j t1 t2 harr hP => ⟨hP.1, (instantiated_busy_interval_prefix_equivalent_busy_interval_prefix huni hsup
        hcons arr_seq hva sched hfrom hmust hcde hreflJ j harr t1 t2).mpr hP.2⟩) hsbf
  refine Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq
    huni hsup hcons arr_seq hva sched hfrom hmust hcde hcost ts tsk hin hvpm
    (fully_nonpreemptive_valid_task_run_to_completion_threshold arr_seq tsk hcpos) hvalid hresp hwcA
    (EDF_implies_sequential_tasks huni arr_seq hva sched hwb hvs hvpm hrespE)
    (instantiated_interference_and_workload_consistent_with_sequential_tasks huni hsup hcons arr_seq hva sched
      hfrom hmust hcde hreflJ tsk EDF_respects_sequential_tasks)
    L hbounded SBF hsbfA hunit _ hintra R ?_ js harrs hjobs
  · intro A hA
    obtain ⟨F, hF1, hF2, hFle⟩ := hsol A (search_space_sub ts hvalid tsk hin L hL hcpos hma A hA)
    refine ⟨F, hFle, ?_, ?_⟩
    · show task_request_bound_function tsk (A + 1) - (task_cost tsk - 1) +
          (blocking_bound ts tsk A + bound_on_athep_workload ts tsk A F) ≤ SBF.supply_bound_function F
      ((try dsimp only [instant, duration, work] at *) <;> omega)
    · show SBF.supply_bound_function F + (task_cost tsk - 1) ≤ SBF.supply_bound_function (A + R)
      exact hF2

end Prosa.Results.Rta.Rs.Edf.FullyNonpreemptive
