-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/prm/fp/fully_nonpreemptive.v

import Prosa.Analysis.Facts.Readiness.Basic
import Prosa.Model.Composite.ValidTaskArrivalSequence
import Prosa.Analysis.Facts.Model.Sbf.Periodic
import Prosa.Analysis.Abstract.RestrictedSupply.TaskIntraInterferenceBound
import Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Fp
import Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fp
import Prosa.Analysis.Facts.Model.TaskCost
import Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive
import Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive

namespace Prosa.Results.Rta.Prm.Fp.FullyNonpreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.FullyNonpreemptive
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyNonpreemptive
open Prosa.Model.Schedule.Nonpreemptive
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Readiness.Basic
open Prosa.Model.Composite.ValidTaskArrivalSequence
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Processor.PlatformProperties
open Prosa.Util.Minmax
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.BlockingBound.Fp
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation
open Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fp
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Priority.Classes
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Definitions.Sbf.Periodic
open Prosa.Analysis.Facts.Model.Sbf.Periodic
open Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive
open Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive
open Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive

/-! Response-time analysis for fully non-preemptive fixed-priority scheduling of
sporadic tasks with arbitrary arrival curves on a uniprocessor with
the periodic resource model, by instantiating the accepted sequential
abstract restricted-supply analysis.

Binders follow the elaborated source types: each declaration takes the
section inputs and hypotheses it uses, in their elaborated order. The
source's section-local instances are passed explicitly where the elaborated
statements use them implicitly: the accepted `fully_nonpreemptive_job_model`,
`fully_nonpreemptive_task_model` and `fully_nonpreemptive_rtc_threshold`, the
accepted `basic_ready_instance`
and the JLFP policy `FP_to_JLFP FP`. The supply bound function is the accepted `prm_sbf`; `is_in_search_space` is the accepted
FP search space. Representation: a Boolean in `Prop` position is `= true`;
`x \in xs` is `decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`; `ε` is `1`. -/

/-- `L` is a positive solution of the busy-window recurrence, including the
blocking bound. -/
def busy_window_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) (tsk : Task) [FP : FP_policy Task] (Pi γ : duration) (L : duration) : Prop :=
  0 < L ∧
    @blocking_bound Task _ fully_nonpreemptive_task_model FP ts tsk +
      total_hep_request_bound_function_FP ts (FP := FP) tsk L ≤ prm_sbf Pi γ L

/-- `R` solves the response-time recurrence for every offset of the search space. -/
def rta_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) (tsk : Task) [FP : FP_policy Task] (Pi γ : duration) (L : duration) (R : Nat) : Prop :=
  ∀ A : duration, is_in_search_space tsk L A = true →
    ∃ F : duration,
      @blocking_bound Task _ fully_nonpreemptive_task_model FP ts tsk +
          (task_request_bound_function tsk (A + 1) - (task_cost tsk - 1)) +
          total_ohep_request_bound_function_FP ts (FP := FP) tsk F ≤ prm_sbf Pi γ F ∧
      prm_sbf Pi γ F + (task_cost tsk - 1) ≤ prm_sbf Pi γ (A + R) ∧
      F ≤ A + R

theorem uniprocessor_response_time_bound_fully_nonpreemptive_fp {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobCost Job] [JobArrival Job] (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true →
    ∀ {PState : ProcessorState Job},
    uniprocessor_model PState → unit_supply_proc_model PState → fully_consuming_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_task_arrival_sequence ts arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP → transitive_task_priorities FP →
    ∀ sched : schedule PState,
      @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ PState basic_ready_instance arr_seq sched →
      nonpreemptive_schedule sched →
      @respects_FP_policy_at_preemption_point Task _ Job _ _ _ _ PState fully_nonpreemptive_job_model
        basic_ready_instance arr_seq sched FP →
      @Prosa.Model.Task.Sequentiality.sequential_tasks Job _ Task _ _ _ _ PState arr_seq sched →
    ∀ Pi γ : duration, periodic_resource_model Pi γ sched →
    ∀ L : duration, busy_window_recurrence_solution ts tsk (FP := FP) Pi γ L →
    ∀ R : duration, rta_recurrence_solution ts tsk (FP := FP) Pi γ L R →
      task_response_time_bound arr_seq sched tsk R := by
  intro hin PState huni hsup hcons arr_seq hvtas FP hrefl htrans sched hvs hwc hnps hrespFP hseq Pi γ harm L hbw R hsol
  have hva := valid_task_arrival_sequence_valid_arrivals ts arr_seq hvtas
  have hcost := valid_task_arrival_sequence_valid_costs ts arr_seq hvtas
  have hall := valid_task_arrival_sequence_from_taskset ts arr_seq hvtas
  have hresp := valid_task_arrival_sequence_respects_max ts arr_seq hvtas
  have hvalid := valid_task_arrival_sequence_valid_curve ts arr_seq hvtas
  let SBF : SupplyBoundFunction := ⟨prm_sbf Pi γ⟩
  have hmono : sbf_is_monotone SBF.supply_bound_function := prm_sbf_monotone sched Pi γ harm
  have hunit : unit_supply_bound_function SBF.supply_bound_function := prm_sbf_unit sched Pi γ harm
  have hsbf : @Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf Task _ Job _ _ _ _ PState arr_seq sched
      (FP_to_JLFP FP) tsk SBF.supply_bound_function :=
    Prosa.Analysis.Facts.SBF.valid_pred_sbf_switch_predicate arr_seq sched _ _ (fun _ _ _ _ _ => trivial)
      (prm_sbf_valid hsup arr_seq sched Pi γ harm)
  obtain ⟨hL, hfix⟩ := hbw
  intro js harrs hjobs
  by_cases hzero : job_cost js = 0
  · unfold job_response_time_bound completed_by
    apply decide_eq_true; rw [hzero]; exact Nat.zero_le _
  have hjpos : 0 < job_cost js := Nat.pos_of_ne_zero hzero
  let _ : JobReady Job PState := basic_ready_instance
  let _ : JobPreemptable Job := fully_nonpreemptive_job_model
  let _ : TaskMaxNonpreemptiveSegment Task := fully_nonpreemptive_task_model
  let _ : TaskRunToCompletionThreshold Task := fully_nonpreemptive_rtc_threshold
  let _ : JLFP_policy Job := FP_to_JLFP FP
  let _ := rs_jlfp_interference arr_seq sched
  let _ := rs_jlfp_interfering_workload arr_seq sched
  have hu := unit_supply_is_unit_service PState hsup
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hfrom := valid_schedule_jobs_come_from_arrival_sequence sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hreflJ := reflexive_priorities_FP_implies_JLFP (Job := Job) FP hrefl
  have htransJ := transitive_priorities_FP_implies_JLFP (Job := Job) FP htrans
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
    huni hsup (FP_to_JLFP FP) hreflJ htransJ arr_seq hva sched hwb hvs hvpm hvm hrespFP tsk
    (fun _ => blocking_bound (FP := FP) ts tsk)
    (fun j t1 _ _ hjob _ =>
      Prosa.Analysis.Facts.BlockingBound.Fp.nonpreemptive_segments_bounded_by_blocking FP arr_seq sched
        hvm ts hall tsk j hjob t1)
  have hintra := Prosa.Analysis.Abstract.RestrictedSupply.TaskIntraInterferenceBound.instantiated_task_intra_interference_is_bounded
    huni hsup hcons hreflJ arr_seq hva sched hfrom hmust hcde tsk _ hSIB
    (fun _ Δ => total_ohep_request_bound_function_FP ts (FP := FP) tsk Δ)
    (athep_workload_le_total_ohep_rbf arr_seq sched hcost ts hall hresp FP tsk)
  have hbounded := Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Fp.busy_intervals_are_bounded_rs_fp
    huni hsup hcons FP hrefl htrans arr_seq hva sched hwb hvs hvpm hvm hrespFP hwcA ts hall hcost hresp tsk hin
    SBF hsbf hunit L hL hfix
  have hsbfA : Prosa.Analysis.Abstract.RestrictedSupply.BusySbf.valid_busy_sbf arr_seq sched tsk
      SBF.supply_bound_function :=
    Prosa.Analysis.Facts.SBF.valid_pred_sbf_switch_predicate arr_seq sched _ _
      (fun j t1 t2 harr hP => ⟨hP.1, (instantiated_busy_interval_prefix_equivalent_busy_interval_prefix huni hsup
        hcons arr_seq hva sched hfrom hmust hcde hreflJ j harr t1 t2).mpr hP.2⟩) hsbf
  refine Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq
    huni hsup hcons arr_seq hva sched hfrom hmust hcde hcost ts tsk hin hvpm
    (fully_nonpreemptive_valid_task_run_to_completion_threshold arr_seq tsk hcpos) hvalid hresp hwcA
    hseq
    (instantiated_interference_and_workload_consistent_with_sequential_tasks huni hsup hcons arr_seq hva sched
      hfrom hmust hcde hreflJ tsk (respects_sequential_tasks FP hrefl))
    L hbounded SBF hsbfA hunit _ hintra R ?_ js harrs hjobs
  · intro A hA
    have hsp : is_in_search_space tsk L A = true :=
      search_space_sub FP ts hvalid tsk hin L hL hcpos hma A hA
    obtain ⟨F, hF1, hF2, hFle⟩ := hsol A hsp
    change _ ≤ prm_sbf Pi γ F at hF1
    change _ ≤ prm_sbf Pi γ (A + R) at hF2
    refine ⟨F, hFle, ?_, ?_⟩
    · show task_request_bound_function tsk (A + 1) - (task_cost tsk - 1) +
          (blocking_bound (FP := FP) ts tsk + total_ohep_request_bound_function_FP ts (FP := FP) tsk F) ≤
        prm_sbf Pi γ F
      ((try dsimp only [instant, duration, work] at *) <;> omega)
    · show prm_sbf Pi γ F + (task_cost tsk - 1) ≤ prm_sbf Pi γ (A + R)
      exact hF2

end Prosa.Results.Rta.Prm.Fp.FullyNonpreemptive
