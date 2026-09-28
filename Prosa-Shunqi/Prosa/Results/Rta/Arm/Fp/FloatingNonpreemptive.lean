-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/arm/fp/floating_nonpreemptive.v

import Prosa.Analysis.Facts.Readiness.Basic
import Prosa.Model.Composite.ValidTaskArrivalSequence
import Prosa.Analysis.Facts.Model.Sbf.Average
import Prosa.Analysis.Abstract.RestrictedSupply.TaskIntraInterferenceBound
import Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Fp
import Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fp
import Prosa.Analysis.Facts.Model.TaskCost
import Prosa.Analysis.Facts.Preemption.RtcThreshold.Floating
import Prosa.Analysis.Facts.Preemption.Task.Floating

namespace Prosa.Results.Rta.Arm.Fp.FloatingNonpreemptive

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
open Prosa.Model.Task.Preemption.FloatingNonpreemptive
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.LimitedPreemptive
open Prosa.Model.Schedule.LimitedPreemptive
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
open Prosa.Analysis.Definitions.Sbf.Average
open Prosa.Analysis.Facts.Model.Sbf.Average
open Prosa.Analysis.Facts.Preemption.Job.Limited
open Prosa.Analysis.Facts.Preemption.Task.Floating
open Prosa.Analysis.Facts.Preemption.RtcThreshold.Floating

/-! Response-time analysis for fixed-priority scheduling with floating non-preemptive regions scheduling of
sporadic tasks with arbitrary arrival curves on a uniprocessor with
the average resource model, by instantiating the accepted sequential
abstract restricted-supply analysis.

Binders follow the elaborated source types: each declaration takes the
section inputs and hypotheses it uses, in their elaborated order. The
source's section-local instances are passed explicitly where the elaborated
statements use them implicitly: the accepted `limited_preemptive_job_model` (the proof uses the accepted
`floating_preemptive_rtc_threshold`), the
accepted `basic_ready_instance`
and the JLFP policy `FP_to_JLFP FP`. The supply bound function is the accepted `arm_sbf`; `is_in_search_space` is the accepted
FP search space. Representation: a Boolean in `Prop` position is `= true`;
`x \in xs` is `decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`; `ε` is `1`. -/

/-- `L` is a positive solution of the busy-window recurrence, including the
blocking bound. -/
def busy_window_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    [TaskMaxNonpreemptiveSegment Task] (ts : List Task) (tsk : Task) [FP : FP_policy Task] (Pi Θ ν : duration) (L : duration) : Prop :=
  0 < L ∧
    @blocking_bound Task _ _ FP ts tsk +
      total_hep_request_bound_function_FP ts (FP := FP) tsk L ≤ arm_sbf Pi Θ ν L

/-- `R` solves the response-time recurrence for every offset of the search space. -/
def rta_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    [TaskMaxNonpreemptiveSegment Task] (ts : List Task) (tsk : Task) [FP : FP_policy Task] (Pi Θ ν : duration) (L : duration) (R : Nat) : Prop :=
  ∀ A : duration, is_in_search_space tsk L A = true →
    ∃ F : duration,
      @blocking_bound Task _ _ FP ts tsk + task_request_bound_function tsk (A + 1) +
          total_ohep_request_bound_function_FP ts (FP := FP) tsk F ≤ arm_sbf Pi Θ ν F ∧
      F ≤ A + R

theorem uniprocessor_response_time_bound_floating_fp {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] [TaskMaxNonpreemptiveSegment Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobCost Job] [JobArrival Job] [JobPreemptionPoints Job] (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true →
    ∀ {PState : ProcessorState Job},
    uniprocessor_model PState → unit_supply_proc_model PState → fully_consuming_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_task_arrival_sequence ts arr_seq →
      valid_model_with_floating_nonpreemptive_regions (Task := Task) arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP → transitive_task_priorities FP →
    ∀ sched : schedule PState,
      @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ PState basic_ready_instance arr_seq sched →
      @schedule_respects_preemption_model Job _ PState limited_preemptive_job_model arr_seq sched →
      @respects_FP_policy_at_preemption_point Task _ Job _ _ _ _ PState limited_preemptive_job_model
        basic_ready_instance arr_seq sched FP →
      @Prosa.Model.Task.Sequentiality.sequential_tasks Job _ Task _ _ _ _ PState arr_seq sched →
    ∀ Pi Θ ν : duration, average_resource_model Pi Θ ν sched →
    ∀ L : duration, busy_window_recurrence_solution ts tsk (FP := FP) Pi Θ ν L →
    ∀ R : duration, rta_recurrence_solution ts tsk (FP := FP) Pi Θ ν L R →
      task_response_time_bound arr_seq sched tsk R := by
  intro hin PState huni hsup hcons arr_seq hvtas hfl FP hrefl htrans sched hvs hwc hrpm hrespFP hseq Pi Θ ν harm L hbw R hsol
  have hva := valid_task_arrival_sequence_valid_arrivals ts arr_seq hvtas
  have hcost := valid_task_arrival_sequence_valid_costs ts arr_seq hvtas
  have hall := valid_task_arrival_sequence_from_taskset ts arr_seq hvtas
  have hresp := valid_task_arrival_sequence_respects_max ts arr_seq hvtas
  have hvalid := valid_task_arrival_sequence_valid_curve ts arr_seq hvtas
  let SBF : SupplyBoundFunction := ⟨arm_sbf Pi Θ ν⟩
  have hmono : sbf_is_monotone SBF.supply_bound_function := arm_sbf_monotone Pi Θ ν
  have hunit : unit_supply_bound_function SBF.supply_bound_function := arm_sbf_unit sched Pi Θ ν harm
  have hsbf : @Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf Task _ Job _ _ _ _ PState arr_seq sched
      (FP_to_JLFP FP) tsk SBF.supply_bound_function :=
    Prosa.Analysis.Facts.SBF.valid_pred_sbf_switch_predicate arr_seq sched _ _ (fun _ _ _ _ _ => trivial)
      (arm_sbf_valid arr_seq sched Pi Θ ν harm)
  obtain ⟨hL, hfix⟩ := hbw
  intro js harrs hjobs
  by_cases hzero : job_cost js = 0
  · unfold job_response_time_bound completed_by
    apply decide_eq_true; rw [hzero]; exact Nat.zero_le _
  have hjpos : 0 < job_cost js := Nat.pos_of_ne_zero hzero
  let _ : JobReady Job PState := basic_ready_instance
  let _ : JobPreemptable Job := limited_preemptive_job_model
  let _ : TaskRunToCompletionThreshold Task := floating_preemptive_rtc_threshold
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
  have hvm : valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched :=
    floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions arr_seq sched hrpm hfl
  have hvpm := hvm.1
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
    (floating_preemptive_valid_task_run_to_completion_threshold arr_seq hcost tsk) hvalid hresp hwcA
    hseq
    (instantiated_interference_and_workload_consistent_with_sequential_tasks huni hsup hcons arr_seq hva sched
      hfrom hmust hcde hreflJ tsk (respects_sequential_tasks FP hrefl))
    L hbounded SBF hsbfA hunit _ hintra R ?_ js harrs hjobs
  · intro A hA
    have hsp : is_in_search_space tsk L A = true :=
      search_space_sub FP ts hvalid tsk hin L hL hcpos hma A hA
    obtain ⟨F, hF1, hFle⟩ := hsol A hsp
    refine ⟨F, hFle, ?_, ?_⟩
    · show task_request_bound_function tsk (A + 1) - (task_cost tsk - task_cost tsk) +
          (blocking_bound (FP := FP) ts tsk + total_ohep_request_bound_function_FP ts (FP := FP) tsk F) ≤
        arm_sbf Pi Θ ν F
      ((try dsimp only [instant, duration, work] at *) <;> omega)
    · show arm_sbf Pi Θ ν F + (task_cost tsk - task_cost tsk) ≤ arm_sbf Pi Θ ν (A + R)
      have : arm_sbf Pi Θ ν F ≤ arm_sbf Pi Θ ν (A + R) := of_decide_eq_true (hmono F (A + R) (decide_eq_true hFle))
      ((try dsimp only [instant, duration, work] at *) <;> omega)

end Prosa.Results.Rta.Arm.Fp.FloatingNonpreemptive
