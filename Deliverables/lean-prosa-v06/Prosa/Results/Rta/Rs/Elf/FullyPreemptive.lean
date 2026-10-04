-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/rs/elf/fully_preemptive.v

import Prosa.Analysis.Facts.Readiness.Basic
import Prosa.Analysis.Facts.Preemption.Task.Preemptive
import Prosa.Analysis.Facts.Preemption.RtcThreshold.Preemptive
import Prosa.Analysis.Abstract.RestrictedSupply.TaskIntraInterferenceBound
import Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Elf
import Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Elf
import Prosa.Analysis.Facts.Model.TaskCost
import Prosa.Analysis.Facts.Priority.Elf
import Prosa.Analysis.Facts.BlockingBound.Elf
import Prosa.Analysis.Facts.Workload.ElfAthepBound

namespace Prosa.Results.Rta.Rs.Elf.FullyPreemptive

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
open Prosa.Model.Task.Preemption.FullyPreemptive
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyPreemptive
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Priority.Gel
open Prosa.Model.Priority.Elf
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Processor.PlatformProperties
open Prosa.Util.Minmax
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.BlockingBound.Elf
open Prosa.Analysis.Definitions.Workload.ElfAthepBound
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation
open Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Elf
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Priority.Elf
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Facts.Preemption.Job.Preemptive
open Prosa.Analysis.Facts.Preemption.Task.Preemptive
open Prosa.Analysis.Facts.Preemption.RtcThreshold.Preemptive

/-! Response-time analysis for fully preemptive ELF scheduling of sporadic
tasks with arbitrary arrival curves on a uniprocessor with arbitrary supply
restrictions, by instantiating the accepted sequential abstract
restricted-supply analysis.

Binders follow the elaborated source types: each declaration takes the
section inputs and hypotheses it uses, in their elaborated order. The
source's section-local instances are passed explicitly where the elaborated
statements use them implicitly: the accepted `fully_preemptive_job_model`,
`fully_preemptive_task_model` and `fully_preemptive_rtc_threshold` and the
accepted `basic_ready_instance`. The ELF policy is the accepted reducible
`ELF FP`, passed explicitly. The busy-SBF validity is the classical one of
`analysis/definitions/sbf/busy.v`; the supply bound function is applied
through its accepted class field; `is_in_search_space` is the accepted ELF
search space and `bound_on_athep_workload` the accepted ELF athep bound.
Representation: a Boolean in `Prop` position is `= true`; `x \in xs` is
`decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`; `ε` is `1`. -/

/-- `L` is a positive solution of the busy-window recurrence. -/
def busy_window_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) (tsk : Task) [FP : FP_policy Task] (SBF : SupplyBoundFunction) (L : duration) : Prop :=
  0 < L ∧ total_hep_request_bound_function_FP ts (FP := FP) tsk L ≤ SBF.supply_bound_function L

/-- `R` solves the response-time recurrence for every offset of the search space. -/
def rta_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    [PriorityPoint Task] (ts : List Task) (tsk : Task) [FP : FP_policy Task] (SBF : SupplyBoundFunction)
    (L : duration) (R : Nat) : Prop :=
  ∀ A : duration, @is_in_search_space Task _ _ fully_preemptive_task_model _ ts _ FP tsk L A = true →
    ∃ F : duration,
      task_request_bound_function tsk (A + 1) + bound_on_athep_workload ts (FP := FP) tsk A F ≤
        SBF.supply_bound_function F ∧
      F ≤ A + R

/-- The ELF blocking bound vanishes in the fully preemptive task model. -/
private theorem blocking_bound_fully_preemptive {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [PriorityPoint Task] [MaxArrivals Task] (FP : FP_policy Task) (ts : List Task) (tsk : Task) (A : duration) :
    @blocking_bound Task _ _ fully_preemptive_task_model _ ts _ FP tsk A = 0 := by
  unfold blocking_bound bigMaxListCond
  induction ts with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    split <;> rfl

theorem uniprocessor_response_time_bound_fully_preemptive_elf {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] [PriorityPoint Task] {Job : JobType} [DecidableEq Job]
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
    ∀ FP : FP_policy Task, reflexive_task_priorities FP → transitive_task_priorities FP →
      total_task_priorities FP →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ PState fully_preemptive_job_model
        basic_ready_instance arr_seq sched (ELF (Job := Job) FP) →
    ∀ SBF : SupplyBoundFunction, sbf_is_monotone SBF.supply_bound_function →
      unit_supply_bound_function SBF.supply_bound_function →
      @Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf Task _ Job _ _ _ _ PState arr_seq sched
        (ELF (Job := Job) FP) tsk SBF.supply_bound_function →
    ∀ L : duration, busy_window_recurrence_solution ts tsk (FP := FP) SBF L →
    ∀ R : duration, rta_recurrence_solution ts tsk (FP := FP) SBF L R →
      task_response_time_bound arr_seq sched tsk R := by
  intro huni hsup hcons arr_seq hva hcost ts hall hresp hvalid tsk hin sched hvs hwc FP hrefl htrans htot hrespE
    SBF hmono hunit hsbf L hbw R hsol
  obtain ⟨hL, hfix⟩ := hbw
  intro js harrs hjobs
  by_cases hzero : job_cost js = 0
  · unfold job_response_time_bound completed_by
    apply decide_eq_true; rw [hzero]; exact Nat.zero_le _
  have hjpos : 0 < job_cost js := Nat.pos_of_ne_zero hzero
  let _ : JobReady Job PState := basic_ready_instance
  let _ : JobPreemptable Job := fully_preemptive_job_model
  let _ : TaskMaxNonpreemptiveSegment Task := fully_preemptive_task_model
  let _ : TaskRunToCompletionThreshold Task := fully_preemptive_rtc_threshold
  let _ : JLFP_policy Job := ELF (Job := Job) FP
  let _ := rs_jlfp_interference arr_seq sched
  let _ := rs_jlfp_interfering_workload arr_seq sched
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hfrom := valid_schedule_jobs_come_from_arrival_sequence sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hreflJ := ELF_is_reflexive (Job := Job) FP hrefl
  have htransJ := ELF_is_transitive (Job := Job) FP htrans
  have hwb := basic_readiness_is_work_bearing_readiness arr_seq sched hreflJ
  have hvpm := valid_fully_preemptive_model arr_seq sched
  have hvm : valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched :=
    ⟨hvpm, fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions arr_seq⟩
  have hB := blocking_bound_fully_preemptive FP ts tsk
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
    (fun A => blocking_bound ts (FP := FP) tsk A)
    (fun j t1 t2 _ hjob hpref =>
      Prosa.Analysis.Facts.BlockingBound.Elf.nonpreemptive_segments_bounded_by_blocking arr_seq hva sched hcost
        hvm ts hall tsk hin hresp j hjob FP htot t1 t2 hpref)
  have hintra := Prosa.Analysis.Abstract.RestrictedSupply.TaskIntraInterferenceBound.instantiated_task_intra_interference_is_bounded
    huni hsup hcons hreflJ arr_seq hva sched hfrom hmust hcde tsk _ hSIB
    (bound_on_athep_workload ts (FP := FP) tsk)
    (Prosa.Analysis.Facts.Workload.ElfAthepBound.bound_on_athep_workload_is_valid arr_seq hva hcost ts hall hresp
      tsk sched FP)
  have hbounded := Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Elf.busy_intervals_are_bounded_rs_elf
    huni hsup hcons FP hrefl htrans htot arr_seq hva sched hwb hvs hvpm hvm hrespE hwcA ts hall hcost hresp tsk hin
    SBF hsbf hunit L hL (fun A => by rw [hB, Nat.zero_add]; exact hfix)
  have hsbfA : Prosa.Analysis.Abstract.RestrictedSupply.BusySbf.valid_busy_sbf arr_seq sched tsk
      SBF.supply_bound_function :=
    Prosa.Analysis.Facts.SBF.valid_pred_sbf_switch_predicate arr_seq sched _ _
      (fun j t1 t2 harr hP => ⟨hP.1, (instantiated_busy_interval_prefix_equivalent_busy_interval_prefix huni hsup
        hcons arr_seq hva sched hfrom hmust hcde hreflJ j harr t1 t2).mpr hP.2⟩) hsbf
  refine Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq
    huni hsup hcons arr_seq hva sched hfrom hmust hcde hcost ts tsk hin hvpm
    (fully_preemptive_valid_task_run_to_completion_threshold arr_seq hcost tsk) hvalid hresp hwcA
    (ELF_implies_sequential_tasks FP hrefl htrans arr_seq hva PState huni sched hwb hvs hvpm hrespE)
    (instantiated_interference_and_workload_consistent_with_sequential_tasks huni hsup hcons arr_seq hva sched
      hfrom hmust hcde hreflJ tsk (ELF_respects_sequential_tasks FP hrefl))
    L hbounded SBF hsbfA hunit _ hintra R ?_ js harrs hjobs
  · intro A hA
    obtain ⟨F, hF, hFle⟩ := hsol A (search_space_sub ts hvalid FP tsk hin L hL hcpos hma A hA)
    refine ⟨F, hFle, ?_, ?_⟩
    · show task_request_bound_function tsk (A + 1) - (task_cost tsk - task_cost tsk) +
          (blocking_bound ts (FP := FP) tsk A + bound_on_athep_workload ts (FP := FP) tsk A F) ≤
        SBF.supply_bound_function F
      rw [hB]; ((try dsimp only [instant, duration, work] at *) <;> omega)
    · show SBF.supply_bound_function F + (task_cost tsk - task_cost tsk) ≤ SBF.supply_bound_function (A + R)
      have := of_decide_eq_true (hmono F (A + R) (decide_eq_true hFle))
      ((try dsimp only [instant, duration, work] at *) <;> omega)

end Prosa.Results.Rta.Rs.Elf.FullyPreemptive
