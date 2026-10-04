-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/abstract_seq_rta.v

import Prosa.Analysis.Facts.Model.Rbf
import Prosa.Analysis.Abstract.IBF.SupplyTask
import Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta

namespace Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta

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
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.PlatformProperties
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.SearchSpace
open Prosa.Analysis.Abstract.IwAuxiliary
open Prosa.Analysis.Abstract.AbstractRta
open Prosa.Analysis.Abstract.IBF.Supply
open Prosa.Analysis.Abstract.IBF.Task
open Prosa.Analysis.Abstract.IBF.SupplyTask
open Prosa.Analysis.Abstract.RestrictedSupply.BusySbf
open Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta

/-! Abstract response-time analysis for restricted-supply uniprocessors with
sequential tasks. Binders follow the elaborated source types: every
declaration takes only the section inputs and hypotheses it uses, in their
elaborated order; instance inputs quantified after a hypothesis are `∀ [..]`
binders at that position. Representation: a Boolean in `Prop` position is
`= true`; `tsk \in ts` is `decide (tsk ∈ ts) = true`; `ε` is `1`; the
definitional class `SupplyBoundFunction` is applied through its field
`supply_bound_function`; the section `Let`s `task_rbf`, `intra_IBF` and `IBF`
are inlined; the source's `search_space`-qualified `is_in_search_space` is the
abstract search space. -/

section AbstractRTARestrictedSupplySequential

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- In the preemptive stage, the intra-supply interference is bounded by the
remaining workload of the task's earlier jobs plus the task intra-supply
interference. -/
theorem IBF_P_bounds_interference [TaskCost Task] [JobTask Job Task] [JobArrival Job] [jc : JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
    ∀ [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
    ∀ [Interference Job] [InterferingWorkload Job], work_conserving arr_seq sched →
      sequential_tasks (Task := Task) arr_seq sched →
      interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk →
    ∀ task_intra_IBF : duration → duration → duration,
      task_intra_interference_is_bounded_by arr_seq sched tsk task_intra_IBF →
      intra_interference_is_bounded_by arr_seq sched tsk
        (fun A Δ => task_request_bound_function tsk (A + 1) - task_cost tsk + task_intra_IBF A Δ) := by
  intro huni hsup arr_seq hva sched hfrom hmust hcde hvjc ts tsk hin _ hresp _ _ hwc hseq hcons tIBF htib
    t1 t2 Δ j hj htsk hbi hlt hnc A hA
  have hAeq := hA t1 t2 hbi
  have hpos : job_cost_positive j = true := by
    unfold job_cost_positive
    apply decide_eq_true
    rcases Nat.eq_zero_or_pos (job_cost j) with h0 | h
    · exfalso
      unfold completed_by at hnc
      rw [h0] at hnc
      simp at hnc
    · exact h
  have hsplit := cumul_cond_interference_ID (fun _ t => has_supply sched t)
    (nonself (Task := Task) arr_seq sched) j t1 (t1 + Δ)
  have hfirst : cumul_cond_interference
      (fun j t => has_supply sched t && nonself (Task := Task) arr_seq sched j t) j t1 (t1 + Δ) ≤ tIBF A Δ := by
    rw [cumul_cond_interference_pred_eq _ (nonself_intra (Task := Task) arr_seq sched) j t1 (t1 + Δ)
      (fun j t => by unfold nonself_intra; rw [Bool.and_comm])]
    exact htib t1 t2 Δ j hj htsk hbi hlt hnc A hA
  have hcjb := cumulative_job_interference_bound huni (unit_supply_is_unit_service PState hsup) arr_seq hva sched
    hfrom hmust hcde hvjc ts tsk hin hresp hwc hseq hcons j hj htsk hpos t1 t2 hbi Δ hlt hnc
  have hpw : cumul_cond_interference
      (fun j t => has_supply sched t && !nonself (Task := Task) arr_seq sched j t) j t1 (t1 + Δ) +
      cumul_task_interference (Task := Task) arr_seq sched j t1 (t1 + Δ) ≤
      cumulative_interference j t1 (t1 + Δ) := by
    unfold cumul_task_interference cumulative_interference cumul_cond_interference
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    unfold cond_interference
    dsimp only
    generalize interference j t = a
    generalize has_supply sched t = b
    generalize nonself (Task := Task) arr_seq sched j t = c
    cases a <;> cases b <;> cases c <;> decide
  rw [hAeq]
  rw [hAeq] at hfirst
  omega'

/-- A solution of the sequential restricted-supply recurrence solves the
general restricted-supply recurrence. -/
theorem sol_seq_rs_equation_impl_sol_rs_equation [TaskCost Task] [TaskRunToCompletionThreshold Task]
    [JobTask Job Task] [jc : JobCost Job] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true →
    valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ [MaxArrivals Task], valid_taskset_arrival_curve ts max_arrivals →
    ∀ (L : duration) (SBF : SupplyBoundFunction) (task_intra_IBF : duration → duration → duration)
      (R : duration),
      (∀ A : duration,
        is_in_search_space L
          (fun A0 Δ => task_request_bound_function tsk (A0 + 1) - task_cost tsk + task_intra_IBF A0 Δ) A →
        ∃ F : duration, F ≤ A + R ∧
          task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk) + task_intra_IBF A F ≤
            SBF.supply_bound_function F ∧
          SBF.supply_bound_function F + (task_cost tsk - task_rtct tsk) ≤ SBF.supply_bound_function (A + R)) →
      0 < max_arrivals tsk 1 →
      ∀ A : duration,
        is_in_search_space L
          (fun A0 Δ => Δ - SBF.supply_bound_function Δ +
            (task_request_bound_function tsk (A0 + 1) - task_cost tsk + task_intra_IBF A0 Δ)) A →
        ∃ F : duration, F ≤ A + R ∧
          task_rtct tsk + (task_request_bound_function tsk (A + 1) - task_cost tsk + task_intra_IBF A F) ≤
            SBF.supply_bound_function F ∧
          SBF.supply_bound_function F + (task_cost tsk - task_rtct tsk) ≤ SBF.supply_bound_function (A + R) := by
  intro hin hrtc _ hvac L SBF tIBF R hmax hpos A hsp
  have hsp' : is_in_search_space L
      (fun A0 Δ => task_request_bound_function tsk (A0 + 1) - task_cost tsk + tIBF A0 Δ) A := by
    rcases hsp with h0 | ⟨hA0, hAL, x, hx, hne⟩
    · exact Or.inl h0
    · refine Or.inr ⟨hA0, hAL, x, hx, ?_⟩
      intro heq
      apply hne
      simp only at heq ⊢
      rw [heq]
  obtain ⟨F, h0, h1, h2⟩ := hmax A hsp'
  refine ⟨F, h0, ?_, h2⟩
  have hle : task_rtct tsk ≤ task_cost tsk := of_decide_eq_true hrtc.1
  have hc1 : task_cost tsk ≤ task_request_bound_function tsk 1 := task_rbf_1_ge_task_cost tsk hpos
  have hmono := of_decide_eq_true
    (task_rbf_monotone tsk (hvac tsk hin) 1 (A + 1) (decide_eq_true (by omega')))
  omega'

/-- `R` bounds the response time of the jobs of `tsk` under restricted supply
and sequential tasks. -/
theorem uniprocessor_response_time_bound_restricted_supply_seq [TaskCost Task]
    [TaskRunToCompletionThreshold Task] [JobTask Job Task] [JobArrival Job] [jc : JobCost Job]
    [JobPreemptable Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState → fully_consuming_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
      valid_preemption_model arr_seq sched →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ [MaxArrivals Task], valid_taskset_arrival_curve ts max_arrivals →
      taskset_respects_max_arrivals arr_seq ts →
    ∀ [Interference Job] [InterferingWorkload Job], work_conserving arr_seq sched →
      sequential_tasks (Task := Task) arr_seq sched →
      interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk →
    ∀ L : duration, busy_intervals_are_bounded_by arr_seq sched tsk L →
    ∀ SBF : SupplyBoundFunction, valid_busy_sbf arr_seq sched tsk SBF.supply_bound_function →
      unit_supply_bound_function SBF.supply_bound_function →
    ∀ task_intra_IBF : duration → duration → duration,
      task_intra_interference_is_bounded_by arr_seq sched tsk task_intra_IBF →
    ∀ R : duration,
      (∀ A : duration,
        is_in_search_space L
          (fun A0 Δ => task_request_bound_function tsk (A0 + 1) - task_cost tsk + task_intra_IBF A0 Δ) A →
        ∃ F : duration, F ≤ A + R ∧
          task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk) + task_intra_IBF A F ≤
            SBF.supply_bound_function F ∧
          SBF.supply_bound_function F + (task_cost tsk - task_rtct tsk) ≤ SBF.supply_bound_function (A + R)) →
      task_response_time_bound arr_seq sched tsk R := by
  intro huni hsup hcons arr_seq hva sched hfrom hmust hcde hvjc ts tsk hin hpm hrtc _ hvac hresp _ _
    hwc hseq hconsist L hL SBF hsbf hunitsbf tIBF htib R hmax j hj htsk
  have hpos := non_pathological_max_arrivals tsk arr_seq (hresp tsk hin) j htsk hj
  exact uniprocessor_response_time_bound_restricted_supply hsup hcons arr_seq sched hmust hcde hvjc ts tsk hin
    hpm hrtc hwc L hL SBF hsbf hunitsbf _
    (IBF_P_bounds_interference huni hsup arr_seq hva sched hfrom hmust hcde hvjc ts tsk hin hresp hwc hseq
      hconsist tIBF htib) R
    (sol_seq_rs_equation_impl_sol_rs_equation arr_seq ts tsk hin hrtc hvac L SBF tIBF R hmax hpos)
    j hj htsk

end AbstractRTARestrictedSupplySequential

end Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta
