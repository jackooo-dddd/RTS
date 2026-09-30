-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/exc/fp/fully_nonpreemptive.v

import Prosa.Results.Rta.Rs.Fp.FullyNonpreemptive
import Prosa.Analysis.Facts.Model.Exceedance.SBF
import Prosa.Model.Composite.ValidTaskArrivalSequence

namespace Prosa.Results.Rta.Exc.Fp.FullyNonpreemptive

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
open Prosa.Model.Readiness.Sequential
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Processor.IdealUniExceed
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.BlockingBound.Fp
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fp
open Prosa.Model.Composite.ValidTaskArrivalSequence
open Prosa.Analysis.Facts.Model.IdealUniExceed
open Prosa.Analysis.Facts.Model.Exceedance.SBF

/-! Response-time analysis for fully nonpreemptive fixed-priority scheduling of sporadic tasks with arbitrary
arrival curves on an ideal uniprocessor with exceedance executions, whose exceedance within every busy-interval
prefix of the task under analysis is bounded by `e`.

Binders follow the elaborated source types: each declaration takes the section inputs and hypotheses it uses, in
their elaborated order. The processor model is the accepted exceedance processor state; the source's section-local
instances are the accepted `sequential_ready_instance arr_seq` (the local `sequential_readiness`),
`fully_nonpreemptive_job_model` and `fully_nonpreemptive_task_model`, passed explicitly where the elaborated
statements use them implicitly; the FP policy acts on jobs through the accepted `FP_to_JLFP`. Representation: a
Boolean in `Prop` position is `= true`; `x \in xs` is `decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`; `ε` is `1`;
`\sum_(t1 <= t < t2) F t` is the `Finset.Ico` sum over `Nat` (= `instant`); `nat_of_bool` is `Bool.toNat`.

The proof instantiates the accepted restricted-supply fully nonpreemptive FP theorem with the exceedance processor
model (uniprocessor, unit supply and full consumption are its accepted facts) and the accepted SBF
`EPS_SBF_inst e = Δ - e` of `analysis/facts/model/exceedance/SBF.v` (valid and unit by its accepted facts); the
recurrences carry over because the SBF is the interval length minus `e`. -/

/-- `L` is a solution of the busy-window recurrence, with the exceedance budget `e`. -/
def busy_window_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) [FP : FP_policy Task] (e : work) (tsk : Task) (L : Nat) : Prop :=
  e < L ∧
    @blocking_bound Task _ fully_nonpreemptive_task_model FP ts tsk +
      total_hep_request_bound_function_FP ts tsk L + e ≤ L

/-- `R` solves the response-time recurrence, with the exceedance budget `e`, for every offset of the search
space. -/
def rta_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) [FP : FP_policy Task] (e : work) (tsk : Task) (L : duration) (R : Nat) : Prop :=
  ∀ A : duration, is_in_search_space tsk L A = true →
    ∃ F : duration,
      @blocking_bound Task _ fully_nonpreemptive_task_model FP ts tsk +
          (task_request_bound_function tsk (A + 1) - (task_cost tsk - 1)) +
          total_ohep_request_bound_function_FP ts tsk F + e ≤ F ∧
      F + (task_cost tsk - 1) ≤ A + R

/-- Response-time bound for fully nonpreemptive FP scheduling on an ideal uniprocessor with bounded exceedance
executions. -/
theorem uniprocessor_response_time_bound_fully_nonpreemptive_fp {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    [JobArrival Job] (arr_seq : arrival_sequence Job) (ts : List Task) :
    valid_task_arrival_sequence ts arr_seq →
    ∀ sched : schedule (exceedance_proc_state Job),
      @valid_schedule Job _ _ (exceedance_proc_state Job) sched _ (sequential_ready_instance (Task := Task) arr_seq)
        arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (exceedance_proc_state Job)
        (sequential_ready_instance (Task := Task) arr_seq) arr_seq sched →
      nonpreemptive_schedule sched →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP → transitive_task_priorities FP →
      @respects_FP_policy_at_preemption_point Task _ Job _ _ _ _ (exceedance_proc_state Job)
        fully_nonpreemptive_job_model (sequential_ready_instance (Task := Task) arr_seq) arr_seq sched FP →
    ∀ (e : work) (tsk : Task), decide (tsk ∈ ts) = true →
      (∀ (j : Job) (t1 t2 : instant), arrives_in arr_seq j → job_of_task tsk j = true →
        @busy_interval_prefix Job _ _ _ (exceedance_proc_state Job) arr_seq sched (FP_to_JLFP FP) j t1 t2 →
        ∑ t ∈ Finset.Ico (α := Nat) t1 t2, (is_exceedance_exec (sched t)).toNat ≤ e) →
    ∀ L : duration, busy_window_recurrence_solution ts (FP := FP) e tsk L →
    ∀ R : duration, rta_recurrence_solution ts (FP := FP) e tsk L R →
      task_response_time_bound arr_seq sched tsk R := by
  intro hvtas sched hvs hwc hnps FP hrefl htrans hresp e tsk hin hexc L hbw R hsol
  have hva := valid_task_arrival_sequence_valid_arrivals ts arr_seq hvtas
  have hcost := valid_task_arrival_sequence_valid_costs ts arr_seq hvtas
  have hall := valid_task_arrival_sequence_from_taskset ts arr_seq hvtas
  have hrespma := valid_task_arrival_sequence_respects_max ts arr_seq hvtas
  have hvalid := valid_task_arrival_sequence_valid_curve ts arr_seq hvtas
  have hsbf := @eps_sbf_is_valid Task _ Job _ _ _ _ (FP_to_JLFP FP) arr_seq sched e tsk hexc
  obtain ⟨hL, hfix⟩ := hbw
  refine Prosa.Results.Rta.Rs.Fp.FullyNonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp
    eps_is_uniproc eps_is_unit_supply eps_is_fully_consuming arr_seq hva hcost ts hall hrespma hvalid tsk hin
    sched hvs hwc hnps FP hrefl htrans hresp (EPS_SBF_inst e) (eps_sbf_is_unit e) hsbf L
    ⟨by ((try dsimp only [instant, duration, work] at *); omega), ?_⟩ R ?_
  · show _ ≤ L - e
    ((try dsimp only [instant, duration, work] at *); omega)
  · intro A hA
    obtain ⟨F, hF, hFR⟩ := hsol A hA
    refine ⟨F, ?_, ?_, ?_⟩
    · show _ ≤ F - e
      ((try dsimp only [instant, duration, work] at *); omega)
    · show F - e + (task_cost tsk - 1) ≤ A + R - e
      ((try dsimp only [instant, duration, work] at *); omega)
    · ((try dsimp only [instant, duration, work] at *); omega)

end Prosa.Results.Rta.Exc.Fp.FullyNonpreemptive
