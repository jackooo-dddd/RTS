-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/bounded_bi/jlfp.v

import Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta
import Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation
import Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary
import Prosa.Analysis.Definitions.Sbf.Busy
import Prosa.Analysis.Facts.BusyInterval.CarryIn

namespace Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Jlfp

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
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Aggregate.Workload
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.ServiceInversion.Pred
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation
open Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Model.Rbf

/-! Bounded busy intervals under JLFP scheduling on a restricted-supply
uniprocessor: for a service-inversion bound `blocking_bound` maximal at `0`,
`blocking_bound 0 + total_rbf L ≤ SBF L` bounds the busy intervals of `tsk`
by `L`.

Binders follow the elaborated source type: the section inputs and hypotheses
the lemma uses, in their elaborated order (the unused arrival-curve validity
hypothesis and the unused transitivity hypothesis are absent, as in the
elaborated type); instance inputs quantified
after a hypothesis are `∀ [..]` binders at that position. The source's
section-local instances `rs_jlfp_interference` and
`rs_jlfp_interfering_workload` are the accepted definitions of the same names
over the JLFP policy, passed explicitly where the elaborated statement uses
them implicitly. The busy-SBF validity is the classical one of
`analysis/definitions/sbf/busy.v`, and the service inversion bound the
classical one of `analysis/definitions/service_inversion/busy_prefix.v` (the
names the elaborated type resolves to, checked in the official environment); the
supply bound function is applied through its accepted class field.
Representation: a Boolean in `Prop` position is `= true`; `x \in xs` is
`decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`. The source's local case lemmas are inlined into the
proof. -/

theorem busy_intervals_are_bounded_rs_jlfp {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState → fully_consuming_proc_model PState →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) [JobReady Job PState], valid_schedule sched arr_seq →
      @Prosa.Analysis.Abstract.Definitions.work_conserving Job _
        (@rs_jlfp_interference Job _ PState arr_seq sched JLFP)
        (@rs_jlfp_interfering_workload Job _ _ PState arr_seq sched JLFP) _ _ _ arr_seq sched →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ SBF : SupplyBoundFunction,
      @Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf Task _ Job _ _ _ _ PState arr_seq sched
        JLFP tsk SBF.supply_bound_function →
      unit_supply_bound_function SBF.supply_bound_function →
    ∀ blocking_bound : duration → duration,
      Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix.service_inversion_is_bounded_by arr_seq sched tsk
        blocking_bound →
      (∀ A : duration, blocking_bound A ≤ blocking_bound 0) →
    ∀ L : duration, 0 < L →
      blocking_bound 0 + total_request_bound_function ts L ≤ SBF.supply_bound_function L →
      @busy_intervals_are_bounded_by Job _
        (@rs_jlfp_interference Job _ PState arr_seq sched JLFP)
        (@rs_jlfp_interfering_workload Job _ _ PState arr_seq sched JLFP) _ _ PState
        arr_seq sched Task _ _ tsk L := by
  intro huni hsup hcons JLFP hreflJ arr_seq hva sched _ hvs hwc ts hall hcost _
    hrespma tsk _ SBF hsbf hunitsbf B hSIB hBmax L hL hfix
  let _ := rs_jlfp_interference arr_seq sched
  let _ := rs_jlfp_interfering_workload arr_seq sched
  have hu := unit_supply_is_unit_service PState hsup
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hfrom := valid_schedule_jobs_come_from_arrival_sequence sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hSBFle : SBF.supply_bound_function L ≤ L :=
    sbf_bounded_by_duration arr_seq sched _ hsbf hunitsbf L
  -- the workload of `j` and the interfering workload over `[t1, t1 + L)` are bounded by `L`
  have hWL : ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → 0 < job_cost j →
      ∀ t1 t2 : instant,
        Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
        t1 + L ≤ t2 →
        workload_of_job arr_seq j t1 (t1 + L) + cumulative_interfering_workload j t1 (t1 + L) ≤ L := by
    intro j harr hjob hpos t1 t2 hpref hle
    rw [cumulative_interfering_workload_split arr_seq sched j t1 (t1 + L),
      cumulative_iw_hep_eq_workload_of_ohep arr_seq t1 (t1 + L) j]
    have hbl := Prosa.Analysis.Facts.SBF.blackout_during_bound_SBF hsup arr_seq sched _ hsbf j harr t1 t2
      ⟨hjob, hpref⟩ L hle
    have hsi1 := Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_widen arr_seq sched
      JLFP_to_JLDP j t1 (t1 + L) t1 t2 (Nat.le_refl _) hle
    have hsi2 := hSIB j harr hjob hpos t1 t2 hpref
    have hwl := workload_job_and_ahep_eq_workload_hep arr_seq JLFP hreflJ j t1 (t1 + L)
    have hrbf := hep_workload_le_total_rbf arr_seq hcost ts hall hrespma JLFP j t1 L
    have hBm := hBmax (job_arrival j - t1)
    omega'
  intro j harr hjob hcpos
  have hpos : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hcpos
  have hpend := job_pending_at_arrival sched j hcpos hmust
  obtain ⟨t1, hle1, hpref⟩ :=
    busy_interval_prefix_exists huni hsup hcons hreflJ arr_seq hva sched hvs j harr hpos
  have hequiv := fun t2 => instantiated_busy_interval_prefix_equivalent_busy_interval_prefix huni hsup hcons
    arr_seq hva sched hfrom hmust hcde hreflJ j harr t1 t2
  refine ⟨t1, ?_⟩
  by_cases hLpref : Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 (t1 + L)
  · -- Case 1: the busy-interval prefix continues until `t1 + L`
    have hnospec := instantiated_i_and_w_no_speculative_execution huni hsup hcons arr_seq hva sched hfrom hmust
      hcde hreflJ
    obtain ⟨t2, hlt2, hle2, hbusy⟩ := Prosa.Analysis.Abstract.BusyInterval.busy_interval_is_bounded hu hnospec
      arr_seq hva.1 hva.2 tsk sched hwc hmust hcde j harr hjob hpos (job_arrival j) hpend t1
      ((hequiv _).mp hpref) L hL (hWL j harr hjob hcpos t1 (t1 + L) hLpref (Nat.le_refl _))
    exact ⟨t2, ⟨hle1, hlt2⟩, hle2, hbusy⟩
  · -- Case 2: the busy-interval prefix terminates before `t1 + L`
    have harrL : job_arrival j < t1 + L := by
      apply Nat.lt_of_not_le
      intro hge
      have hex := workload_exceeds_interval huni hsup hcons hreflJ arr_seq hva sched hvs
        hwc j harr hpos t1 (job_arrival j + 1) hpref L hL (by omega')
      have hb := hWL j harr hjob hcpos t1 (job_arrival j + 1) hpref (by omega')
      omega'
    obtain ⟨t2, hbusy⟩ := Prosa.Analysis.Abstract.BusyInterval.terminating_busy_prefix_is_busy_interval sched j hpos
      t1 (job_arrival j + 1) (t1 + L) (by omega') ((hequiv _).mp hpref)
      (fun h => hLpref ((hequiv _).mpr h))
    have hcl := abstract_busy_interval_classic_busy_interval_prefix huni hsup hcons arr_seq hva sched hfrom hmust
      hcde hreflJ j harr t1 t2 hbusy
    obtain ⟨⟨_, hlt2⟩, _, _⟩ := hbusy.1
    refine ⟨t2, ⟨hle1, hlt2⟩, ?_, hbusy⟩
    apply Nat.le_of_not_lt
    intro hgt
    apply hLpref
    obtain ⟨_, hq1, hnq, _⟩ := hcl
    refine ⟨by omega', hq1, ?_, ?_⟩
    · intro t ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
      exact hnq t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    · simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'

end Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Jlfp
