-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/bounded_bi/elf.v

import Prosa.Analysis.Facts.BlockingBound.Elf
import Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta
import Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation
import Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary
import Prosa.Analysis.Definitions.Sbf.Busy
import Prosa.Analysis.Facts.Priority.JlfpWithFp

namespace Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Elf

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
open Prosa.Model.Priority.Gel
open Prosa.Model.Priority.Elf
open Prosa.Analysis.Definitions.BlockingBound.Elf
open Prosa.Analysis.Facts.Priority.Classes
open Prosa.Analysis.Facts.Priority.Elf
open Prosa.Util.Sum
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

/-! Bounded busy intervals under ELF scheduling on a restricted-supply
uniprocessor: `blocking_bound ts tsk A + total_hep_rbf L ≤ SBF L` for every
relative arrival `A` bounds the busy intervals of `tsk` by `L`.

Binders follow the elaborated source type: the section inputs and hypotheses
the lemma uses, in their elaborated order (the unused arrival-curve validity
hypothesis is absent, as in the elaborated type); instance inputs quantified
after a hypothesis are `∀ [..]` binders at that position. The source's
section-local instances `rs_jlfp_interference` and
`rs_jlfp_interfering_workload` are the accepted definitions of the same names
over the JLFP policy `ELF FP` (the accepted reducible definition), passed
explicitly where the elaborated statement uses them implicitly. The busy-SBF
validity is the classical one of `analysis/definitions/sbf/busy.v`; the
supply bound function is applied through its accepted class field.
Representation: a Boolean in `Prop` position is `= true`; `x \in xs` is
`decide (x ∈ xs) = true`. The source's local case lemmas are inlined into the
proof. -/

theorem busy_intervals_are_bounded_rs_elf {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [PriorityPoint Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState → fully_consuming_proc_model PState →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP → transitive_task_priorities FP →
      total_task_priorities FP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) [JobReady Job PState],
      @work_bearing_readiness Job _ _ _ PState _ arr_seq sched (ELF (Job := Job) FP) →
      valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job] [TaskMaxNonpreemptiveSegment Task], valid_preemption_model arr_seq sched →
      valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched (ELF (Job := Job) FP) →
      @Prosa.Analysis.Abstract.Definitions.work_conserving Job _
        (@rs_jlfp_interference Job _ PState arr_seq sched (ELF (Job := Job) FP))
        (@rs_jlfp_interfering_workload Job _ _ PState arr_seq sched (ELF (Job := Job) FP)) _ _ _ arr_seq sched →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ SBF : SupplyBoundFunction,
      @Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf Task _ Job _ _ _ _ PState arr_seq sched
        (ELF (Job := Job) FP) tsk SBF.supply_bound_function →
      unit_supply_bound_function SBF.supply_bound_function →
    ∀ L : duration, 0 < L →
      (∀ A : duration, blocking_bound ts (FP := FP) tsk A + total_hep_request_bound_function_FP ts (FP := FP) tsk L ≤
        SBF.supply_bound_function L) →
      @busy_intervals_are_bounded_by Job _
        (@rs_jlfp_interference Job _ PState arr_seq sched (ELF (Job := Job) FP))
        (@rs_jlfp_interfering_workload Job _ _ PState arr_seq sched (ELF (Job := Job) FP)) _ _ PState
        arr_seq sched Task _ _ tsk L := by
  intro huni hsup hcons FP hrefl htrans htot arr_seq hva sched _ hwb hvs _ _ hvpm hvm hresp hwc ts hall hcost _
    hrespma tsk hin SBF hsbf hunitsbf L hL hfix
  let _ : JLFP_policy Job := ELF (Job := Job) FP
  let _ := rs_jlfp_interference arr_seq sched
  let _ := rs_jlfp_interfering_workload arr_seq sched
  have hu := unit_supply_is_unit_service PState hsup
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hfrom := valid_schedule_jobs_come_from_arrival_sequence sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hreflJ := ELF_is_reflexive (Job := Job) FP hrefl
  have htransJ := ELF_is_transitive (Job := Job) FP htrans
  have hSBFle : SBF.supply_bound_function L ≤ L :=
    sbf_bounded_by_duration arr_seq sched _ hsbf hunitsbf L
  -- the service inversion within a busy-interval prefix is bounded by the blocking bound
  have hSIB := Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_is_bounded
    huni hsup (ELF (Job := Job) FP) hreflJ htransJ arr_seq hva sched hwb hvs hvpm hvm hresp tsk
    (fun A => blocking_bound ts (FP := FP) tsk A)
    (fun j t1 t2 _ hjob hpref =>
      Prosa.Analysis.Facts.BlockingBound.Elf.nonpreemptive_segments_bounded_by_blocking arr_seq hva sched
        hcost hvm ts hall tsk hin hrespma j hjob FP htot t1 t2 hpref)
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
    have hwl := workload_job_and_ahep_eq_workload_hep arr_seq (ELF (Job := Job) FP) hreflJ j t1 (t1 + L)
    have hj : job_task (Task := Task) j = tsk := of_decide_eq_true hjob
    have hrbf : workload_of_hep_jobs arr_seq j t1 (t1 + L) ≤
        total_hep_request_bound_function_FP ts (FP := FP) tsk L :=
      workload_of_jobs_bounded arr_seq hcost ts hall hrespma (fun jo => hep_job jo j)
        (fun o => FP.hep_task o tsk)
        (fun jo h => by
          have := hep_job_implies_hep_task (ELF (Job := Job) FP) FP (ELF_is_JLFP_FP_compatible FP) jo j h
          rw [hj] at this; exact this) t1 L
    have hfixA := hfix (job_arrival j - t1)
    omega'
  intro j harr hjob hcpos
  have hpos : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hcpos
  have hpend := job_pending_at_arrival sched j hcpos hmust
  obtain ⟨t1, hle1, hpref⟩ :=
    busy_interval_prefix_exists huni hsup hcons (JLFP := ELF (Job := Job) FP) hreflJ arr_seq hva sched hvs j harr hpos
  have hequiv := fun t2 => instantiated_busy_interval_prefix_equivalent_busy_interval_prefix huni hsup hcons
    arr_seq hva sched hfrom hmust hcde (JLFP := ELF (Job := Job) FP) hreflJ j harr t1 t2
  refine ⟨t1, ?_⟩
  by_cases hLpref : Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 (t1 + L)
  · -- Case 1: the busy-interval prefix continues until `t1 + L`
    have hnospec := instantiated_i_and_w_no_speculative_execution huni hsup hcons arr_seq hva sched hfrom hmust
      hcde (JLFP := ELF (Job := Job) FP) hreflJ
    obtain ⟨t2, hlt2, hle2, hbusy⟩ := Prosa.Analysis.Abstract.BusyInterval.busy_interval_is_bounded hu hnospec
      arr_seq hva.1 hva.2 tsk sched hwc hmust hcde j harr hjob hpos (job_arrival j) hpend t1
      ((hequiv _).mp hpref) L hL (hWL j harr hjob hcpos t1 (t1 + L) hLpref (Nat.le_refl _))
    exact ⟨t2, ⟨hle1, hlt2⟩, hle2, hbusy⟩
  · -- Case 2: the busy-interval prefix terminates before `t1 + L`
    have harrL : job_arrival j < t1 + L := by
      apply Nat.lt_of_not_le
      intro hge
      have hex := workload_exceeds_interval huni hsup hcons (JLFP := ELF (Job := Job) FP) hreflJ arr_seq hva sched hvs
        hwc j harr hpos t1 (job_arrival j + 1) hpref L hL (by omega')
      have hb := hWL j harr hjob hcpos t1 (job_arrival j + 1) hpref (by omega')
      omega'
    obtain ⟨t2, hbusy⟩ := Prosa.Analysis.Abstract.BusyInterval.terminating_busy_prefix_is_busy_interval sched j hpos
      t1 (job_arrival j + 1) (t1 + L) (by omega') ((hequiv _).mp hpref)
      (fun h => hLpref ((hequiv _).mpr h))
    have hcl := abstract_busy_interval_classic_busy_interval_prefix huni hsup hcons arr_seq hva sched hfrom hmust
      hcde (JLFP := ELF (Job := Job) FP) hreflJ j harr t1 t2 hbusy
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

end Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Elf
