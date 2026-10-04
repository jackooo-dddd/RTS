-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/bounded_bi/aux.v

import Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation
import Prosa.Analysis.Abstract.BusyInterval

namespace Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Definitions.ServiceInversion.Pred
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation
open Prosa.Analysis.Facts.Interference
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service

/-! Helper lemmas for the bounded-busy-interval lemmas of the restricted-supply
analysis.

Binders follow the elaborated source types: every lemma takes only the section
inputs and hypotheses it uses, in their elaborated order (the unused section
`Task`, `TaskCost`, `JobTask` and the work-bearing-readiness hypothesis are
absent, as in the elaborated types); instance inputs quantified after a
hypothesis are `∀ [..]` binders at that position. The source's section-local
instances `rs_jlfp_interference` and `rs_jlfp_interfering_workload` are the
accepted definitions of the same names, passed explicitly where the elaborated
statements use them implicitly. The classical and abstract busy-interval
notions are distinguished by namespace. Representation: a Boolean in `Prop`
position is `= true`; `a < b < c` is a Boolean conjunction of decides;
`n.+1` is `n + 1`. -/

/-- A pending job at its arrival lies in a (possibly unbounded) busy-interval
prefix starting no later than its arrival. -/
theorem busy_interval_prefix_exists {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState → fully_consuming_proc_model PState →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) [JobReady Job PState], valid_schedule sched arr_seq →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
      ∃ t1 : Nat, t1 ≤ job_arrival j ∧
        Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1
          (job_arrival j + 1) := by
  intro huni hsup hcons JLFP hrefl arr_seq hva sched _ hvs j harr hpos
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hfrom := valid_schedule_jobs_come_from_arrival_sequence sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hpos' : 0 < job_cost j := by
    unfold job_cost_positive at hpos; exact of_decide_eq_true hpos
  have hpend := job_pending_at_arrival sched j hpos' hmust
  letI := rs_jlfp_interference arr_seq sched
  letI := rs_jlfp_interfering_workload arr_seq sched
  obtain ⟨t1, hpref, hle⟩ :=
    Prosa.Analysis.Abstract.BusyInterval.exists_busy_interval_prefix sched j (job_arrival j) hpend
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hle
  exact ⟨t1, hle.1, (instantiated_busy_interval_prefix_equivalent_busy_interval_prefix huni hsup hcons
    arr_seq hva sched hfrom hmust hcde hrefl j harr t1 _).mpr hpref⟩

/-- Inside a busy-interval prefix, the service of higher-or-equal-priority
jobs is strictly less than their workload. -/
theorem service_lt_workload_in_busy {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    unit_supply_proc_model PState →
    ∀ [JLFP : JLFP_policy Job] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) [JobReady Job PState], valid_schedule sched arr_seq →
    ∀ j : Job, job_cost_positive j = true →
    ∀ t1 t2 : instant,
      Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
      ∀ t : Nat, (decide (t1 < t) && decide (t < t2)) = true →
        service_of_hep_jobs arr_seq sched j t1 t < workload_of_hep_jobs arr_seq j t1 t := by
  intro hsup JLFP arr_seq hva sched _ hvs j _ t1 t2 hpref t ht
  have hu := unit_supply_is_unit_service PState hsup
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hle := service_of_jobs_le_workload hu sched hcde (fun jhp => hep_job jhp j)
    (arrivals_between arr_seq t1 t) t1 t
  apply Nat.lt_of_not_le
  intro hge
  have heq : workload_of_jobs (fun jhp => hep_job jhp j) (arrivals_between arr_seq t1 t) =
      service_of_jobs sched (fun jhp => hep_job jhp j) (arrivals_between arr_seq t1 t) t1 t := by
    unfold service_of_hep_jobs workload_of_hep_jobs at hge
    exact Nat.le_antisymm hge hle
  obtain ⟨_, hq1, hnq, _⟩ := hpref
  have ht' := ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
  apply hnq t ht
  intro s hs hhep hbef
  by_cases hlt : job_arrival s < t1
  · exact completion_monotonic sched s t1 t (Nat.le_of_lt ht'.1)
      (hq1 s hs hhep (by simp [arrived_before, hlt]))
  · refine workload_eq_service_impl_all_jobs_have_completed hu arr_seq hva.1 sched hmust hcde _ t1 t t heq s
      (arrived_between_implies_in_arrivals arr_seq hva.1 s t1 t hs ?_) hhep
    unfold arrived_before at hbef
    simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at hbef ⊢
    exact ⟨Nat.le_of_not_lt hlt, hbef⟩

/-- Within a busy-interval prefix, the workload of `j` plus the cumulative
interfering workload over `[t1, t1 + Δ)` strictly exceeds `Δ`. -/
theorem workload_exceeds_interval {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState → fully_consuming_proc_model PState →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) [JobReady Job PState], valid_schedule sched arr_seq →
      @Prosa.Analysis.Abstract.Definitions.work_conserving Job _ (rs_jlfp_interference arr_seq sched)
        (rs_jlfp_interfering_workload arr_seq sched) _ _ _ arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant,
      Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
      ∀ Δ : Nat, 0 < Δ → t1 + Δ < t2 →
        Δ < workload_of_job arr_seq j t1 (t1 + Δ) +
          @cumulative_interfering_workload Job _ (rs_jlfp_interfering_workload arr_seq sched) j t1 (t1 + Δ) := by
  intro huni hsup hcons JLFP hrefl arr_seq hva sched _ hvs hwc j harr hpos t1 t2 hpref Δ hΔ hlt
  have hu := unit_supply_is_unit_service PState hsup
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hfrom := valid_schedule_jobs_come_from_arrival_sequence sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hpos' : 0 < job_cost j := by
    unfold job_cost_positive at hpos; exact of_decide_eq_true hpos
  have habs := (instantiated_busy_interval_prefix_equivalent_busy_interval_prefix huni hsup hcons
    arr_seq hva sched hfrom hmust hcde hrefl j harr t1 t2).mp hpref
  have hp0 := hpref
  obtain ⟨_, hq1, _, harr1⟩ := hp0
  simp only [Bool.and_eq_true, decide_eq_true_eq] at harr1
  -- every instant of the window is either interference or service of `j`
  have hstep : Δ ≤ service_during sched j t1 (t1 + Δ) +
      @cumulative_interference Job _ (rs_jlfp_interference arr_seq sched) j t1 (t1 + Δ) := by
    unfold service_during cumulative_interference cumul_cond_interference cond_interference
    rw [← Finset.sum_add_distrib]
    calc Δ = ∑ _x ∈ Finset.Ico t1 (t1 + Δ), (1 : Nat) := (Prosa.Util.Sum.sum_of_ones t1 Δ).symm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.mem_Ico] at hx
        have hw := hwc j t1 t2 x harr hpos' habs ⟨hx.1, by omega'⟩
        cases hi : (rs_jlfp_interference arr_seq sched).interference j x
        · have hs := hw.mp (by simp [hi])
          unfold receives_service_at at hs
          have := of_decide_eq_true hs
          simp only [Bool.and_false, Bool.toNat_false, Nat.add_zero]
          omega'
        · simp
  rw [cumulative_interference_split huni hcons arr_seq hva sched hfrom hmust hrefl j t1 (t1 + Δ)] at hstep
  rw [cumulative_interfering_workload_split arr_seq sched j t1 (t1 + Δ),
    cumulative_iw_hep_eq_workload_of_ohep arr_seq t1 (t1 + Δ) j]
  rw [cumulative_i_ohep_eq_service_of_ohep huni arr_seq hva sched hmust hcde JLFP hu j t1 (t1 + Δ) hq1]
    at hstep
  have hsvc := service_plus_ahep_eq_service_hep arr_seq hva sched hmust JLFP hrefl t1 (t1 + Δ) j harr harr1.1
  have hwl := workload_job_and_ahep_eq_workload_hep arr_seq JLFP hrefl j t1 (t1 + Δ)
  have hlt' := service_lt_workload_in_busy hsup arr_seq hva sched hvs j hpos t1 t2 hpref
    (t1 + Δ) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by omega', hlt⟩)
  omega'

end Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary
