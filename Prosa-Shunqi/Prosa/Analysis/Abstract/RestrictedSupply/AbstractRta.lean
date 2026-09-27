-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/abstract_rta.v

import Prosa.Analysis.Facts.Behavior.Supply
import Prosa.Analysis.Facts.SBF
import Prosa.Analysis.Abstract.AbstractRta
import Prosa.Analysis.Abstract.IwAuxiliary
import Prosa.Analysis.Abstract.IBF.Supply
import Prosa.Analysis.Abstract.RestrictedSupply.BusySbf
import Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable

namespace Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.PlatformProperties
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Supply
open Prosa.Analysis.Facts.SBF
open Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.SearchSpace
open Prosa.Analysis.Abstract.BusyInterval
open Prosa.Analysis.Abstract.IwAuxiliary
open Prosa.Analysis.Abstract.LowerBoundOnService
open Prosa.Analysis.Abstract.AbstractRta
open Prosa.Analysis.Abstract.IBF.Supply
open Prosa.Analysis.Abstract.RestrictedSupply.BusySbf

/-! Abstract response-time analysis under restricted supply.
Binders follow the elaborated source types: every theorem takes only the
section inputs and hypotheses it uses, in their elaborated order; instance
inputs quantified after a hypothesis are `∀ [..]` binders at that position.
Representation: a Boolean in `Prop` position is `= true`; `~~ b` is
`(!b) = true`; `t1 <= t < t2` is `(decide (t1 ≤ t) && decide (t < t2)) = true`;
a Boolean in a Nat sum is `Bool.toNat`; `tsk \in ts` is
`decide (tsk ∈ ts) = true`; the single-field class `SupplyBoundFunction` is
applied through its field `supply_bound_function`. -/

section AbstractRTARestrictedSupply

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job]

/-- A blackout inside the busy-interval prefix of a pending job is interference. -/
theorem blackout_impl_interference [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true →
    ∀ [Interference Job] [InterferingWorkload Job],
    work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix sched j t1 t2 →
    ∀ Δ : duration, t1 + Δ < t2 → (!completed_by sched j (t1 + Δ)) = true →
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true →
      is_blackout sched t = true → interference j t = true := by
  intro _ _ _ hwc j ha _ hpos t1 t2 hbip _ _ _ t ht hb
  have hpos' : job_cost j > 0 := of_decide_eq_true hpos
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  cases hi : interference j t
  · have hr := (hwc j t1 t2 t ha hpos' hbip ht).mp (by rw [hi]; simp)
    have hsvc : 0 < service_at sched j t := of_decide_eq_true hr
    have hsup := pos_service_impl_pos_supply sched j t hsvc
    unfold is_blackout has_supply at hb
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hb
    exact absurd hsup hb
  · rfl

/-- Pointwise, interference splits into blackout and intra-supply interference. -/
theorem blackout_plus_local_is_interference [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true →
    ∀ [Interference Job] [InterferingWorkload Job],
    work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix sched j t1 t2 →
    ∀ Δ : duration, t1 + Δ < t2 → (!completed_by sched j (t1 + Δ)) = true →
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true →
      (is_blackout sched t).toNat + (intra_interference sched j t).toNat =
        (interference j t).toNat := by
  intro hts _ _ hwc j ha hjt hpos t1 t2 hbip Δ hlt hnc t ht
  unfold intra_interference cond_interference
  dsimp only
  cases hs : has_supply sched t
  · have hb : is_blackout sched t = true := by unfold is_blackout; rw [hs]; rfl
    rw [blackout_impl_interference arr_seq sched ts tsk hts hwc j ha hjt hpos t1 t2 hbip Δ hlt hnc t
      ht hb, hb]
    rfl
  · have hb : is_blackout sched t = false := by unfold is_blackout; rw [hs]; rfl
    rw [hb]
    simp

/-- Cumulatively, interference splits into blackouts and intra-supply interference. -/
theorem blackout_plus_local_is_interference_cumul [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true →
    ∀ [Interference Job] [InterferingWorkload Job],
    work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix sched j t1 t2 →
    ∀ Δ : duration, t1 + Δ < t2 → (!completed_by sched j (t1 + Δ)) = true →
      blackout_during sched t1 (t1 + Δ) + cumul_intra_interference sched j t1 (t1 + Δ) =
        cumulative_interference j t1 (t1 + Δ) := by
  intro hts _ _ hwc j ha hjt hpos t1 t2 hbip Δ hlt hnc
  unfold blackout_during cumul_intra_interference cumulative_interference cumul_cond_interference
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  have h := blackout_plus_local_is_interference arr_seq sched ts tsk hts hwc j ha hjt hpos t1 t2 hbip
    Δ hlt hnc t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
  unfold intra_interference at h
  rw [h]
  unfold cond_interference
  simp

/-- Cumulative interference is bounded by the SBF complement plus the
intra-supply interference. -/
theorem cumulative_job_interference_bound [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    unit_supply_proc_model PState →
    ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState) (ts : List Task) (tsk : Task),
    decide (tsk ∈ ts) = true →
    ∀ [Interference Job] [InterferingWorkload Job],
    work_conserving arr_seq sched →
    ∀ SBF : SupplyBoundFunction, valid_busy_sbf arr_seq sched tsk SBF.supply_bound_function →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix sched j t1 t2 →
    ∀ Δ : duration, t1 + Δ < t2 → (!completed_by sched j (t1 + Δ)) = true →
      cumulative_interference j t1 (t1 + Δ) ≤
        Δ - SBF.supply_bound_function Δ + cumul_intra_interference sched j t1 (t1 + Δ) := by
  intro hunit arr_seq sched ts tsk hts _ _ hwc SBF hsbf j ha hjt hpos t1 t2 hbip Δ hlt hnc
  rw [← blackout_plus_local_is_interference_cumul arr_seq sched ts tsk hts hwc j ha hjt hpos t1 t2
    hbip Δ hlt hnc]
  have hb := blackout_during_bound_SBF hunit arr_seq sched
    (fun j t1 t2 => job_of_task tsk j = true ∧ busy_interval_prefix sched j t1 t2) hsbf j ha t1 t2
    ⟨hjt, hbip⟩ Δ (Nat.le_of_lt hlt)
  omega'

/-- After the job has reached its run-to-completion threshold, it incurs no
intra-supply interference. -/
theorem no_intra_interference_after_F [TaskCost Task] [TaskRunToCompletionThreshold Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job]
    {PState : ProcessorState Job} :
    fully_consuming_proc_model PState →
    ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState) (ts : List Task) (tsk : Task),
    decide (tsk ∈ ts) = true → valid_preemption_model arr_seq sched →
    valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ [Interference Job] [InterferingWorkload Job],
    work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix sched j t1 t2 →
    ∀ Δ : duration, t1 + Δ < t2 → (!completed_by sched j (t1 + Δ)) = true →
    ∀ F : duration, F ≤ Δ → task_rtct tsk ≤ service sched j (t1 + F) →
      cumul_intra_interference sched j (t1 + F) (t1 + Δ) = 0 := by
  intro hcons arr_seq sched ts tsk _ hvalid hrtc _ _ hwc j ha hjt hpos t1 t2 hbip Δ hlt hnc F _ hsvc
  have hpos' : job_cost j > 0 := of_decide_eq_true hpos
  unfold cumul_intra_interference cumul_cond_interference
  apply Finset.sum_eq_zero
  intro t ht
  rw [Finset.mem_Ico] at ht
  unfold cond_interference
  dsimp only
  cases hs : has_supply sched t
  · rfl
  · have hsched : scheduled_at sched j t = true := by
      apply job_nonpreemptive_after_run_to_completion_threshold arr_seq sched hvalid j ha
        (t1 + F) t ht.1
      · exact Nat.le_trans (hrtc.2 j ha hjt) hsvc
      · have hm := completion_monotonic sched j t (t1 + Δ) (Nat.le_of_lt ht.2)
        cases hc : completed_by sched j t
        · rfl
        · rw [hc] at hm
          rw [hm rfl] at hnc
          exact absurd hnc (by decide)
    have hprog := progress_inside_supplies sched hcons j t hs hsched
    have hr : receives_service_at sched j t = true := decide_eq_true hprog
    have hw := hwc j t1 t2 t ha hpos' hbip ⟨by omega', by omega'⟩
    cases hi : interference j t
    · rfl
    · exact absurd hi (hw.mpr hr)

/-- The preemptive-stage bound `IBF_P A Δ := (Δ - SBF Δ) + intra_IBF A Δ`. -/
theorem IBF_P_bounds_interference [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    unit_supply_proc_model PState →
    ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState) (ts : List Task) (tsk : Task),
    decide (tsk ∈ ts) = true →
    ∀ [Interference Job] [InterferingWorkload Job],
    work_conserving arr_seq sched →
    ∀ SBF : SupplyBoundFunction, valid_busy_sbf arr_seq sched tsk SBF.supply_bound_function →
    ∀ intra_IBF : duration → duration → duration,
      intra_interference_is_bounded_by arr_seq sched tsk intra_IBF →
      job_interference_is_bounded_by arr_seq sched tsk
        (fun A Δ => Δ - SBF.supply_bound_function Δ + intra_IBF A Δ)
        (relative_arrival_time_of_job_is_A sched) := by
  intro hunit arr_seq sched ts tsk hts _ _ hwc SBF hsbf intra hintra
  intro t1 t2 Δ j ha hjt hbi hlt hnc A hA
  have hpos := incomplete_implies_positive_cost sched j (t1 + Δ) hnc
  have h := cumulative_job_interference_bound hunit arr_seq sched ts tsk hts hwc SBF hsbf j ha hjt
    hpos t1 t2 hbi.1 Δ hlt hnc
  have hi : cumul_intra_interference sched j t1 (t1 + Δ) ≤ intra A Δ :=
    hintra t1 t2 Δ j ha hjt hbi hlt hnc A hA
  change cumulative_interference j t1 (t1 + Δ) ≤ _
  omega'

/-- The non-preemptive-stage bound
`IBF_NP F Δ := (F - task_rtct tsk) + (Δ - SBF Δ - (F - SBF F))`. -/
theorem IBF_NP_bounds_interference [TaskCost Task] [TaskRunToCompletionThreshold Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job]
    {PState : ProcessorState Job} :
    unit_supply_proc_model PState → fully_consuming_proc_model PState →
    ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState),
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
      valid_preemption_model arr_seq sched →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ [Interference Job] [InterferingWorkload Job],
    work_conserving arr_seq sched →
    ∀ SBF : SupplyBoundFunction, valid_busy_sbf arr_seq sched tsk SBF.supply_bound_function →
      unit_supply_bound_function SBF.supply_bound_function →
    ∀ intra_IBF : duration → duration → duration,
      intra_interference_is_bounded_by arr_seq sched tsk intra_IBF →
      job_interference_is_bounded_by arr_seq sched tsk
        (fun F Δ => F - task_rtct tsk +
          (Δ - SBF.supply_bound_function Δ - (F - SBF.supply_bound_function F)))
        (relative_time_to_reach_rtct sched tsk
          (fun A Δ => Δ - SBF.supply_bound_function Δ + intra_IBF A Δ)) := by
  intro hunit hcons arr_seq sched harr hcomp ts tsk hts hvalid hrtc _ _ hwc SBF hsbf hunitsbf intra
    hintra
  intro t1 t2 Δ j ha hjt hbi hlt hnc F hrt
  have huser : unit_service_proc_model PState := unit_supply_is_unit_service PState hunit
  have hpos := incomplete_implies_positive_cost sched j (t1 + Δ) hnc
  obtain ⟨hfix, hrtcsvc⟩ := hrt t1 t2 hbi
  have ⟨⟨⟨hle1, hle2⟩, _, _⟩, _⟩ := hbi
  change cumulative_interference j t1 (t1 + Δ) ≤ _
  have hbound : ∀ δ, t1 + δ ≤ t2 →
      service_during sched j t1 (t1 + δ) + cumulative_interference j t1 (t1 + δ) ≤ δ :=
    fun δ hδ => service_and_interference_bounded arr_seq sched tsk hwc j ha hjt hpos t1 t2 hbi.1
      t1 δ (Nat.le_refl _) hδ huser
  rcases Nat.lt_or_ge (t1 + F) t2 with hF | hF
  · rcases Nat.le_total F Δ with hFD | hDF
    · -- the preemptive stage ends inside the interval
      have hsplit := blackout_plus_local_is_interference_cumul arr_seq sched ts tsk hts hwc j ha hjt
        hpos t1 t2 hbi.1 Δ hlt hnc
      have hblk := blackout_during_bound_SBF hunit arr_seq sched
        (fun j t1 t2 => job_of_task tsk j = true ∧ busy_interval_prefix sched j t1 t2) hsbf j ha t1 t2
        ⟨hjt, hbi.1⟩ Δ (Nat.le_of_lt hlt)
      have hcat := cumulative_interference_cat (fun _ t => has_supply sched t) j (t1 + F) t1 (t1 + Δ)
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
      have hzero := no_intra_interference_after_F hcons arr_seq sched ts tsk hts hvalid hrtc hwc j ha
        hjt hpos t1 t2 hbi.1 Δ hlt hnc F hFD hrtcsvc
      have hncF : (!completed_by sched j (t1 + F)) = true := by
        have hm := completion_monotonic sched j (t1 + F) (t1 + Δ) (by omega')
        cases hc : completed_by sched j (t1 + F)
        · rfl
        · rw [hc] at hm
          rw [hm rfl] at hnc
          exact absurd hnc (by decide)
      have hintraF : cumul_intra_interference sched j t1 (t1 + F) ≤ intra (job_arrival j - t1) F := by
        refine hintra t1 t2 F j ha hjt hbi hF hncF (job_arrival j - t1) ?_
        intro t1' t2' hbi'
        obtain ⟨rfl, rfl⟩ := busy_interval_is_unique sched j t1 t2 t1' t2' hbi hbi'
        rfl
      have hmono := complement_SBF_monotone hunitsbf hFD
      unfold cumul_intra_interference at hzero hintraF hsplit
      omega'
    · -- the interval ends inside the preemptive stage
      have hsub := cumulative_interference_sub (fun _ _ => true) j t1 (t1 + Δ) t1 (t1 + F)
        (Nat.le_refl _) (by omega')
      have hb := hbound F (Nat.le_of_lt hF)
      have hns := no_service_before_busy_interval sched harr j hpos t1 t2 hbi (t1 + F)
      unfold cumulative_interference at hb ⊢
      omega'
  · -- the preemptive-stage solution lies beyond the busy interval
    have hcost := service_within_busy_interval_ge_job_cost sched harr j hpos t1 t2 hbi
    have hmost := service_at_most_cost sched hcomp j huser (t1 + F)
    have hsub := cumulative_interference_sub (fun _ _ => true) j t1 (t1 + Δ) t1 t2
      (Nat.le_refl _) (by omega')
    have hb := hbound (t2 - t1) (by omega')
    have ht2 : t1 + (t2 - t1) = t2 := by omega'
    rw [ht2] at hb
    unfold cumulative_interference at hb ⊢
    omega'

/-- The second stage accounts for the first: `F ≤ task_cost + IBF_NP F Δ`. -/
theorem IBF_P_sol_le_IBF_NP [TaskCost Task] [TaskRunToCompletionThreshold Task]
    [JobTask Job Task] [JobCost Job] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true → valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ (SBF : SupplyBoundFunction) (F Δ : duration),
      F ≤ task_cost tsk + (F - task_rtct tsk +
        (Δ - SBF.supply_bound_function Δ - (F - SBF.supply_bound_function F))) := by
  intro _ hrtc SBF F Δ
  have hle : task_rtct tsk ≤ task_cost tsk := of_decide_eq_true hrtc.1
  omega'

/-- The restricted-supply recurrence implies the abstract-RTA recurrence. -/
theorem max_in_rs_hypothesis_impl_max_in_arta_hypothesis [TaskCost Task]
    [TaskRunToCompletionThreshold Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    [JobPreemptable Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true → valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ [Interference Job] [InterferingWorkload Job] (L : duration) (SBF : SupplyBoundFunction),
      valid_busy_sbf arr_seq sched tsk SBF.supply_bound_function →
      unit_supply_bound_function SBF.supply_bound_function →
    ∀ (intra_IBF : duration → duration → duration) (R : duration),
      (∀ A : duration,
        is_in_search_space L (fun A0 Δ => Δ - SBF.supply_bound_function Δ + intra_IBF A0 Δ) A →
        ∃ F : duration, F ≤ A + R ∧
          task_rtct tsk + intra_IBF A F ≤ SBF.supply_bound_function F ∧
          SBF.supply_bound_function F + (task_cost tsk - task_rtct tsk) ≤
            SBF.supply_bound_function (A + R)) →
    ∀ A : duration,
      is_in_search_space L (fun A0 Δ => Δ - SBF.supply_bound_function Δ + intra_IBF A0 Δ) A →
      ∃ F : duration,
        task_rtct tsk + (F - SBF.supply_bound_function F + intra_IBF A F) ≤ F ∧
        task_cost tsk + (F - task_rtct tsk + (A + R - SBF.supply_bound_function (A + R) -
          (F - SBF.supply_bound_function F))) ≤ A + R := by
  intro _ hrtc _ _ L SBF hsbf hunitsbf intra R hmax A hsp
  obtain ⟨F, h0, h1, h2⟩ := hmax A hsp
  have hle : task_rtct tsk ≤ task_cost tsk := of_decide_eq_true hrtc.1
  have hF := sbf_bounded_by_duration arr_seq sched _ hsbf hunitsbf F
  have hAR := sbf_bounded_by_duration arr_seq sched _ hsbf hunitsbf (A + R)
  have hmono := complement_SBF_monotone hunitsbf h0
  exact ⟨F, by omega', by omega'⟩

/-- `R` bounds the response time of the jobs of `tsk` under restricted supply. -/
theorem uniprocessor_response_time_bound_restricted_supply [TaskCost Task]
    [TaskRunToCompletionThreshold Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    [JobPreemptable Job] {PState : ProcessorState Job} :
    unit_supply_proc_model PState → fully_consuming_proc_model PState →
    ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState),
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
      valid_preemption_model arr_seq sched →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ [Interference Job] [InterferingWorkload Job],
    work_conserving arr_seq sched →
    ∀ L : duration, busy_intervals_are_bounded_by arr_seq sched tsk L →
    ∀ SBF : SupplyBoundFunction, valid_busy_sbf arr_seq sched tsk SBF.supply_bound_function →
      unit_supply_bound_function SBF.supply_bound_function →
    ∀ intra_IBF : duration → duration → duration,
      intra_interference_is_bounded_by arr_seq sched tsk intra_IBF →
    ∀ R : duration,
      (∀ A : duration,
        is_in_search_space L (fun A0 Δ => Δ - SBF.supply_bound_function Δ + intra_IBF A0 Δ) A →
        ∃ F : duration, F ≤ A + R ∧
          task_rtct tsk + intra_IBF A F ≤ SBF.supply_bound_function F ∧
          SBF.supply_bound_function F + (task_cost tsk - task_rtct tsk) ≤
            SBF.supply_bound_function (A + R)) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hunit hcons arr_seq sched harr hcomp hvalid ts tsk hts hpm hrtc _ _ hwc L hL SBF hsbf
    hunitsbf intra hintra R hmax
  exact uniprocessor_response_time_bound arr_seq sched hvalid ts tsk hts hwc L hL
    (fun A Δ => Δ - SBF.supply_bound_function Δ + intra A Δ)
    (IBF_P_bounds_interference hunit arr_seq sched ts tsk hts hwc SBF hsbf intra hintra)
    (fun F Δ => F - task_rtct tsk +
      (Δ - SBF.supply_bound_function Δ - (F - SBF.supply_bound_function F)))
    (IBF_NP_bounds_interference hunit hcons arr_seq sched harr hcomp ts tsk hts hpm hrtc hwc SBF
      hsbf hunitsbf intra hintra)
    (IBF_P_sol_le_IBF_NP arr_seq ts tsk hts hrtc SBF) R
    (max_in_rs_hypothesis_impl_max_in_arta_hypothesis arr_seq sched ts tsk hts hrtc L SBF hsbf
      hunitsbf intra R hmax)

end AbstractRTARestrictedSupply

end Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta
