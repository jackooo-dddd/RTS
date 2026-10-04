-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/busy_interval/carry_in.v

import Prosa.Analysis.Facts.Model.Workload
import Prosa.Analysis.Facts.Model.Ideal.ServiceOfJobs
import Prosa.Analysis.Facts.BusyInterval.QuietTime
import Prosa.Analysis.Facts.BusyInterval.Existence
import Prosa.Analysis.Definitions.WorkBearingReadiness
import Prosa.Model.Schedule.WorkConserving
import Prosa.Util.Tactics
import Prosa.Analysis.Facts.Behavior.Supply

namespace Prosa.Analysis.Facts.BusyInterval.CarryIn

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Processor.Supply
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Schedule.WorkConserving
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Model.Aggregate.Workload
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.CarryIn
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Model.Ideal.ServiceOfJobs
open Prosa.Analysis.Facts.BusyInterval.QuietTime
open Prosa.Analysis.Facts.BusyInterval.Existence
open Prosa.Util.Sum
open scoped BigOperators

/-! Busy intervals from a bound on the total workload: a bounded total
workload forces an instant without carry-in within every window of length
`Δ`, and hence a bounded busy interval.
Binders follow the elaborated source types: every lemma takes only the section
inputs and hypotheses it uses, in their elaborated order; instance inputs
quantified after a hypothesis are `∀ [..]` binders at that position.
Representation: a Boolean in `Prop` position is `= true`; `~ P` is `¬ P`;
`a <= b < c` is a Boolean conjunction of decides; `t.+1` is `t + 1`;
`predT` is `fun _ => true`. -/

section CarryIn

variable {Job : JobType} [DecidableEq Job]

/-- Trivially, there is no carry-in at time `0`. -/
theorem no_carry_in_at_zero [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job)
    {PState : ProcessorState Job} (sched : schedule PState) : no_carry_in arr_seq sched 0 := by
  intro j _ hbef
  simp [arrived_before] at hbef

/-- A pending job prevents idleness under work conservation. -/
theorem pending_job_not_idle [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
    ∀ (JLFP : JLFP_policy Job) [JobReady Job PState], work_bearing_readiness arr_seq sched →
      work_conserving arr_seq sched →
    ∀ (j : Job) (t : instant), arrives_in arr_seq j → pending sched j t = true →
      ¬ is_idle arr_seq sched t = true := by
  intro hva PState sched hfrom hmust JLFP _ hwb hwc j t ha hpend hidle
  obtain ⟨jhp, hahp, hrhp, _⟩ := hwb j t ha hpend
  have hns := not_scheduled_when_idle arr_seq hva sched hfrom hmust jhp t hidle
  have hback : backlogged sched jhp t = true := by
    unfold backlogged
    rw [hrhp]
    simpa using hns
  obtain ⟨jo, hjo⟩ := hwc jhp t hahp hback
  have hno := not_scheduled_when_idle arr_seq hva sched hfrom hmust jo t hidle
  rw [hjo] at hno
  exact absurd hno (by decide)

/-- An idle instant has no carry-in. -/
theorem idle_instant_no_carry_in [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
    ∀ (JLFP : JLFP_policy Job) [JobReady Job PState], work_bearing_readiness arr_seq sched →
      work_conserving arr_seq sched →
    ∀ t : instant, is_idle arr_seq sched t = true → no_carry_in arr_seq sched t := by
  intro hva PState sched hfrom hmust JLFP _ hwb hwc t hidle j ha hbef
  by_contra hnc
  apply pending_job_not_idle arr_seq hva sched hfrom hmust JLFP hwb hwc j t ha _ hidle
  simp only [arrived_before, decide_eq_true_eq] at hbef
  unfold pending has_arrived
  have hf : completed_by sched j t = false := by simpa using hnc
  rw [hf]
  simp only [Bool.not_false, Bool.and_true, decide_eq_true_eq]
  exact Nat.le_of_lt hbef

/-- An idle instant is followed by an instant without carry-in. -/
theorem idle_instant_next_no_carry_in [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
    ∀ (JLFP : JLFP_policy Job) [JobReady Job PState], work_bearing_readiness arr_seq sched →
      work_conserving arr_seq sched →
    ∀ t : instant, is_idle arr_seq sched t = true → no_carry_in arr_seq sched (t + 1) := by
  intro hva PState sched hfrom hmust JLFP _ hwb hwc t hidle j ha hbef
  by_contra hnc
  apply pending_job_not_idle arr_seq hva sched hfrom hmust JLFP hwb hwc j t ha _ hidle
  simp only [arrived_before, decide_eq_true_eq] at hbef
  unfold pending has_arrived
  have hf : completed_by sched j t = false := by
    cases h : completed_by sched j t
    · rfl
    · exact absurd (completion_monotonic sched j t (t + 1) (Nat.le_succ t) h) hnc
  rw [hf]
  simp only [Bool.not_false, Bool.and_true, decide_eq_true_eq]
  omega'

/-- The blackout plus the total service in any window of length `Δ` is at
most `Δ`. -/
theorem total_service_is_bounded_by_Δ [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (Δ : duration), unit_service_proc_model PState →
    ∀ t : duration,
      blackout_during sched t (t + Δ) +
          service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 (t + Δ)) t (t + Δ) ≤ Δ := by
  intro hva PState huni sched Δ hunit t
  have hnd := arrivals_uniq arr_seq hva.1 hva.2 0 (t + Δ)
  rw [service_of_jobs_sum_over_time_interval]
  unfold blackout_during
  rw [← Finset.sum_add_distrib]
  conv_rhs => rw [← sum_of_ones t Δ]
  apply Finset.sum_le_sum
  intro x _
  rcases Prosa.Analysis.Facts.Behavior.Supply.blackout_or_supply sched x with hb | hs
  · have hz : service_of_jobs_at sched (fun _ => true) (arrivals_between arr_seq 0 (t + Δ)) x = 0 := by
      have h0 : ∀ y, service_at sched y x = 0 := fun y => no_service_during_blackout sched y x hb
      simp [service_of_jobs_at, sumFiltered, h0]
    rw [hz, hb]
    rfl
  · have hnb : is_blackout sched x = false := by
      unfold is_blackout
      rw [hs]
      rfl
    rw [hnb]
    simpa using service_of_jobs_le_1 hunit huni sched (fun _ => true) _ hnd x

/-- If blackout plus total service in `[t, t + Δ)` falls short of `Δ`, some
instant of `(t, t + Δ]` has no carry-in. -/
theorem low_total_service_implies_existence_of_time_with_no_carry_in [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState → fully_consuming_proc_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
    ∀ (JLFP : JLFP_policy Job) [JobReady Job PState], work_bearing_readiness arr_seq sched →
      work_conserving arr_seq sched →
    ∀ Δ : duration, 0 < Δ →
    ∀ t : duration,
      blackout_during sched t (t + Δ) +
          service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 (t + Δ)) t (t + Δ) < Δ →
      ∃ δ : Nat, δ < Δ ∧ no_carry_in arr_seq sched (t + 1 + δ) := by
  intro hva PState huni hfc sched hfrom hmust JLFP _ hwb hwc Δ _ t hlt
  obtain ⟨ti, hin, hidle⟩ := low_service_implies_existence_of_idle_time_rs Job PState huni hfc arr_seq hva
    sched hfrom hmust t (t + Δ) (by omega')
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
  rcases Nat.lt_or_ge t ti with hlt' | hge
  · refine ⟨ti - t - 1, by omega', ?_⟩
    have heq : t + 1 + (ti - t - 1) = ti := by omega'
    rw [heq]
    exact idle_instant_no_carry_in arr_seq hva sched hfrom hmust JLFP hwb hwc ti hidle
  · have heq : ti = t := Nat.le_antisymm hge hin.1
    subst heq
    refine ⟨0, by omega', ?_⟩
    exact idle_instant_next_no_carry_in arr_seq hva sched hfrom hmust JLFP hwb hwc ti hidle

/-- If blackout plus total service in `[t, t + Δ)` equals `Δ`, then under the
workload bound all jobs are complete at `t + Δ`. -/
theorem completion_of_all_jobs_implies_no_carry_in [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState),
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ Δ : duration,
      (∀ t : instant, no_carry_in arr_seq sched t →
        blackout_during sched t (t + Δ) + total_workload_between arr_seq t (t + Δ) ≤ Δ) →
      unit_service_proc_model PState →
    ∀ t : duration, no_carry_in arr_seq sched t →
      blackout_during sched t (t + Δ) +
          service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 (t + Δ)) t (t + Δ) = Δ →
      no_carry_in arr_seq sched (t + Δ) := by
  intro hva PState sched hmust hcomp Δ hwork hunit t hnci heqs s ha hbef
  have hcons := hva.1
  have hW := hwork t hnci
  unfold total_workload_between total_workload at hW
  have hcompl := all_jobs_have_completed_impl_workload_eq_service hunit arr_seq hcons sched hmust hcomp
    (fun _ => true) 0 t t (by
      intro x hx _
      exact hnci x (in_arrivals_implies_arrived arr_seq x 0 t hx) (by
        have hb := in_arrivals_implies_arrived_between arr_seq hcons x 0 t hx
        simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at hb
        simp only [arrived_before, decide_eq_true_eq]
        exact hb.2))
  have hcatw := workload_of_jobs_cat arr_seq t 0 (t + Δ) (fun _ => true)
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
  have hcats := service_of_jobs_cat_scheduling_interval arr_seq hcons sched hmust (fun _ => true) 0
    (t + Δ) t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
  have hcata := service_of_jobs_cat_arrival_interval arr_seq sched (fun _ => true) 0 (t + Δ) t
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
  have hle := service_of_jobs_le_workload hunit sched hcomp (fun _ => true)
    (arrivals_between arr_seq 0 (t + Δ)) 0 (t + Δ)
  have hEQ : workload_of_jobs (fun _ => true) (arrivals_between arr_seq 0 (t + Δ)) =
      service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 (t + Δ)) 0 (t + Δ) := by
    omega'
  have hin : decide (s ∈ arrivals_between arr_seq 0 (t + Δ)) = true :=
    arrived_between_implies_in_arrivals arr_seq hcons s 0 (t + Δ) ha (by
      simp only [arrived_before, decide_eq_true_eq] at hbef
      simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]
      omega')
  exact workload_eq_service_impl_all_jobs_have_completed hunit arr_seq hcons sched hmust hcomp
    (fun _ => true) 0 (t + Δ) (t + Δ) hEQ s hin rfl

/-- Every window of length `Δ` contains an instant without carry-in. -/
theorem processor_is_not_too_busy [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState → fully_consuming_proc_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched →
    ∀ (JLFP : JLFP_policy Job) [JobReady Job PState], work_bearing_readiness arr_seq sched →
      work_conserving arr_seq sched →
    ∀ Δ : duration, 0 < Δ →
      (∀ t : instant, no_carry_in arr_seq sched t →
        blackout_during sched t (t + Δ) + total_workload_between arr_seq t (t + Δ) ≤ Δ) →
      unit_service_proc_model PState →
    ∀ t : Nat, ∃ δ : Nat, δ < Δ ∧ no_carry_in arr_seq sched (t + δ) := by
  intro hva PState huni hfc sched hfrom hmust hcomp JLFP _ hwb hwc Δ hpos hwork hunit t
  induction t with
  | zero => exact ⟨0, hpos, by simpa using no_carry_in_at_zero arr_seq sched⟩
  | succ t ih =>
    obtain ⟨δ, hlt, hnci⟩ := ih
    rcases Nat.eq_zero_or_pos δ with h0 | hposδ
    · subst h0
      have hnci0 : no_carry_in arr_seq sched t := by simpa using hnci
      have hb := total_service_is_bounded_by_Δ arr_seq hva huni sched Δ hunit t
      rcases Nat.lt_or_ge
          (blackout_during sched t (t + Δ) +
            service_of_jobs sched (fun _ => true) (arrivals_between arr_seq 0 (t + Δ)) t (t + Δ)) Δ
        with hl | hg
      · exact low_total_service_implies_existence_of_time_with_no_carry_in arr_seq hva huni hfc sched hfrom
          hmust JLFP hwb hwc Δ hpos t hl
      · refine ⟨Δ - 1, by omega', ?_⟩
        have heq : t + 1 + (Δ - 1) = t + Δ := by omega'
        rw [heq]
        exact completion_of_all_jobs_implies_no_carry_in arr_seq hva sched hmust hcomp Δ hwork hunit t
          hnci0 (Nat.le_antisymm hb hg)
    · refine ⟨δ - 1, by omega', ?_⟩
      have heq : t + 1 + (δ - 1) = t + δ := by omega'
      rw [heq]
      exact hnci

/-- A bound on the total workload yields a bounded busy interval containing
the arrival of any job with positive cost. -/
theorem busy_interval_from_total_workload_bound [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState → fully_consuming_proc_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched →
    ∀ JLFP : JLFP_policy Job, reflexive_job_priorities JLFP →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched → work_conserving arr_seq sched →
    ∀ Δ : duration, 0 < Δ →
      (∀ t : instant, no_carry_in arr_seq sched t →
        blackout_during sched t (t + Δ) + total_workload_between arr_seq t (t + Δ) ≤ Δ) →
      unit_service_proc_model PState →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
      ∃ t1 t2 : Nat, (decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2)) = true ∧
        t2 ≤ t1 + Δ ∧ busy_interval arr_seq sched j t1 t2 := by
  intro hva PState huni hfc sched hfrom hmust hcomp JLFP hrefl _ hwb hwc Δ hpos hwork hunit j ha hjcp
  classical
  have hpend := job_pending_at_arrival sched j (of_decide_eq_true hjcp) hmust
  obtain ⟨t1, hbip, hge⟩ := exists_busy_interval_prefix arr_seq hva sched JLFP j ha hrefl
    (job_arrival j) hpend
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hge
  obtain ⟨δ, hδ, hnci⟩ := processor_is_not_too_busy arr_seq hva huni hfc sched hfrom hmust hcomp JLFP hwb
    hwc Δ hpos hwork hunit (t1 + 1)
  have hq := no_carry_in_implies_quiet_time sched arr_seq j (t1 + 1 + δ) hnci
  have hex : ∃ t2, t1 < t2 ∧ t2 ≤ t1 + 1 + δ ∧ quiet_time arr_seq sched j t2 :=
    ⟨t1 + 1 + δ, by omega', le_rfl, hq⟩
  have hspec := Nat.find_spec hex
  have hmin : ∀ t, t < Nat.find hex → ¬ (t1 < t ∧ t ≤ t1 + 1 + δ ∧ quiet_time arr_seq sched j t) :=
    fun t ht => Nat.find_min hex ht
  have ⟨_, hq1, hnq, _⟩ := hbip
  have harr : job_arrival j < Nat.find hex := by
    by_contra hle
    exact hnq (Nat.find hex) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hspec.2.2
  refine ⟨t1, Nat.find hex, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega', by omega', ?_⟩
  refine ⟨⟨hspec.1, hq1, ?_, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'⟩, hspec.2.2⟩
  intro t ht hqt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  exact hmin t ht.2 ⟨ht.1, by omega', hqt⟩

end CarryIn

end Prosa.Analysis.Facts.BusyInterval.CarryIn
