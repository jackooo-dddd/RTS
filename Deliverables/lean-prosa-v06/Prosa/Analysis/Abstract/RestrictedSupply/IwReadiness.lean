-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/iw_readiness.v

import Prosa.Analysis.Abstract.AbstractRta
import Prosa.Analysis.Abstract.IBF.SupplyTask
import Prosa.Analysis.Facts.Interference
import Prosa.Analysis.Facts.BusyInterval.ServiceInversion
import Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware
import Prosa.Analysis.Facts.ReadinessInterference
import Prosa.Analysis.Facts.Model.Uniprocessor
import Prosa.Model.Schedule.WorkConserving

namespace Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Definitions.Service
open Prosa.Analysis.Definitions.ReadinessInterference
open Prosa.Analysis.Definitions.ServiceInversion
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.IBF.Task
open Prosa.Analysis.Abstract.IBF.SupplyTask
open Prosa.Analysis.Definitions.BusyInterval
open Prosa.Analysis.Definitions.TaskSchedule
open Prosa.Model.Task.Sequentiality
open Prosa.Analysis.Facts.Interference
open Prosa.Analysis.Facts.ReadinessInterference
open Prosa.Analysis.Facts.Model.TaskSchedule
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Model.Workload
open Prosa.Analysis.Facts.Model.Uniprocessor
open Prosa.Analysis.Facts.BusyInterval.HepAtPt
open Prosa.Analysis.Facts.BusyInterval.Existence
open Prosa.Analysis.Facts.BusyInterval.ServiceInversion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Supply
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Util.Sum
open Prosa.Util.Notation
open scoped BigOperators

/-! Readiness-aware JLFP instantiation of interference and interfering workload for restricted-supply
uniprocessors, and their equivalence with the classical notions.

Binders follow the elaborated source types: every declaration takes only the section inputs and hypotheses it
uses, in their elaborated order; instance inputs quantified after a hypothesis are `∀ [..]` binders at that
position. The source's section-local instances `rs_readiness_jlfp_interference` and
`rs_readiness_jlfp_interfering_workload` are the definitions of the same names below (the source `Instance`
fields; Booleans added to naturals are counted by `Bool.toNat`, the source's `nat_of_bool` coercion), passed
explicitly wherever the elaborated statements use them implicitly. The readiness-aware service inversion is the
accepted `ReadinessAware.service_inversion`; the section-local `readiness_interference_during` is unfolded as the
`Finset.Ico` sum of the counted predicate. The classical and abstract busy-interval notions are distinguished by
namespace. Representation: a Boolean in `Prop` position is `= true`; `~~ b` is `!b`; `a <= b < c` is a Boolean
conjunction of decides; the interval sum `\sum_(t1 <= t < t2) F t` is the `Finset.Ico` sum over `Nat`; the
source's `fun=> [eta has_supply sched]` is `fun _ t => has_supply sched t`. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

/-- LEAN_HELPER: a half-open `sumSeq` over `List.range'` is the corresponding `Finset.Ico` sum. -/
private theorem sumSeq_range'_eq (a b : Nat) (f : Nat → Nat) :
    sumSeq (List.range' a (b - a)) f = ∑ t ∈ (Finset.Ico a b : Finset Nat), f t := by
  unfold sumSeq
  rw [Finset.sum_Ico_eq_sum_range]
  have : ∀ n a, ((List.range' a n).map f).sum = ∑ k ∈ Finset.range n, f (a + k) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [List.range'_succ, List.map_cons, List.sum_cons, ih (a + 1), Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [Nat.add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.add_assoc, Nat.add_comm 1 k]
  exact this (b - a) a

private theorem sumFiltered_append' {I : Type _} (l1 l2 : List I) (P : I → Bool) (F : I → Nat) :
    sumFiltered (l1 ++ l2) P F = sumFiltered l1 P F + sumFiltered l2 P F := by
  unfold sumFiltered
  rw [List.filter_append, List.map_append, List.sum_append]

section IWInstantiation

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- A job incurs interference if there is no supply, another higher-or-equal-priority job is served, it incurs
a (readiness-aware) service inversion, or there is supply but no higher-or-equal-priority job is ready. -/
@[reducible] noncomputable def rs_readiness_jlfp_interference [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} [JobReady Job PState] (arr_seq : arrival_sequence Job)
    (sched : schedule PState) [JLFP_policy Job] : Interference Job where
  interference j t :=
    is_blackout sched t || another_hep_job_interference arr_seq sched j t ||
      ReadinessAware.service_inversion arr_seq sched j t ||
      (has_supply sched t && !some_hep_job_ready arr_seq sched j t)

/-- The interfering workload counts the indicator values of the predicates of the interference, with the
workload of the other higher-or-equal-priority jobs released at `t` in place of their service. -/
@[reducible] noncomputable def rs_readiness_jlfp_interfering_workload [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} [JobReady Job PState] (arr_seq : arrival_sequence Job)
    (sched : schedule PState) [JLFP_policy Job] : InterferingWorkload Job where
  interfering_workload j t :=
    (is_blackout sched t).toNat + other_hep_jobs_interfering_workload arr_seq j t +
      (ReadinessAware.service_inversion arr_seq sched j t).toNat +
      (has_supply sched t && !some_hep_job_ready arr_seq sched j t).toNat

/-- LEAN_HELPER: under supply with some ready higher-or-equal-priority job, another higher-or-equal-priority job
being served excludes a readiness-aware service inversion (a uniprocessor serves at most one job). -/
private theorem ahep_excludes_service_inversion [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    (huni : uniprocessor_model PState) [JobReady Job PState] (arr_seq : arrival_sequence Job)
    (sched : schedule PState) [JLFP_policy Job] (j : Job) (t : instant)
    (hahep : another_hep_job_interference arr_seq sched j t = true) :
    ReadinessAware.service_inversion arr_seq sched j t = false := by
  unfold ReadinessAware.service_inversion Pred.service_inversion
  cases hsi : (served_jobs_at arr_seq sched t).any (fun jlp => !hep_job_at t jlp j) with
  | false => simp
  | true =>
    exfalso
    obtain ⟨x, hx, hxhep⟩ := List.any_eq_true.mp hahep
    obtain ⟨y, hy, hylp⟩ := List.any_eq_true.mp hsi
    have hsx : scheduled_at sched x t = true := by
      have := (List.mem_filter.mp hx).2
      unfold receives_service_at at this
      exact service_at_implies_scheduled_at sched x t (of_decide_eq_true this)
    have hsy : scheduled_at sched y t = true := by
      have := (List.mem_filter.mp hy).2
      unfold receives_service_at at this
      exact service_at_implies_scheduled_at sched y t (of_decide_eq_true this)
    have hxy := huni x y sched t hsx hsy
    subst hxy
    unfold another_hep_job at hxhep
    rw [hep_job_at_jlfp] at hylp
    simp only [Bool.and_eq_true] at hxhep
    rw [hxhep.1] at hylp
    exact absurd hylp (by decide)

theorem cumulative_interference_split [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job) (sched : schedule PState),
      valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job] (j : Job) (t1 t2 : Nat),
      @cumulative_interference Job _ (rs_readiness_jlfp_interference arr_seq sched) j t1 t2 =
        blackout_during sched t1 t2 + cumulative_another_hep_job_interference arr_seq sched j t1 t2 +
          ReadinessAware.cumulative_service_inversion arr_seq sched j t1 t2 +
          ∑ t ∈ Finset.Ico (α := Nat) t1 t2, (has_supply sched t && !some_hep_job_ready arr_seq sched j t).toNat := by
  intro huni JobReady0 arr_seq sched hvs JLFP j t1 t2
  unfold cumulative_interference cumul_cond_interference blackout_during cumulative_another_hep_job_interference
    ReadinessAware.cumulative_service_inversion
  simp only [sumSeq_range'_eq]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  show (true && (is_blackout sched t || another_hep_job_interference arr_seq sched j t ||
      ReadinessAware.service_inversion arr_seq sched j t ||
      (has_supply sched t && !some_hep_job_ready arr_seq sched j t))).toNat =
    (is_blackout sched t).toNat + (another_hep_job_interference arr_seq sched j t).toNat +
      (ReadinessAware.service_inversion arr_seq sched j t).toNat +
      (has_supply sched t && !some_hep_job_ready arr_seq sched j t).toNat
  cases hsup : has_supply sched t
  · have hbl : is_blackout sched t = true := by unfold is_blackout; rw [hsup]; rfl
    have e2 : another_hep_job_interference arr_seq sched j t = false := by
      simpa using no_hep_job_interference_without_supply arr_seq sched JLFP t hbl j
    have e1 : ReadinessAware.service_inversion arr_seq sched j t = false := by
      have := blackout_implies_no_service_inversion arr_seq sched (JLFP_to_JLDP) j t hbl
      unfold ReadinessAware.service_inversion
      simp only [Bool.not_eq_true'] at this
      rw [this]; simp
    rw [hbl, e1, e2]; rfl
  · have hbl : is_blackout sched t = false := by unfold is_blackout; rw [hsup]; rfl
    rw [hbl]
    cases hready : some_hep_job_ready arr_seq sched j t
    · have e2 : another_hep_job_interference arr_seq sched j t = false := by
        simpa using no_hep_ready_implies_no_another_hep_interference arr_seq sched hvs j t (by rw [hready]; rfl)
      have e1 : ReadinessAware.service_inversion arr_seq sched j t = false := by
        simpa using no_hep_ready_implies_no_service_inversion arr_seq sched j t (by rw [hready]; rfl)
      rw [e1, e2]; rfl
    · cases hahep : another_hep_job_interference arr_seq sched j t
      · cases ReadinessAware.service_inversion arr_seq sched j t <;> rfl
      · rw [ahep_excludes_service_inversion huni arr_seq sched j t hahep]; rfl

theorem cumulative_interfering_workload_split [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    [JobReady Job PState] (arr_seq : arrival_sequence Job) (sched : schedule PState)
    [JLFP_policy Job] (j : Job) (t1 t2 : Nat) :
    @cumulative_interfering_workload Job _ (rs_readiness_jlfp_interfering_workload arr_seq sched) j t1 t2 =
      blackout_during sched t1 t2 + cumulative_other_hep_jobs_interfering_workload arr_seq j t1 t2 +
        ReadinessAware.cumulative_service_inversion arr_seq sched j t1 t2 +
        ∑ t ∈ Finset.Ico (α := Nat) t1 t2, (has_supply sched t && !some_hep_job_ready arr_seq sched j t).toNat := by
  unfold cumulative_interfering_workload blackout_during cumulative_other_hep_jobs_interfering_workload
    ReadinessAware.cumulative_service_inversion
  simp only [sumSeq_range'_eq]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rfl

theorem cumulative_task_interference_split [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → fully_consuming_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job] (tsk : Task) (j : Job) (t1 : Nat) (t2 : instant), arrives_in arr_seq j →
      job_of_task tsk j = true → (!completed_by sched j t2) = true →
      @cumul_cond_interference Job _ (rs_readiness_jlfp_interference arr_seq sched)
          (nonself_intra (Task := Task) arr_seq sched) j t1 t2 ≤
        cumulative_another_task_hep_job_interference (Task := Task) arr_seq sched j t1 t2 +
          ReadinessAware.cumulative_service_inversion arr_seq sched j t1 t2 +
          ∑ t ∈ Finset.Ico (α := Nat) t1 t2, (has_supply sched t && !some_hep_job_ready arr_seq sched j t).toNat := by
  intro huni hcons JobReady0 arr_seq hva sched hvs JLFP tsk j t1 t2 _ _ _
  have hfrom := hvs.1
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  unfold cumul_cond_interference cumulative_another_task_hep_job_interference
    ReadinessAware.cumulative_service_inversion
  simp only [sumSeq_range'_eq]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  unfold cond_interference nonself_intra nonself
  show ((!task_served_at arr_seq sched (job_task (Task := Task) j) t) && has_supply sched t &&
      (is_blackout sched t || another_hep_job_interference arr_seq sched j t ||
        ReadinessAware.service_inversion arr_seq sched j t ||
        (has_supply sched t && !some_hep_job_ready arr_seq sched j t))).toNat ≤
    (another_task_hep_job_interference (Task := Task) arr_seq sched j t).toNat +
      (ReadinessAware.service_inversion arr_seq sched j t).toNat +
      (has_supply sched t && !some_hep_job_ready arr_seq sched j t).toNat
  cases hsup : has_supply sched t
  · simp
  · have hbl : is_blackout sched t = false := by unfold is_blackout; rw [hsup]; rfl
    rw [hbl]
    cases hready : some_hep_job_ready arr_seq sched j t
    · have := Bool.toNat_le ((!task_served_at arr_seq sched (job_task (Task := Task) j) t) && true &&
        (false || another_hep_job_interference arr_seq sched j t ||
          ReadinessAware.service_inversion arr_seq sched j t || (true && !false)))
      simp only [Bool.not_false, Bool.and_true, Bool.toNat_true] at this ⊢
      omega
    · simp only [Bool.not_true, Bool.and_false, Bool.or_false, Bool.false_or, Bool.toNat_false, Nat.add_zero]
      rcases scheduled_at_cases arr_seq hva sched hfrom hmust t with hidle | ⟨s, hs⟩
      · have e1 : Pred.service_inversion arr_seq sched j t = false := by
          simpa using idle_implies_no_service_inversion arr_seq hva sched hfrom hmust (JLFP_to_JLDP) j t hidle
        have e2 : another_hep_job_interference arr_seq sched j t = false := by
          simpa using no_hep_job_interference_when_idle arr_seq hva sched hfrom hmust JLFP t hidle j
        unfold ReadinessAware.service_inversion
        rw [e1, e2]; simp
      · cases hsi : ReadinessAware.service_inversion arr_seq sched j t
        · have hts := task_served_at_eq_job_of_task arr_seq hva PState huni sched hfrom hmust
            (job_task (Task := Task) j) hcons t hsup s hs
          have hahep := interference_ahep_def huni hcons arr_seq hva sched hfrom hmust JLFP j t hsup s hs
          have hathep := interference_athep_def (Task := Task) huni hcons arr_seq hva sched hfrom hmust JLFP j t
            hsup s hs
          rw [hts, hahep, hathep]
          unfold job_of_task another_hep_job another_task_hep_job
          by_cases hst : job_task (Task := Task) s = job_task (Task := Task) j
          · simp [hst]
          · have hsj : s ≠ j := fun h => hst (h ▸ rfl)
            cases hep_job s j <;> simp [hst, hsj]
        · have := Bool.toNat_le ((!task_served_at arr_seq sched (job_task (Task := Task) j) t) && true &&
            (another_hep_job_interference arr_seq sched j t || true))
          simp only [Bool.toNat_true] at this ⊢
          omega

theorem cumulative_intra_interference_split [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    [JobReady Job PState] (arr_seq : arrival_sequence Job) (sched : schedule PState) [JLFP_policy Job]
    (j : Job) (t1 t2 : Nat) :
    @cumul_cond_interference Job _ (rs_readiness_jlfp_interference arr_seq sched) (fun _ t => has_supply sched t)
        j t1 t2 ≤
      cumulative_another_hep_job_interference arr_seq sched j t1 t2 +
        ReadinessAware.cumulative_service_inversion arr_seq sched j t1 t2 +
        ∑ t ∈ Finset.Ico (α := Nat) t1 t2, (has_supply sched t && !some_hep_job_ready arr_seq sched j t).toNat := by
  unfold cumul_cond_interference cumulative_another_hep_job_interference ReadinessAware.cumulative_service_inversion
  simp only [sumSeq_range'_eq]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  unfold cond_interference
  show (has_supply sched t && (is_blackout sched t || another_hep_job_interference arr_seq sched j t ||
      ReadinessAware.service_inversion arr_seq sched j t ||
      (has_supply sched t && !some_hep_job_ready arr_seq sched j t))).toNat ≤
    (another_hep_job_interference arr_seq sched j t).toNat +
      (ReadinessAware.service_inversion arr_seq sched j t).toNat +
      (has_supply sched t && !some_hep_job_ready arr_seq sched j t).toNat
  unfold is_blackout
  cases has_supply sched t <;> cases another_hep_job_interference arr_seq sched j t <;>
    cases ReadinessAware.service_inversion arr_seq sched j t <;>
    cases some_hep_job_ready arr_seq sched j t <;> decide

theorem cumulative_iw_hep_eq_workload_of_ohep [JobCost Job] (arr_seq : arrival_sequence Job) [JLFP_policy Job]
    (t1 t2 : instant) (j : Job) :
    cumulative_other_hep_jobs_interfering_workload arr_seq j t1 t2 = workload_of_other_hep_jobs arr_seq j t1 t2 := by
  unfold cumulative_other_hep_jobs_interfering_workload workload_of_other_hep_jobs workload_of_jobs
  rcases Nat.lt_or_ge t1 t2 with hlt | hge
  · obtain ⟨k, rfl⟩ : ∃ k, t2 = t1 + k := ⟨t2 - t1, by omega'⟩
    rw [Nat.add_sub_cancel_left]
    clear hlt
    induction k with
    | zero =>
      rw [arrivals_between_geq arr_seq t1 (t1 + 0) (by omega')]
      rfl
    | succ k ih =>
      rw [List.range'_concat, sumSeq, List.map_append, List.sum_append, ← sumSeq, ih,
        arrivals_between_cat arr_seq t1 (t1 + k) (t1 + (k + 1)) (by omega') (by omega'), sumFiltered_append']
      congr 1
      have : arrivals_between arr_seq (t1 + k) (t1 + (k + 1)) = arrivals_at arr_seq (t1 + k) := by
        unfold arrivals_between bigCat
        rw [show t1 + (k + 1) - (t1 + k) = 1 by omega']
        simp
      rw [this]
      simp [other_hep_jobs_interfering_workload]
  · rw [show t2 - t1 = 0 by omega', arrivals_between_geq arr_seq t1 t2 hge]
    rfl

private theorem classical_quiet_time_zero [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) [JLFP_policy Job] (j : Job) :
    Classical.quiet_time arr_seq sched j 0 := by
  intro jhp _ _ hab
  unfold arrived_before at hab
  simp at hab

private theorem ohep_equation [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    (huni : uniprocessor_model PState) (hsup : unit_supply_proc_model PState) [JobReady Job PState]
    (arr_seq : arrival_sequence Job) (hva : valid_arrival_sequence arr_seq) (sched : schedule PState)
    (hvs : valid_schedule sched arr_seq) [JLFP : JLFP_policy Job] (j : Job) (t : instant) :
    (@cumulative_interference Job _ (rs_readiness_jlfp_interference arr_seq sched) j 0 t =
        @cumulative_interfering_workload Job _ (rs_readiness_jlfp_interfering_workload arr_seq sched) j 0 t) ↔
      service_of_other_hep_jobs arr_seq sched j 0 t = workload_of_other_hep_jobs arr_seq j 0 t := by
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  rw [cumulative_interference_split huni arr_seq sched hvs j 0 t,
    cumulative_interfering_workload_split arr_seq sched j 0 t,
    cumulative_i_ohep_eq_service_of_ohep huni arr_seq hva sched hmust hcde
      JLFP (unit_supply_is_unit_service PState hsup) j 0 t (classical_quiet_time_zero arr_seq sched j),
    cumulative_iw_hep_eq_workload_of_ohep]
  omega'

theorem quiet_time_cl_implies_quiet_time_ab [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j →
    ∀ t : instant, Classical.quiet_time arr_seq sched j t →
      @Prosa.Analysis.Abstract.Definitions.quiet_time Job _ (rs_readiness_jlfp_interference arr_seq sched)
        (rs_readiness_jlfp_interfering_workload arr_seq sched) _ _ _ sched j t = true := by
  intro huni hsup JobReady0 arr_seq hva sched hvs JLFP hrefl j _ t hqt
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  unfold Prosa.Analysis.Abstract.Definitions.quiet_time
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rw [ohep_equation huni hsup arr_seq hva sched hvs j t]
    unfold service_of_other_hep_jobs workload_of_other_hep_jobs
    symm
    apply (all_jobs_have_completed_equiv_workload_eq_service (unit_supply_is_unit_service PState hsup) arr_seq
      hva.1 sched hmust hcde _ 0 t t).mp
    intro j0 hin hP
    have hbt := in_arrivals_implies_arrived_between arr_seq hva.1 j0 0 t hin
    unfold another_hep_job at hP
    simp only [Bool.and_eq_true] at hP
    apply hqt j0 (in_arrivals_implies_arrived arr_seq j0 0 t hin) hP.1
    unfold arrived_between at hbt; unfold arrived_before
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbt
    exact decide_eq_true hbt.2
  · unfold pending_earlier_and_at
    cases hab : arrived_before j t
    · rfl
    · have := hqt j (by assumption) (hrefl j) hab
      simp [this]

theorem quiet_time_ab_implies_quiet_time_cl [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j →
    ∀ t : instant, @Prosa.Analysis.Abstract.Definitions.quiet_time Job _
        (rs_readiness_jlfp_interference arr_seq sched) (rs_readiness_jlfp_interfering_workload arr_seq sched)
        _ _ _ sched j t = true → Classical.quiet_time arr_seq sched j t := by
  intro huni hsup JobReady0 arr_seq hva sched hvs JLFP _ j _ t hqa
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  unfold Prosa.Analysis.Abstract.Definitions.quiet_time at hqa
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hqa
  obtain ⟨h0, h1⟩ := hqa
  rw [ohep_equation huni hsup arr_seq hva sched hvs j t] at h0
  unfold service_of_other_hep_jobs workload_of_other_hep_jobs at h0
  have hjc : arrived_before j t = true → completed_by sched j t = true := by
    intro hab
    unfold pending_earlier_and_at at h1
    rw [hab] at h1
    simpa using h1
  have hB : workload_of_jobs (fun x => hep_job x j && !decide (x ≠ j)) (arrivals_between arr_seq 0 t) =
      service_of_jobs sched (fun x => hep_job x j && !decide (x ≠ j)) (arrivals_between arr_seq 0 t) 0 t := by
    apply (all_jobs_have_completed_equiv_workload_eq_service (unit_supply_is_unit_service PState hsup) arr_seq
      hva.1 sched hmust hcde _ 0 t t).mp
    intro x hin hP
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_not] at hP
    rw [hP.2]
    apply hjc
    have hbt := in_arrivals_implies_arrived_between arr_seq hva.1 x 0 t hin
    rw [hP.2] at hbt
    unfold arrived_between at hbt; unfold arrived_before
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbt
    exact decide_eq_true hbt.2
  have hall : workload_of_jobs (fun x => hep_job x j) (arrivals_between arr_seq 0 t) =
      service_of_jobs sched (fun x => hep_job x j) (arrivals_between arr_seq 0 t) 0 t := by
    rw [workload_of_jobs_case_on_pred _ _ (fun x => decide (x ≠ j)),
      service_of_jobs_case_on_pred sched _ 0 t _ (fun x => decide (x ≠ j)), hB]
    congr 1
    exact h0.symm
  intro jhp hjhp hhep hab
  apply (all_jobs_have_completed_equiv_workload_eq_service (unit_supply_is_unit_service PState hsup) arr_seq
    hva.1 sched hmust hcde _ 0 t t).mpr hall jhp _ hhep
  unfold arrived_before at hab
  exact job_in_arrivals_between arr_seq hva.1 jhp 0 t hjhp (Nat.zero_le _) (of_decide_eq_true hab)

theorem instantiated_quiet_time_equivalent_quiet_time [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j →
    ∀ t : instant, Classical.quiet_time arr_seq sched j t ↔
      @Prosa.Analysis.Abstract.Definitions.quiet_time Job _ (rs_readiness_jlfp_interference arr_seq sched)
        (rs_readiness_jlfp_interfering_workload arr_seq sched) _ _ _ sched j t = true := by
  intro huni hsup JobReady0 arr_seq hva sched hvs JLFP hrefl j hj t
  exact ⟨quiet_time_cl_implies_quiet_time_ab huni hsup arr_seq hva sched hvs hrefl j hj t,
    quiet_time_ab_implies_quiet_time_cl huni hsup arr_seq hva sched hvs hrefl j hj t⟩

theorem instantiated_busy_interval_prefix_equivalent_busy_interval_prefix [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j →
    ∀ t1 t2 : instant, Classical.busy_interval_prefix arr_seq sched j t1 t2 ↔
      @Prosa.Analysis.Abstract.Definitions.busy_interval_prefix Job _
        (rs_readiness_jlfp_interference arr_seq sched) (rs_readiness_jlfp_interfering_workload arr_seq sched)
        _ _ _ sched j t1 t2 := by
  intro huni hsup JobReady0 arr_seq hva sched hvs JLFP hrefl j hj t1 t2
  have hq := instantiated_quiet_time_equivalent_quiet_time huni hsup arr_seq hva sched hvs hrefl j hj
  unfold Classical.busy_interval_prefix Prosa.Analysis.Abstract.Definitions.busy_interval_prefix
  constructor
  · rintro ⟨_, hqt1, hnq, harr⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at harr
    refine ⟨harr, (hq t1).mp hqt1, ?_⟩
    intro t ht hqa
    exact hnq t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ht) ((hq t).mpr hqa)
  · rintro ⟨harr, hqa1, hnq⟩
    refine ⟨by omega', (hq t1).mpr hqa1, ?_, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact harr⟩
    intro t ht hqt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    exact hnq t ht ((hq t).mp hqt)

theorem instantiated_busy_interval_equivalent_busy_interval [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j →
    ∀ t1 t2 : instant, Classical.busy_interval arr_seq sched j t1 t2 ↔
      @Prosa.Analysis.Abstract.Definitions.busy_interval Job _ (rs_readiness_jlfp_interference arr_seq sched)
        (rs_readiness_jlfp_interfering_workload arr_seq sched) _ _ _ sched j t1 t2 := by
  intro huni hsup JobReady0 arr_seq hva sched hvs JLFP hrefl j hj t1 t2
  have hp := instantiated_busy_interval_prefix_equivalent_busy_interval_prefix huni hsup arr_seq hva sched hvs
    hrefl j hj t1 t2
  have hq := instantiated_quiet_time_equivalent_quiet_time huni hsup arr_seq hva sched hvs hrefl j hj t2
  unfold Classical.busy_interval Prosa.Analysis.Abstract.Definitions.busy_interval
  exact ⟨fun h => ⟨hp.mp h.1, hq.mp h.2⟩, fun h => ⟨hp.mpr h.1, hq.mpr h.2⟩⟩

theorem abstract_busy_interval_classic_quiet_time [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j →
    ∀ t1 t2 : instant, @Prosa.Analysis.Abstract.Definitions.busy_interval Job _
        (rs_readiness_jlfp_interference arr_seq sched) (rs_readiness_jlfp_interfering_workload arr_seq sched)
        _ _ _ sched j t1 t2 → Classical.quiet_time arr_seq sched j t1 := by
  intro huni hsup JobReady0 arr_seq hva sched hvs JLFP hrefl j hj t1 t2 hb
  exact ((instantiated_busy_interval_equivalent_busy_interval huni hsup arr_seq hva sched hvs hrefl j hj
    t1 t2).mpr hb).1.2.1

theorem abstract_busy_interval_classic_busy_interval_prefix [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j →
    ∀ t1 t2 : instant, @Prosa.Analysis.Abstract.Definitions.busy_interval Job _
        (rs_readiness_jlfp_interference arr_seq sched) (rs_readiness_jlfp_interfering_workload arr_seq sched)
        _ _ _ sched j t1 t2 → Classical.busy_interval_prefix arr_seq sched j t1 t2 := by
  intro huni hsup JobReady0 arr_seq hva sched hvs JLFP hrefl j hj t1 t2 hb
  exact ((instantiated_busy_interval_equivalent_busy_interval huni hsup arr_seq hva sched hvs hrefl j hj
    t1 t2).mpr hb).1

theorem pending_hep_job_exists_inside_busy_interval [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ j : Job, arrives_in arr_seq j → 0 < job_cost j →
    ∀ t1 t2 : instant, @Prosa.Analysis.Abstract.Definitions.busy_interval_prefix Job _
        (rs_readiness_jlfp_interference arr_seq sched) (rs_readiness_jlfp_interfering_workload arr_seq sched)
        _ _ _ sched j t1 t2 →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t2)) = true →
      ∃ jhp : Job, arrives_in arr_seq jhp ∧ pending sched jhp t = true ∧ hep_job jhp j = true := by
  intro huni hsup JobReady0 arr_seq hva sched hvs JLFP hrefl j hj hpos t1 t2 hbp t ht
  have hcl := (instantiated_busy_interval_prefix_equivalent_busy_interval_prefix huni hsup arr_seq hva sched
    hvs hrefl j hj t1 t2).mpr hbp
  exact pending_hp_job_exists arr_seq hva sched (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs)
    JLFP j hj (by unfold job_cost_positive; exact decide_eq_true hpos) hrefl t1 t2 hcl t ht

theorem not_interference_implies_scheduled [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    fully_consuming_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job], Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → 0 < job_cost j →
    ∀ t1 t2 : instant, @Prosa.Analysis.Abstract.Definitions.busy_interval_prefix Job _
        (rs_readiness_jlfp_interference arr_seq sched) (rs_readiness_jlfp_interfering_workload arr_seq sched)
        _ _ _ sched j t1 t2 →
    ∀ t : instant, (!@Interference.interference Job _ (rs_readiness_jlfp_interference arr_seq sched) j t) = true →
      receives_service_at sched j t = true := by
  intro hcons JobReady0 arr_seq hva sched hvs JLFP hwc j _ _ t1 t2 _ t hnint
  have hfrom := hvs.1
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have h0 : @Interference.interference Job _ (rs_readiness_jlfp_interference arr_seq sched) j t = false := by
    simpa using hnint
  have hni : (is_blackout sched t || another_hep_job_interference arr_seq sched j t ||
      ReadinessAware.service_inversion arr_seq sched j t ||
      (has_supply sched t && !some_hep_job_ready arr_seq sched j t)) = false := h0
  simp only [Bool.or_eq_false_iff] at hni
  obtain ⟨⟨⟨hbl, hahi⟩, hsi⟩, hrd⟩ := hni
  have hsupp : has_supply sched t = true := by unfold is_blackout at hbl; simpa using hbl
  rw [hsupp] at hrd
  have hready : some_hep_job_ready arr_seq sched j t = true := by simpa using hrd
  apply ideal_progress_inside_supplies hcons sched j t hsupp
  -- a scheduled job at t is served and of higher-or-equal priority, hence it is j
  have hserved_hep : ∀ x, scheduled_at sched x t = true → hep_job x j = true → x = j := by
    intro x hx hhx
    have hrx := ideal_progress_inside_supplies hcons sched x t hsupp hx
    have hinx := receives_service_and_served_at_consistent arr_seq hva sched hfrom hmust x t hrx
    unfold another_hep_job_interference at hahi
    have := List.any_eq_false.mp hahi x (of_decide_eq_true hinx)
    unfold another_hep_job at this
    simpa [hhx] using this
  unfold ReadinessAware.service_inversion Pred.service_inversion at hsi
  rw [hready] at hsi
  simp only [Bool.true_and, Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at hsi
  rcases hsi with hjin | hall
  · exact service_at_implies_scheduled_at sched j t
      (by have := served_at_and_receives_service_consistent arr_seq sched j t (decide_eq_true hjin)
          unfold receives_service_at at this; exact of_decide_eq_true this)
  · -- every served job has higher-or-equal priority; take a ready higher-or-equal-priority job
    have hall' : ∀ x, scheduled_at sched x t = true → hep_job x j = true := by
      intro x hx
      have hrx := ideal_progress_inside_supplies hcons sched x t hsupp hx
      have hinx := receives_service_and_served_at_consistent arr_seq hva sched hfrom hmust x t hrx
      have := List.any_eq_false.mp hall x (of_decide_eq_true hinx)
      simpa [hep_job_at_jlfp] using this
    unfold some_hep_job_ready at hready
    obtain ⟨jo, hjo, hrjo⟩ := List.any_eq_true.mp hready
    have hjo' := List.mem_filter.mp hjo
    cases hsj : scheduled_at sched jo t
    · have hback : backlogged sched jo t = true := by unfold backlogged; rw [hrjo, hsj]; rfl
      have harr : arrives_in arr_seq jo := by
        unfold arrivals_up_to at hjo'
        exact in_arrivals_implies_arrived arr_seq jo _ _ (decide_eq_true hjo'.1)
      obtain ⟨j', hj'⟩ := hwc jo t harr hback
      have := hserved_hep j' hj' (hall' j' hj')
      subst this; exact hj'
    · have := hserved_hep jo hsj (hall' jo hsj)
      subst this; exact hsj

theorem scheduled_implies_no_interference [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → fully_consuming_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ (j : Job) (t : instant), receives_service_at sched j t = true →
      (!@Interference.interference Job _ (rs_readiness_jlfp_interference arr_seq sched) j t) = true := by
  intro huni hcons JobReady0 arr_seq hva sched hvs JLFP hrefl j t hrs
  have hfrom := hvs.1
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hsupp := receives_service_implies_has_supply sched j t hrs
  have e1 : is_blackout sched t = false := by simpa using no_blackout_when_service_received sched j t hrs
  have e2 : another_hep_job_interference arr_seq sched j t = false := by
    simpa using no_ahep_interference_when_served huni hcons arr_seq hva sched hfrom hmust JLFP j t hsupp hrs
  have hin := receives_service_and_served_at_consistent arr_seq hva sched hfrom hmust j t hrs
  have e3 : ReadinessAware.service_inversion arr_seq sched j t = false := by
    unfold ReadinessAware.service_inversion Pred.service_inversion
    rw [hin]; simp
  have hsched : scheduled_at sched j t = true := by
    unfold receives_service_at at hrs
    exact service_at_implies_scheduled_at sched j t (of_decide_eq_true hrs)
  have e4 : some_hep_job_ready arr_seq sched j t = true := by
    unfold some_hep_job_ready
    have hin' := of_decide_eq_true hin
    unfold served_jobs_at at hin'
    exact List.any_eq_true.mpr ⟨j, List.mem_filter.mpr ⟨(List.mem_filter.mp hin').1, hrefl j⟩,
      hvs.2 j t hsched⟩
  show (!(is_blackout sched t || another_hep_job_interference arr_seq sched j t ||
    ReadinessAware.service_inversion arr_seq sched j t ||
    (has_supply sched t && !some_hep_job_ready arr_seq sched j t))) = true
  rw [e1, e2, e3, e4]; simp

theorem instantiated_i_and_w_are_coherent_with_schedule [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → fully_consuming_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
      @Prosa.Analysis.Abstract.Definitions.work_conserving Job _ (rs_readiness_jlfp_interference arr_seq sched)
        (rs_readiness_jlfp_interfering_workload arr_seq sched) _ _ _ arr_seq sched := by
  intro huni hcons JobReady0 arr_seq hva sched hvs JLFP hrefl hwc j t1 t2 t hj hpos hbp _
  constructor
  · intro hnint
    exact not_interference_implies_scheduled hcons arr_seq hva sched hvs hwc j hj hpos t1 t2 hbp t
      (by simpa using hnint)
  · intro hrs
    have := scheduled_implies_no_interference huni hcons arr_seq hva sched hvs hrefl j t hrs
    simpa using this

theorem instantiated_interference_and_workload_consistent_with_sequential_tasks [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ tsk : Task, policy_respects_sequential_tasks (Task := Task) JLFP →
      @interference_and_workload_consistent_with_sequential_tasks Job _ Task _ _ _ _ _ arr_seq sched tsk
        (rs_readiness_jlfp_interference arr_seq sched) (rs_readiness_jlfp_interfering_workload arr_seq sched) := by
  intro huni hsup JobReady0 arr_seq hva sched hvs JLFP hrefl tsk hseq j t1 t2 hj htsk _ hb
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hcl := (instantiated_busy_interval_equivalent_busy_interval huni hsup arr_seq hva sched hvs hrefl j hj
    t1 t2).mpr hb
  obtain ⟨⟨_, hqt, _, harr⟩, _⟩ := hcl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at harr
  unfold task_workload_between task_workload task_service_of_jobs_in
  apply (all_jobs_have_completed_equiv_workload_eq_service (unit_supply_is_unit_service PState hsup) arr_seq
    hva.1 sched hmust hcde _ 0 t1 t1).mp
  intro s hin hst
  have hbt := in_arrivals_implies_arrived_between arr_seq hva.1 s 0 t1 hin
  unfold arrived_between at hbt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbt
  apply hqt s (in_arrivals_implies_arrived arr_seq s 0 t1 hin)
  · apply hseq s j
    · unfold job_of_task at hst htsk
      rw [of_decide_eq_true hst, of_decide_eq_true htsk]; simp
    · omega'
  · unfold arrived_before; exact decide_eq_true hbt.2

theorem instantiated_i_and_w_no_speculative_execution [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JLFP : JLFP_policy Job],
    @no_speculative_execution Job _ (rs_readiness_jlfp_interference arr_seq sched)
      (rs_readiness_jlfp_interfering_workload arr_seq sched) := by
  intro huni hsup JobReady0 arr_seq hva sched hvs JLFP j t
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  rw [cumulative_interference_split huni arr_seq sched hvs j 0 t,
    cumulative_interfering_workload_split arr_seq sched j 0 t,
    cumulative_i_ohep_eq_service_of_ohep huni arr_seq hva sched hmust hcde
      JLFP (unit_supply_is_unit_service PState hsup) j 0 t (classical_quiet_time_zero arr_seq sched j),
    cumulative_iw_hep_eq_workload_of_ohep]
  have := service_of_jobs_le_workload (unit_supply_is_unit_service PState hsup) sched hcde
    (fun jhp => another_hep_job jhp j) (arrivals_between arr_seq 0 t) 0 t
  unfold service_of_other_hep_jobs workload_of_other_hep_jobs
  omega'

end IWInstantiation

end Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness
