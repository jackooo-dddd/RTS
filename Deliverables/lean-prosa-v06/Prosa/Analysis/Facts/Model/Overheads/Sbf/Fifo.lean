-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/overheads/sbf/fifo.v

import Prosa.Analysis.Facts.Readiness.Basic
import Prosa.Analysis.Facts.Model.Overheads.BlackoutBound
import Prosa.Analysis.Facts.Model.Overheads.ScheduleChangeBound
import Prosa.Analysis.Definitions.Sbf.Busy

namespace Prosa.Analysis.Facts.Model.Overheads.Sbf.Fifo

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Readiness.Basic
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.Overheads
open Prosa.Model.Processor.OverheadResourceModel
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Definitions.Sbf.Busy
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Facts.Behavior.Supply
open Prosa.Analysis.Facts.Model.Overheads.Schedule
open Prosa.Analysis.Facts.Model.Overheads.BlackoutBound
open Prosa.Analysis.Facts.Model.Overheads.ScheduleChangeBound
open Prosa.Util.UnitGrowth
open Prosa.Util.Sum

/-! A supply bound function for FIFO scheduling in the presence of overheads, and its validity.
Binders follow the elaborated source types. The source's `SupplyBoundFunction` (a definitional class, i.e. a
function of the interval length) is the accepted Lean class `SupplyBoundFunction`; statements about it apply
its field `supply_bound_function`. The source's section-local `basic_ready_instance` (implicit in the elaborated
`valid_schedule`, `work_conserving` and `respects_JLFP_policy_at_preemption_point`) is the accepted Lean
definition of the same name, passed explicitly. The source's local instance `fifo_ovh_sbf` (the unslowed SBF)
is not public. Representation: a Boolean in `Prop` position is `= true`; `\sum_(tsk <- ts) F tsk` is
`sumSeq ts F`; `monotone leq f` is `Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) f`. -/

/-- The FIFO blackout bound for an interval of length `Δ`: the number of arrivals in `Δ`, plus one, times the
sum of all overhead bounds. -/
def fifo_blackout_bound {Task : TaskType} [DecidableEq Task] [MaxArrivals Task] (ts : List Task)
    (DB CSB CRPDB : duration) (Δ : duration) : Nat :=
  (DB + CSB + CRPDB) * (1 + sumSeq ts (fun tsk => max_arrivals tsk Δ))

/-- The slowed-down FIFO SBF: the interval length minus the slowed-down blackout bound. -/
def fifo_ovh_sbf_slow {Task : TaskType} [DecidableEq Task] [MaxArrivals Task] (ts : List Task)
    (DB CSB CRPDB : duration) : SupplyBoundFunction :=
  ⟨fun Δ => Δ - slowed (fifo_blackout_bound ts DB CSB CRPDB) Δ⟩

/-- LEAN_HELPER: pointwise-bounded list sums. -/
private theorem fifo_sum_le {α : Type _} (f g : α → Nat) :
    ∀ L : List α, (∀ a ∈ L, f a ≤ g a) → (L.map f).sum ≤ (L.map g).sum
  | [], _ => by simp
  | a :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := fifo_sum_le f g L (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

/-- The slowed SBF is monotone. -/
theorem overheads_sbf_monotone {Task : TaskType} [DecidableEq Task] [MaxArrivals Task] (ts : List Task)
    (DB CSB CRPDB : duration) :
    sbf_is_monotone (fifo_ovh_sbf_slow ts DB CSB CRPDB).supply_bound_function := by
  intro x y hxy
  simp only [decide_eq_true_eq] at hxy ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hxy
  have := unit_growth_function_k_steps_bounded _ (slowed_is_unit_step (fifo_blackout_bound ts DB CSB CRPDB)) x k
  show x - slowed (fifo_blackout_bound ts DB CSB CRPDB) x ≤
    x + k - slowed (fifo_blackout_bound ts DB CSB CRPDB) (x + k)
  ((try dsimp only [instant, duration, work] at *); omega)

/-- The FIFO blackout bound is monotone. -/
theorem fifo_blackout_bound_monotone {Task : TaskType} [DecidableEq Task] [MaxArrivals Task] (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ DB CSB CRPDB : duration,
      Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) (fifo_blackout_bound ts DB CSB CRPDB) := by
  intro hvalid DB CSB CRPDB x y hxy
  simp only [decide_eq_true_eq] at hxy ⊢
  have hsum : sumSeq ts (fun tsk => max_arrivals tsk x) ≤ sumSeq ts (fun tsk => max_arrivals tsk y) := by
    unfold sumSeq
    apply fifo_sum_le
    intro tsk htsk
    have := (hvalid tsk (decide_eq_true htsk)).2 x y (decide_eq_true hxy)
    exact of_decide_eq_true this
  unfold fifo_blackout_bound
  apply Nat.mul_le_mul_left
  ((try dsimp only [instant, duration, work] at *); omega)

/-- The slowed SBF is a unit-supply SBF. -/
theorem overheads_sbf_unit {Task : TaskType} [DecidableEq Task] [MaxArrivals Task] (ts : List Task) :
    valid_taskset_arrival_curve ts max_arrivals →
    ∀ DB CSB CRPDB : duration,
      unit_supply_bound_function (fifo_ovh_sbf_slow ts DB CSB CRPDB).supply_bound_function := by
  intro hvalid DB CSB CRPDB δ
  have hmono := slowed_respects_monotone _ (fifo_blackout_bound_monotone ts hvalid DB CSB CRPDB) δ (δ + 1)
    (by simp)
  simp only [decide_eq_true_eq] at hmono
  show δ + 1 - slowed (fifo_blackout_bound ts DB CSB CRPDB) (δ + 1) ≤
    δ - slowed (fifo_blackout_bound ts DB CSB CRPDB) δ + 1
  ((try dsimp only [instant, duration, work] at *); omega)

/-- The slowed SBF is a valid busy-interval SBF. -/
theorem overheads_sbf_busy_valid {Task : TaskType} [DecidableEq Task] [MaxArrivals Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job]
    (JLFP : JLFP_policy Job) :
    policy_is_FIFO JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
      @no_superfluous_preemptions Job _ _ (JLFP_to_JLDP (JLFP := JLFP)) (processor_state Job) sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq
        sched JLFP →
      valid_preemption_model arr_seq sched →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → taskset_respects_max_arrivals arr_seq ts →
      (∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true) →
    ∀ DB CSB CRPDB : duration, overhead_resource_model sched DB CSB CRPDB →
    ∀ tsk : Task, valid_busy_sbf arr_seq sched tsk (fifo_ovh_sbf_slow ts DB CSB CRPDB).supply_bound_function := by
  intro hfifo arr_seq hva sched hvs hwc hnsp hresp hvpm ts hall hrespma hpos DB CSB CRPDB horm tsk
  refine ⟨by show 0 - _ = 0; exact Nat.zero_sub _, ?_⟩
  intro j t1 t2 harr ⟨_, hbip⟩ t ⟨h1, h2⟩
  obtain ⟨δ, rfl⟩ := Nat.exists_eq_add_of_le h1
  have hsup := supply_during_complement sched overheads_proc_model_provides_unit_supply t1 δ
  rw [hsup]
  show t1 + δ - t1 - slowed (fifo_blackout_bound ts DB CSB CRPDB) (t1 + δ - t1) ≤
    δ - blackout_during sched t1 (t1 + δ)
  rw [Nat.add_sub_cancel_left]
  have hunit : unit_growth_function (fun x => blackout_during sched t1 (t1 + x)) := by
    intro x
    show blackout_during sched t1 (t1 + (x + 1)) ≤ blackout_during sched t1 (t1 + x) + 1
    have := blackout_during_unit_growth sched t1 (t1 + x)
    rw [show t1 + (x + 1) = t1 + x + 1 by ((try dsimp only [instant, duration, work] at *); omega)]
    exact this
  have hle : ∀ x, x ≤ δ → blackout_during sched t1 (t1 + x) ≤ fifo_blackout_bound ts DB CSB CRPDB x := by
    intro x hx
    have hb := finite_sched_changes_bounded_overheads_blackout sched DB CSB CRPDB horm
      (Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes sched (t1 + 1) (t1 + x))
      t1 (t1 + x) rfl
    have hc := schedule_changes_bounded_by_total_arrivals_FIFO JLFP hfifo arr_seq hva sched hvs hwc hnsp
      hresp hvpm j harr (hpos j harr) t1 t2 hbip ts hall hrespma x (by ((try dsimp only [instant, duration, work] at *); omega))
    unfold fifo_blackout_bound
    refine Nat.le_trans hb (Nat.mul_le_mul_left _ ?_)
    ((try dsimp only [instant, duration, work] at *); omega)
  have := slowed_respects_pointwise_leq _ _ δ hunit hle
  ((try dsimp only [instant, duration, work] at *); omega)

end Prosa.Analysis.Facts.Model.Overheads.Sbf.Fifo
