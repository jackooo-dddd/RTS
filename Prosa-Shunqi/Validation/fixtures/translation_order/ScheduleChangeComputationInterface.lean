import Prosa.Analysis.Definitions.Overheads.ScheduleChange

namespace Prosa.Validation.ScheduleChangeInterface

open Prosa.Analysis.Definitions.Overheads.ScheduleChange
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Overheads

universe u

theorem production_index_iota_eq (a b : Nat) :
    Prosa.Util.List.index_iota a b = List.range' a (b - a) := rfl

theorem production_range_prime_zero (start : Nat) :
    List.range' start 0 = [] := rfl

theorem production_range_prime_succ (start len : Nat) :
    List.range' start (Nat.succ len) =
      start :: List.range' (start + 1) len := rfl

theorem production_nat_pred_zero : Nat.pred 0 = 0 := rfl

theorem production_nat_pred_succ (n : Nat) : Nat.pred (n + 1) = n := by
  simp

theorem production_countP_nil (P : Nat → Bool) :
    List.countP P ([] : List Nat) = 0 := rfl

theorem production_countP_cons (P : Nat → Bool) (t : Nat) (ts : List Nat) :
    List.countP P (t :: ts) =
      List.countP P ts + if P t = true then 1 else 0 := by
  exact List.countP_cons

theorem production_all_nil (P : Nat → Bool) :
    List.all ([] : List Nat) P = true := rfl

theorem production_all_cons (P : Nat → Bool) (t : Nat) (ts : List Nat) :
    List.all (t :: ts) P = (P t && List.all ts P) := rfl

theorem production_schedule_change_eq {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t : instant) :
    schedule_change sched t =
      decide (scheduled_job sched (Nat.pred t) ≠ scheduled_job sched t) := rfl

theorem production_number_schedule_changes_eq {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t1 t2 : instant) :
    number_schedule_changes sched t1 t2 =
      (Prosa.Util.List.index_iota t1 t2).countP (schedule_change sched) := rfl

theorem production_no_schedule_changes_during_eq
    {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t1 t2 : instant) :
    no_schedule_changes_during sched t1 t2 =
      decide (number_schedule_changes sched (t1 + 1) t2 = 0) := rfl

theorem production_scheduled_job_invariant_eq
    {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (oj : Option Job)
    (t1 t2 : instant) :
    scheduled_job_invariant sched oj t1 t2 =
      (Prosa.Util.List.index_iota t1 t2).all
        (fun t => decide (scheduled_job sched t = oj)) := rfl

end Prosa.Validation.ScheduleChangeInterface
