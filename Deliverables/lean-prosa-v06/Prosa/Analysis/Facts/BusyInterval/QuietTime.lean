-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/busy_interval/quiet_time.v

import Prosa.Analysis.Definitions.BusyInterval.Classical
import Prosa.Analysis.Definitions.CarryIn

namespace Prosa.Analysis.Facts.BusyInterval.QuietTime

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.CarryIn

/-! Representation notes: a chained `a < b < c` is
`(decide (a < b) && decide (b < c)) = true`; `~ P` is `¬ P`. Binder orders
follow the elaborated types (`sched` precedes `arr_seq` as in the source
section). -/

section Facts

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job] [JLFP_policy Job]
variable {PState : ProcessorState Job}
variable (sched : schedule PState) (arr_seq : arrival_sequence Job)

/-- Time `0` is always a quiet time. -/
theorem zero_is_quiet_time (j : Job) : quiet_time arr_seq sched j 0 := by
  intro j_hp _ _ hbef
  simp [arrived_before] at hbef

/-- Absence of carry-in at `t` implies that `t` is a quiet time. -/
theorem no_carry_in_implies_quiet_time :
    ∀ (j : Job) (t : instant), no_carry_in arr_seq sched t → quiet_time arr_seq sched j t := by
  intro j t h j_hp harr _ hbef
  exact h j_hp harr hbef

/-- There are no quiet times inside a busy-interval prefix. -/
theorem busy_interval_prefix_no_quiet_time :
    ∀ (j : Job) (t1 t2 : instant), busy_interval_prefix arr_seq sched j t1 t2 →
      ∀ t : Nat, (decide (t1 < t) && decide (t < t2)) = true → ¬ quiet_time arr_seq sched j t := by
  intro j t1 t2 h
  exact h.2.2.1

/-- There are no quiet times inside a busy interval. -/
theorem busy_interval_no_quiet_time :
    ∀ (j : Job) (t1 t2 : instant), busy_interval arr_seq sched j t1 t2 →
      ∀ t : Nat, (decide (t1 < t) && decide (t < t2)) = true → ¬ quiet_time arr_seq sched j t := by
  intro j t1 t2 h
  exact busy_interval_prefix_no_quiet_time sched arr_seq j t1 t2 h.1

end Facts

end Prosa.Analysis.Facts.BusyInterval.QuietTime
