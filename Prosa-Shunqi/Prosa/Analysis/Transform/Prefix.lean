-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/transform/prefix.v

import Prosa.Behavior.All

namespace Prosa.Analysis.Transform.Prefix

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time

/-! Representation notes: the structural recursion on the horizon and the
local `let prefix` are kept (the local is named `pfx`, since `prefix` is a Lean
keyword); a single comparison in `Prop` position is the
Lean proposition. Binder orders follow the elaborated types. -/

section SchedulePrefixMap

variable {Job : JobType} [DecidableEq Job] {PState : ProcessorState Job}

/-- Apply the point-wise transformation `f` to every instant of the prefix
`[0, horizon)` of `sched`. -/
def prefix_map (sched : schedule PState) (f : schedule PState → instant → schedule PState) :
    instant → schedule PState
  | 0 => sched
  | t + 1 =>
    let pfx := prefix_map sched f t
    f pfx t

/-- A property maintained by `f` is maintained by `prefix_map`. -/
theorem prefix_map_property_invariance (P : schedule PState → Prop)
    (f : schedule PState → instant → schedule PState) :
    (∀ (sched : schedule PState) (t : instant), P sched → P (f sched t)) →
      ∀ (sched : schedule PState) (h : instant), P sched → P (prefix_map sched f h) := by
  intro H_f sched h hP
  induction h with
  | zero => exact hP
  | succ h ih => exact H_f _ _ ih

/-- A property established step by step by `f` holds on the whole prefix. -/
theorem prefix_map_pointwise_property (P : schedule PState → Prop)
    (Q : schedule PState → instant → Prop) (f : schedule PState → instant → schedule PState) :
    (∀ (sched : schedule PState) (t_ref : instant), P sched → P (f sched t_ref)) →
      (∀ (sched : schedule PState) (t_ref : Nat), P sched →
        (∀ t' : Nat, t' < t_ref → Q sched t') → ∀ t' : Nat, t' ≤ t_ref → Q (f sched t_ref) t') →
      ∀ (sched : schedule PState) (horizon : Nat), P sched →
        ∀ t : Nat, t < horizon → Q (prefix_map sched f horizon) t := by
  intro H_P H_Q sched horizon hP
  induction horizon with
  | zero => intro t ht; exact absurd ht (Nat.not_lt_zero _)
  | succ h ih =>
    intro t ht
    exact H_Q _ h (prefix_map_property_invariance P f H_P sched h hP) ih t (Nat.le_of_lt_succ ht)

end SchedulePrefixMap

end Prosa.Analysis.Transform.Prefix
