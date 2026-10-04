-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/arrival/basic/task.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 22)

import Prosa.Classic.Model.Time
import Prosa.Util.Seqset

/-!
Attributes of valid sporadic tasks and task sets.

Representation notes (classic representation rules, see the plan README):
* `Context {Task : eqType}` is an implicit carrier `{Task}` with
  `[DecidableEq Task]`; model parameters such as `task_cost : Task → time` stay
  explicit function arguments, in the binder order Rocq records after closing
  the sections (checked with `About` on the Rocq 9.3 reference build).
* Definitions whose source body is a Boolean comparison (`>`, `<=`) are `Bool`
  (`decide …`); propositions built from them use `… = true`.
* `taskset_of Task := {set Task}` is the accepted v0.6 sequence-set
  `Prosa.Util.Seqset.set`.
* The Rocq modules `SporadicTask` and `SporadicTaskset` are nested namespaces;
  `Export SporadicTask` inside `SporadicTaskset` is a Lean `export`.
-/

namespace Prosa.Classic.Model.Arrival.Basic.Task

open Prosa.Classic.Model.Time.Time

universe u

namespace SporadicTask

def task_cost_positive {Task : Type u} [DecidableEq Task] (task_cost : Task → time)
    (tsk : Task) : Bool :=
  decide (0 < task_cost tsk)

def task_period_positive {Task : Type u} [DecidableEq Task] (task_period : Task → time)
    (tsk : Task) : Bool :=
  decide (0 < task_period tsk)

def task_deadline_positive {Task : Type u} [DecidableEq Task] (task_deadline : Task → time)
    (tsk : Task) : Bool :=
  decide (0 < task_deadline tsk)

def task_cost_le_deadline {Task : Type u} [DecidableEq Task]
    (task_cost task_deadline : Task → time) (tsk : Task) : Bool :=
  decide (task_cost tsk ≤ task_deadline tsk)

def task_cost_le_period {Task : Type u} [DecidableEq Task]
    (task_cost task_period : Task → time) (tsk : Task) : Bool :=
  decide (task_cost tsk ≤ task_period tsk)

def is_valid_sporadic_task {Task : Type u} [DecidableEq Task]
    (task_cost task_period task_deadline : Task → time) (tsk : Task) : Prop :=
  task_cost_positive task_cost tsk = true ∧
  task_period_positive task_period tsk = true ∧
  task_deadline_positive task_deadline tsk = true ∧
  task_cost_le_deadline task_cost task_deadline tsk = true ∧
  task_cost_le_period task_cost task_period tsk = true

end SporadicTask

namespace SporadicTaskset

export SporadicTask (task_cost_positive task_period_positive task_deadline_positive
  task_cost_le_deadline task_cost_le_period is_valid_sporadic_task)

/-- A task set is a sequence of tasks without duplicates. -/
abbrev taskset_of (Task : Type u) [DecidableEq Task] := Prosa.Util.Seqset.set Task

def valid_sporadic_taskset {Task : Type u} [DecidableEq Task]
    (task_cost task_period task_deadline : Task → time) (ts : List Task) : Prop :=
  ∀ tsk, tsk ∈ ts → SporadicTask.is_valid_sporadic_task task_cost task_period task_deadline tsk

def implicit_deadline_model {Task : Type u} [DecidableEq Task]
    (task_period task_deadline : Task → time) (ts : List Task) : Prop :=
  ∀ tsk, tsk ∈ ts → task_deadline tsk = task_period tsk

def constrained_deadline_model {Task : Type u} [DecidableEq Task]
    (task_period task_deadline : Task → time) (ts : List Task) : Prop :=
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk

def arbitrary_deadline_model : Prop := True

end SporadicTaskset

end Prosa.Classic.Model.Arrival.Basic.Task
