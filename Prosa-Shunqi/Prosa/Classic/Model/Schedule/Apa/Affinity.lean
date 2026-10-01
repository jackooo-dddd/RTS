-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/apa/affinity.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 29)

import Prosa.Classic.Util.Seqset
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule

/-!
Processor affinities (Rocq module `Affinity`).

Representation notes: an affinity `{set (processor num_cpus)}` is the accepted
v0.6 sequence-set `Prosa.Util.Seqset.set (Fin num_cpus)`; `cpu \in alpha` is
`decide (cpu ∈ alpha)`; `{subset A <= B}` is `∀ x, x ∈ A → x ∈ B`; `#|A|` is
`(Finset.univ.filter (· ∈ A)).card` (as in classic `Seqset`); the Boolean
quantifier `[exists cpu, P cpu]` is `(List.finRange num_cpus).any P`.
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask

universe u v

abbrev affinity (num_cpus : Nat) := Prosa.Util.Seqset.set (processor num_cpus)

abbrev task_affinity (sporadic_task : Type u) [DecidableEq sporadic_task] (num_cpus : Nat) :=
  sporadic_task → affinity num_cpus

def can_execute_on {sporadic_task : Type u} [DecidableEq sporadic_task] {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus) (tsk : sporadic_task)
    (cpu : processor num_cpus) : Bool :=
  decide (cpu ∈ alpha tsk)

def task_scheduled_on_affinity {sporadic_task : Type u} [DecidableEq sporadic_task]
    {num_cpus : Nat} {Job : Type v} [DecidableEq Job] (job_task : Job → sporadic_task)
    (sched : schedule Job num_cpus) (alpha : affinity num_cpus) (tsk : sporadic_task)
    (t : time) : Bool :=
  (List.finRange num_cpus).any
    (fun cpu => decide (cpu ∈ alpha) && task_scheduled_on job_task sched tsk cpu t)

def is_subaffinity {num_cpus : Nat} (alpha' alpha : affinity num_cpus) : Prop :=
  ∀ x, x ∈ alpha' → x ∈ alpha

theorem leq_subaffinity {num_cpus : Nat} (alpha' alpha : affinity num_cpus)
    (H_subaffinity : is_subaffinity alpha' alpha) :
    (Finset.univ.filter (fun x => x ∈ alpha')).card ≤
      (Finset.univ.filter (fun x => x ∈ alpha)).card := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact H_subaffinity x hx

def affinity_intersects {num_cpus : Nat} (alpha alpha' : affinity num_cpus) : Bool :=
  (List.finRange num_cpus).any (fun cpu => decide (cpu ∈ alpha) && decide (cpu ∈ alpha'))

end Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity
