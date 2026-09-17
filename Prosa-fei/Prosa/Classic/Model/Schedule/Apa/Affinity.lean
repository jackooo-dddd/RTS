-- Translated from: ../rt-proofs/classic/model/schedule/apa/affinity.v
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Apa.Affinity

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Schedule ScheduleOfSporadicTask

section AffinityDefs

variable (sporadic_task : Type _)
variable (num_cpus : ℕ)

abbrev affinity := Finset (processor num_cpus)

abbrev task_affinity := sporadic_task → affinity num_cpus

end AffinityDefs

section Properties

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable {num_cpus : ℕ}

section JobProperties

variable (alpha : task_affinity sporadic_task num_cpus)
variable (tsk : sporadic_task)
variable (cpu : processor num_cpus)

def can_execute_on : Prop := cpu ∈ alpha tsk

end JobProperties

section ScheduleProperties

variable {Job : Type _} [DecidableEq Job]
variable (job_task : Job → sporadic_task)
variable (sched : schedule Job num_cpus)
variable (alpha : affinity num_cpus)

def task_scheduled_on_affinity (tsk : sporadic_task) (t : Time) : Prop :=
  ∃ cpu, cpu ∈ alpha ∧ task_scheduled_on job_task sched tsk cpu t = true

end ScheduleProperties

section Subset

variable (alpha' alpha : affinity num_cpus)

def is_subaffinity : Prop := ∀ x, x ∈ alpha' → x ∈ alpha

section Lemmas

variable (H_subaffinity : is_subaffinity alpha' alpha)
include H_subaffinity

theorem leq_subaffinity : alpha'.card ≤ alpha.card := by
  exact Finset.card_le_card (fun x hx => H_subaffinity x hx)

end Lemmas

end Subset

section IntersectingAffinities

def affinity_intersects (alpha alpha' : affinity num_cpus) : Prop :=
  ∃ cpu, cpu ∈ alpha ∧ cpu ∈ alpha'

instance decAffinity_intersects (alpha alpha' : affinity num_cpus) :
    Decidable (affinity_intersects alpha alpha') :=
  decidable_of_iff (alpha ∩ alpha').Nonempty
    ⟨fun ⟨x, hx⟩ => ⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩,
     fun ⟨x, h1, h2⟩ => ⟨x, Finset.mem_inter.mpr ⟨h1, h2⟩⟩⟩

end IntersectingAffinities

end Properties

end Prosa.Classic.Model.Schedule.Apa.Affinity
