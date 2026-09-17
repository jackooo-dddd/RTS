-- Translated from: ../rt-proofs/classic/model/schedule/global/transformation/construction.v
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Global.Transformation.Construction

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Schedule

namespace ScheduleConstruction

section ConstructionFromPrefixes

variable {Job : Type _} [DecidableEq Job]
variable (arr_seq : arrival_sequence Job)
variable {num_cpus : ℕ}
variable (build_schedule_fn : schedule Job num_cpus → schedule Job num_cpus)
variable (base_sched : schedule Job num_cpus)

def update_schedule (prev_sched : schedule Job num_cpus)
    (t_next : Time) : schedule Job num_cpus :=
  fun (cpu : processor num_cpus) t =>
    if t == t_next then
      build_schedule_fn prev_sched cpu t
    else prev_sched cpu t

def schedule_prefix : Time → schedule Job num_cpus
  | 0 => update_schedule build_schedule_fn base_sched 0
  | (t_prev + 1) =>
    update_schedule build_schedule_fn
      (schedule_prefix t_prev) (t_prev + 1)

def build_schedule_from_prefixes : schedule Job num_cpus :=
  fun cpu t => schedule_prefix build_schedule_fn base_sched t cpu t

section Lemmas

theorem prefix_construction_same_prefix :
    ∀ t t_max cpu,
      t ≤ t_max →
      schedule_prefix build_schedule_fn base_sched t_max cpu t =
        build_schedule_from_prefixes build_schedule_fn base_sched cpu t := by
  intro t t_max cpu h_le
  induction t_max with
  | zero =>
    have h_eq : t = 0 := Nat.le_zero.mp h_le
    subst h_eq
    rfl
  | succ t_max ih =>
    rcases Nat.eq_or_lt_of_le h_le with h_eq | h_lt
    · subst h_eq; rfl
    · have h_le' : t ≤ t_max := Nat.lt_succ_iff.mp h_lt
      specialize ih h_le'
      change (update_schedule build_schedule_fn (schedule_prefix build_schedule_fn base_sched t_max) (t_max + 1)) cpu t = _
      unfold update_schedule
      split
      · next h_eq =>
        exfalso
        have h_le' : t ≤ t_max := Nat.lt_succ_iff.mp h_lt
        simp only [beq_iff_eq] at h_eq
        subst h_eq
        exact absurd h_le' (by omega)
      · exact ih

section ServiceDependent

variable (H_depends_only_on_service :
    ∀ sched1 sched2 : schedule Job num_cpus, ∀ cpu t,
      (∀ j, service sched1 j t = service sched2 j t) →
      build_schedule_fn sched1 cpu t = build_schedule_fn sched2 cpu t)
include H_depends_only_on_service

theorem service_dependent_schedule_construction :
    ∀ cpu t,
      build_schedule_from_prefixes build_schedule_fn base_sched cpu t =
        build_schedule_fn (build_schedule_from_prefixes build_schedule_fn base_sched) cpu t := by
  intro cpu t
  show schedule_prefix build_schedule_fn base_sched t cpu t =
    build_schedule_fn (build_schedule_from_prefixes build_schedule_fn base_sched) cpu t
  induction t using Nat.strongRecOn with
  | _ t ih =>
  match t with
  | 0 =>
    simp only [schedule_prefix, update_schedule, beq_self_eq_true, ↓reduceIte]
    apply H_depends_only_on_service
    intro j
    simp only [service, Finset.Ico_self, Finset.sum_empty]
  | t + 1 =>
    simp only [schedule_prefix, update_schedule, beq_self_eq_true, ↓reduceIte]
    apply H_depends_only_on_service
    intro j
    unfold service
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    unfold service_at
    apply Finset.sum_congr rfl
    intro cpu' _
    unfold scheduled_on
    have h_le : i ≤ t := Nat.lt_succ_iff.mp hi.2
    rw [prefix_construction_same_prefix build_schedule_fn base_sched i t cpu' h_le]

end ServiceDependent

section PrefixDependent

variable (H_depends_only_on_prefix :
    ∀ (sched1 sched2 : schedule Job num_cpus) (cpu : processor num_cpus) (t : Time),
      (∀ t0 cpu, t0 < t → sched1 cpu t0 = sched2 cpu t0) →
      build_schedule_fn sched1 cpu t = build_schedule_fn sched2 cpu t)
include H_depends_only_on_prefix

theorem prefix_dependent_schedule_construction :
    ∀ cpu t,
      build_schedule_from_prefixes build_schedule_fn base_sched cpu t =
        build_schedule_fn (build_schedule_from_prefixes build_schedule_fn base_sched) cpu t := by
  intro cpu t
  show schedule_prefix build_schedule_fn base_sched t cpu t =
    build_schedule_fn (build_schedule_from_prefixes build_schedule_fn base_sched) cpu t
  induction t using Nat.strongRecOn with
  | _ t ih =>
  match t with
  | 0 =>
    simp only [schedule_prefix, update_schedule, beq_self_eq_true, ↓reduceIte]
    apply H_depends_only_on_prefix
    intro t0 _ h_lt
    exact absurd h_lt (Nat.not_lt_zero t0)
  | t + 1 =>
    simp only [schedule_prefix, update_schedule, beq_self_eq_true, ↓reduceIte]
    apply H_depends_only_on_prefix
    intro t0 cpu0 h_lt
    have h_le : t0 ≤ t := Nat.lt_succ_iff.mp h_lt
    exact prefix_construction_same_prefix build_schedule_fn base_sched t0 t cpu0 h_le

end PrefixDependent

end Lemmas

end ConstructionFromPrefixes

end ScheduleConstruction

end Prosa.Classic.Model.Schedule.Global.Transformation.Construction
