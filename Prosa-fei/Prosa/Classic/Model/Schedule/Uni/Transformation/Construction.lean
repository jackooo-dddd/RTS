-- Translated from: ../rt-proofs/classic/model/schedule/uni/transformation/construction.v
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Transformation.Construction

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule

namespace ScheduleConstruction

section ConstructionFromPrefixes

variable {Job : Type _} [DecidableEq Job]

variable (arr_seq : arrival_sequence Job)

variable (build_schedule : schedule Job → Time → Option Job)

variable (base_sched : schedule Job)

def update_schedule (prev_sched : schedule Job) (t_next : Time) : schedule Job :=
  fun t =>
    if t == t_next then
      build_schedule prev_sched t
    else prev_sched t

def schedule_prefix : Time → schedule Job
  | 0 => update_schedule build_schedule base_sched 0
  | (t_prev + 1) => update_schedule build_schedule (schedule_prefix t_prev) (t_prev + 1)

def build_schedule_from_prefixes : schedule Job :=
  fun t => schedule_prefix build_schedule base_sched t t

section Lemmas

variable (sched := build_schedule_from_prefixes build_schedule base_sched)

theorem prefix_construction_same_prefix :
    ∀ t t_max,
      t ≤ t_max →
      schedule_prefix build_schedule base_sched t_max t = build_schedule_from_prefixes build_schedule base_sched t := by
  intro t t_max hle
  induction t_max with
  | zero =>
    have : t = 0 := Nat.le_zero.mp hle
    subst this
    rfl
  | succ t_max ih =>
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · -- t = t_max + 1
      rfl
    · -- t < t_max + 1, i.e. t ≤ t_max
      have hle' : t ≤ t_max := Nat.lt_succ_iff.mp hlt
      unfold schedule_prefix update_schedule
      have hne : t ≠ t_max + 1 := by simp only [Time] at *; omega
      simp only [beq_iff_eq, hne, ↓reduceIte]
      exact ih hle'

section ServiceDependent

variable (H_depends_only_on_service :
    ∀ sched1 sched2 t,
      (∀ j, service sched1 j t = service sched2 j t) →
      build_schedule sched1 t = build_schedule sched2 t)

include H_depends_only_on_service

theorem service_dependent_schedule_construction :
    ∀ t,
      build_schedule_from_prefixes build_schedule base_sched t = build_schedule (build_schedule_from_prefixes build_schedule base_sched) t := by
  intro t
  simp only [build_schedule_from_prefixes]
  cases t with
  | zero =>
    simp only [schedule_prefix, update_schedule, beq_self_eq_true, ↓reduceIte]
    apply H_depends_only_on_service
    intro j
    simp [service, service_during]
  | succ n =>
    simp only [schedule_prefix, update_schedule, beq_self_eq_true, ↓reduceIte]
    apply H_depends_only_on_service
    intro j
    simp only [service, service_during]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    simp only [service_at, scheduled_at, build_schedule_from_prefixes]
    have hle : i ≤ n := by simp only [Time] at *; omega
    have := prefix_construction_same_prefix build_schedule base_sched i n hle
    simp only [build_schedule_from_prefixes] at this
    rw [this]

end ServiceDependent

section PrefixDependent

variable (H_depends_only_on_prefix :
    ∀ (sched1 sched2 : schedule Job) t,
      (∀ t0, t0 < t → sched1 t0 = sched2 t0) →
      build_schedule sched1 t = build_schedule sched2 t)

include H_depends_only_on_prefix

theorem prefix_dependent_schedule_construction :
    ∀ t,
      build_schedule_from_prefixes build_schedule base_sched t = build_schedule (build_schedule_from_prefixes build_schedule base_sched) t := by
  intro t
  simp only [build_schedule_from_prefixes]
  cases t with
  | zero =>
    simp only [schedule_prefix, update_schedule, beq_self_eq_true, ↓reduceIte]
    apply H_depends_only_on_prefix
    intro t0 ht0; exact absurd ht0 (Nat.not_lt_zero _)
  | succ n =>
    simp only [schedule_prefix, update_schedule, beq_self_eq_true, ↓reduceIte]
    apply H_depends_only_on_prefix
    intro t0 ht0
    have hle : t0 ≤ n := by simp only [Time] at *; omega
    exact prefix_construction_same_prefix build_schedule base_sched t0 n hle

end PrefixDependent

section ImmediateProperty

variable (P : Option Job → Prop)

variable (H_immediate_property :
    ∀ sched_prefix t, P (build_schedule sched_prefix t))

include H_immediate_property

theorem immediate_property_of_schedule_construction :
    ∀ t, P (build_schedule_from_prefixes build_schedule base_sched t) := by
  intro t
  simp only [build_schedule_from_prefixes]
  cases t <;> simp [schedule_prefix, update_schedule, H_immediate_property]

end ImmediateProperty

end Lemmas

end ConstructionFromPrefixes

end ScheduleConstruction

end Prosa.Classic.Model.Schedule.Uni.Transformation.Construction
