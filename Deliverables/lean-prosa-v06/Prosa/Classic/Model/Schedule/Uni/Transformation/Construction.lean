-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/transformation/construction.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 60)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.Schedule

/-!
Constructing a uniprocessor schedule from prefixes (Rocq module `ScheduleConstruction`).

Representation notes (as in the global `classic/model/schedule/global/transformation/construction.v`):
* `t == t_next` is `decide (t = t_next)`; `if t_max is t_prev.+1 then … else …` is a match on `t_max`.
* The section-local `Let sched := build_schedule_from_prefixes` is unfolded.
* Binder lists follow the Rocq contract: the unused section variable `arr_seq` is not abstracted.
-/

namespace Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule

universe u

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def update_schedule {Job : Type u} [DecidableEq Job] (build_schedule : schedule Job → time → Option Job)
    (prev_sched : schedule Job) (t_next : time) : schedule Job :=
  fun t => if decide (t = t_next) then build_schedule prev_sched t else prev_sched t

def schedule_prefix {Job : Type u} [DecidableEq Job] (build_schedule : schedule Job → time → Option Job)
    (base_sched : schedule Job) : time → schedule Job
  | 0 => update_schedule build_schedule base_sched 0
  | t_prev + 1 => update_schedule build_schedule (schedule_prefix build_schedule base_sched t_prev) (t_prev + 1)

def build_schedule_from_prefixes {Job : Type u} [DecidableEq Job]
    (build_schedule : schedule Job → time → Option Job) (base_sched : schedule Job) : schedule Job :=
  fun t => schedule_prefix build_schedule base_sched t t

theorem prefix_construction_same_prefix {Job : Type u} [DecidableEq Job]
    (build_schedule : schedule Job → time → Option Job) (base_sched : schedule Job) :
    ∀ (t t_max : Nat), t ≤ t_max →
      schedule_prefix build_schedule base_sched t_max t = build_schedule_from_prefixes build_schedule base_sched t := by
  intro t t_max LEt
  induction t_max with
  | zero => rw [Nat.le_zero.mp LEt]; rfl
  | succ t_max IH =>
    rcases Nat.lt_or_eq_of_le LEt with LESS | EQ
    · have hne : ¬ t = t_max + 1 := by omega
      simp only [schedule_prefix, update_schedule, hne, decide_false, Bool.false_eq_true, if_false]
      exact IH (by omega)
    · subst EQ; rfl

theorem service_dependent_schedule_construction {Job : Type u} [DecidableEq Job]
    (build_schedule : schedule Job → time → Option Job) (base_sched : schedule Job)
    (H_depends_only_on_service : ∀ (sched1 sched2 : schedule Job) (t : time),
      (∀ j, service sched1 j t = service sched2 j t) → build_schedule sched1 t = build_schedule sched2 t) :
    ∀ t : time, build_schedule_from_prefixes build_schedule base_sched t =
      build_schedule (build_schedule_from_prefixes build_schedule base_sched) t := by
  intro t
  rw [← prefix_construction_same_prefix build_schedule base_sched t t (Nat.le_refl t)]
  cases t with
  | zero =>
    simp only [schedule_prefix, update_schedule, decide_true, if_true]
    apply H_depends_only_on_service
    intro j; simp [service, service_during]
  | succ t =>
    simp only [schedule_prefix, update_schedule, decide_true, if_true]
    apply H_depends_only_on_service
    intro j
    unfold service service_during
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    unfold service_at scheduled_at
    rw [prefix_construction_same_prefix build_schedule base_sched i t (by omega')]

theorem prefix_dependent_schedule_construction {Job : Type u} [DecidableEq Job]
    (build_schedule : schedule Job → time → Option Job) (base_sched : schedule Job)
    (H_depends_only_on_prefix : ∀ (sched1 sched2 : schedule Job) (t : time),
      (∀ t0, t0 < t → sched1 t0 = sched2 t0) → build_schedule sched1 t = build_schedule sched2 t) :
    ∀ t : time, build_schedule_from_prefixes build_schedule base_sched t =
      build_schedule (build_schedule_from_prefixes build_schedule base_sched) t := by
  intro t
  rw [← prefix_construction_same_prefix build_schedule base_sched t t (Nat.le_refl t)]
  cases t with
  | zero =>
    simp only [schedule_prefix, update_schedule, decide_true, if_true]
    apply H_depends_only_on_prefix
    intro t0 h; exact absurd h (Nat.not_lt_zero _)
  | succ t =>
    simp only [schedule_prefix, update_schedule, decide_true, if_true]
    apply H_depends_only_on_prefix
    intro t0 LT
    exact prefix_construction_same_prefix build_schedule base_sched t0 t (by omega')

theorem immediate_property_of_schedule_construction {Job : Type u} [DecidableEq Job]
    (build_schedule : schedule Job → time → Option Job) (base_sched : schedule Job) (P : Option Job → Prop)
    (H_immediate_property : ∀ (sched_prefix : schedule Job) (t : time), P (build_schedule sched_prefix t)) :
    ∀ t : time, P (build_schedule_from_prefixes build_schedule base_sched t) := by
  intro t
  cases t with
  | zero =>
    simp only [build_schedule_from_prefixes, schedule_prefix, update_schedule, decide_true, if_true]
    exact H_immediate_property _ _
  | succ t =>
    simp only [build_schedule_from_prefixes, schedule_prefix, update_schedule, decide_true, if_true]
    exact H_immediate_property _ _

end Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
