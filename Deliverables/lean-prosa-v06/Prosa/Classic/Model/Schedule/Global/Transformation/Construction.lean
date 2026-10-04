-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/global/transformation/construction.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 50)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule

/-!
Constructing a global schedule from prefixes (Rocq module `ScheduleConstruction`).

Representation notes:
* `t == t_next` is `decide (t = t_next)`; `if t_max is t_prev.+1 then … else …` is a match on `t_max`.
* The section-local `Let sched := build_schedule_from_prefixes` is unfolded.
* Binder lists follow the Rocq contract: the unused section variable `arr_seq` is not abstracted.
-/

namespace Prosa.Classic.Model.Schedule.Global.Transformation.Construction.ScheduleConstruction

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule

universe u

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def update_schedule {Job : Type u} [DecidableEq Job] (num_cpus : Nat)
    (build_schedule : schedule Job num_cpus → schedule Job num_cpus) (prev_sched : schedule Job num_cpus)
    (t_next : time) : schedule Job num_cpus :=
  fun (cpu : processor num_cpus) t =>
    if decide (t = t_next) then build_schedule prev_sched cpu t else prev_sched cpu t

def schedule_prefix {Job : Type u} [DecidableEq Job] (num_cpus : Nat)
    (build_schedule : schedule Job num_cpus → schedule Job num_cpus) (base_sched : schedule Job num_cpus) :
    time → schedule Job num_cpus
  | 0 => update_schedule num_cpus build_schedule base_sched 0
  | t_prev + 1 =>
    update_schedule num_cpus build_schedule (schedule_prefix num_cpus build_schedule base_sched t_prev) (t_prev + 1)

def build_schedule_from_prefixes {Job : Type u} [DecidableEq Job] (num_cpus : Nat)
    (build_schedule : schedule Job num_cpus → schedule Job num_cpus) (base_sched : schedule Job num_cpus) :
    schedule Job num_cpus :=
  fun cpu t => schedule_prefix num_cpus build_schedule base_sched t cpu t

theorem prefix_construction_same_prefix {Job : Type u} [DecidableEq Job] (num_cpus : Nat)
    (build_schedule : schedule Job num_cpus → schedule Job num_cpus) (base_sched : schedule Job num_cpus) :
    ∀ (t t_max : Nat) (cpu : processor num_cpus), t ≤ t_max →
      schedule_prefix num_cpus build_schedule base_sched t_max cpu t =
        build_schedule_from_prefixes num_cpus build_schedule base_sched cpu t := by
  intro t t_max cpu LEt
  induction t_max with
  | zero => rw [Nat.le_zero.mp LEt]; rfl
  | succ t_max IH =>
    rcases Nat.lt_or_eq_of_le LEt with LESS | EQ
    · have hne : ¬ t = t_max + 1 := by omega
      simp only [schedule_prefix, update_schedule, hne, decide_false, Bool.false_eq_true, if_false]
      exact IH (by omega)
    · subst EQ; rfl

theorem service_dependent_schedule_construction {Job : Type u} [DecidableEq Job] (num_cpus : Nat)
    (build_schedule : schedule Job num_cpus → schedule Job num_cpus) (base_sched : schedule Job num_cpus)
    (H_depends_only_on_service : ∀ (sched1 sched2 : schedule Job num_cpus) (cpu : processor num_cpus) (t : time),
      (∀ j, service sched1 j t = service sched2 j t) →
      build_schedule sched1 cpu t = build_schedule sched2 cpu t) :
    ∀ (cpu : processor num_cpus) (t : time),
      build_schedule_from_prefixes num_cpus build_schedule base_sched cpu t =
        build_schedule (build_schedule_from_prefixes num_cpus build_schedule base_sched) cpu t := by
  intro cpu t
  rw [← prefix_construction_same_prefix num_cpus build_schedule base_sched t t cpu (Nat.le_refl t)]
  cases t with
  | zero =>
    simp only [schedule_prefix, update_schedule, decide_true, if_true]
    apply H_depends_only_on_service
    intro j; simp [service]
  | succ t =>
    simp only [schedule_prefix, update_schedule, decide_true, if_true]
    apply H_depends_only_on_service
    intro j
    unfold service
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    unfold service_at scheduled_on
    congr 1
    apply Finset.filter_congr
    intro cpu' _
    rw [prefix_construction_same_prefix num_cpus build_schedule base_sched i t cpu' (by omega')]

theorem prefix_dependent_schedule_construction {Job : Type u} [DecidableEq Job] (num_cpus : Nat)
    (build_schedule : schedule Job num_cpus → schedule Job num_cpus) (base_sched : schedule Job num_cpus)
    (H_depends_only_on_prefix : ∀ (sched1 sched2 : schedule Job num_cpus) (cpu : processor num_cpus) (t : time),
      (∀ (t0 : time) (cpu : processor num_cpus), t0 < t → sched1 cpu t0 = sched2 cpu t0) →
      build_schedule sched1 cpu t = build_schedule sched2 cpu t) :
    ∀ (cpu : processor num_cpus) (t : time),
      build_schedule_from_prefixes num_cpus build_schedule base_sched cpu t =
        build_schedule (build_schedule_from_prefixes num_cpus build_schedule base_sched) cpu t := by
  intro cpu t
  rw [← prefix_construction_same_prefix num_cpus build_schedule base_sched t t cpu (Nat.le_refl t)]
  cases t with
  | zero =>
    simp only [schedule_prefix, update_schedule, decide_true, if_true]
    apply H_depends_only_on_prefix
    intro t0 _ h; exact absurd h (Nat.not_lt_zero _)
  | succ t =>
    simp only [schedule_prefix, update_schedule, decide_true, if_true]
    apply H_depends_only_on_prefix
    intro t0 cpu0 LT
    exact prefix_construction_same_prefix num_cpus build_schedule base_sched t0 t cpu0 (by omega')

end Prosa.Classic.Model.Schedule.Global.Transformation.Construction.ScheduleConstruction
