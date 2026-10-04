-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/susp/last_execution.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 59)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Util.UnitGrowth

/-!
The time after the last execution of a job (Rocq module `LastExecution`, which `Export`s `Job` and
`UniprocessorSchedule`).

Representation notes:
* `[exists t0 : 'I_t, P t0]` is `(List.finRange t).any (fun t0 => P t0)` (ordinals coerced to `nat`);
  `\max_(t_last < t | P t_last) t_last` is the v0.6 `maxFiltered (List.finRange t) (fun x => P x) (fun x => x.val)`
  (the maximum of the ordinals satisfying `P`, `0` if none).
* The section-local `Let`s (`job_scheduled_at`, `job_completed_by`, `scheduled_before`, `last_time_scheduled`) are
  unfolded. Boolean tests in proposition position are `= true`.
* Binder lists follow the Rocq contract (e.g. `last_execution_monotonic` does not take `H_after_arrival`, and
  `last_execution_bounded_by_identity` does not take `H_jobs_must_arrive_to_execute`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Util.Sum (maxFiltered)

universe u

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def time_after_last_execution {Job : Type u} [DecidableEq Job] (job_arrival : Job → time) (sched : schedule Job)
    (j : Job) (t : time) : Nat :=
  if (List.finRange t).any (fun t0 => scheduled_at sched j t0) then
    maxFiltered (List.finRange t) (fun t_last : Fin t => scheduled_at sched j t_last) (fun t_last : Fin t => t_last.val) + 1
  else job_arrival j

/-! ### Proof-local facts about the last scheduled instant -/

private theorem foldr_max_ge (l : List Nat) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
  induction l with
  | nil => intro x h; simp at h
  | cons a l ih =>
    intro x h
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · exact le_trans (ih x h) (by simp)

private theorem foldr_max_mem (l : List Nat) (h : l ≠ []) : l.foldr max 0 ∈ l := by
  induction l with
  | nil => exact absurd rfl h
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hl : l = []
    · subst hl; simp
    · rcases le_total a (l.foldr max 0) with hle | hle
      · rw [max_eq_right hle]; exact List.mem_cons_of_mem _ (ih hl)
      · rw [max_eq_left hle]; exact List.mem_cons_self

/-- LEAN_HELPER: the last instant before `t` at which `j` is scheduled. -/
private theorem last_scheduled_spec {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : Nat)
    (EX : ∃ x, x < t ∧ scheduled_at sched j x = true) :
    let m := maxFiltered (List.finRange t) (fun t_last : Fin t => scheduled_at sched j t_last) (fun t_last : Fin t => t_last.val)
    m < t ∧ scheduled_at sched j m = true ∧ ∀ x, x < t → scheduled_at sched j x = true → x ≤ m := by
  intro m
  have hne : ((List.finRange t).filter (fun t_last : Fin t => scheduled_at sched j t_last)).map (fun t_last : Fin t => t_last.val)
      ≠ [] := by
    obtain ⟨x, hx, hs⟩ := EX
    intro h
    have : (⟨x, hx⟩ : Fin t).val ∈ ((List.finRange t).filter (fun t_last : Fin t => scheduled_at sched j t_last)).map
        (fun t_last : Fin t => t_last.val) := List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_finRange _, hs⟩)
    rw [h] at this; simp at this
  have hmem := foldr_max_mem _ hne
  obtain ⟨y, hy, hym⟩ := List.mem_map.mp hmem
  rw [List.mem_filter] at hy
  have hm : m = y.val := hym.symm
  refine ⟨by rw [hm]; exact y.isLt, by rw [hm]; exact hy.2, ?_⟩
  intro x hx hs
  exact foldr_max_ge _ x (List.mem_map.mpr ⟨⟨x, hx⟩, List.mem_filter.mpr ⟨List.mem_finRange _, hs⟩, rfl⟩)

private theorem any_iff {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : Nat) :
    (List.finRange t).any (fun t0 => scheduled_at sched j t0) = true ↔ ∃ x, x < t ∧ scheduled_at sched j x = true := by
  simp only [List.any_eq_true, List.mem_finRange, true_and]
  constructor
  · rintro ⟨x, h⟩; exact ⟨x.val, x.isLt, h⟩
  · rintro ⟨x, hx, h⟩; exact ⟨⟨x, hx⟩, h⟩

/-- LEAN_HELPER: characterization of `time_after_last_execution`. -/
private theorem tale_spec {Job : Type u} [DecidableEq Job] (job_arrival : Job → time) (sched : schedule Job)
    (j : Job) (t : Nat) :
    ((∃ x, x < t ∧ scheduled_at sched j x = true) →
      0 < time_after_last_execution job_arrival sched j t ∧
      time_after_last_execution job_arrival sched j t ≤ t ∧
      scheduled_at sched j (time_after_last_execution job_arrival sched j t - 1) = true ∧
      ∀ x, x < t → scheduled_at sched j x = true → x < time_after_last_execution job_arrival sched j t) ∧
    ((¬ ∃ x, x < t ∧ scheduled_at sched j x = true) →
      time_after_last_execution job_arrival sched j t = job_arrival j) := by
  constructor
  · intro EX
    have hany := (any_iff sched j t).mpr EX
    obtain ⟨hlt, hs, hmax⟩ := last_scheduled_spec sched j t EX
    simp only [time_after_last_execution, hany, if_true, Nat.add_sub_cancel]
    exact ⟨Nat.succ_pos _, hlt, hs, fun x hx hsx => Nat.lt_succ_of_le (hmax x hx hsx)⟩
  · intro NEX
    have hany : (List.finRange t).any (fun t0 => scheduled_at sched j t0) = false := by
      cases h : (List.finRange t).any (fun t0 => scheduled_at sched j t0)
      · rfl
      · exact absurd ((any_iff sched j t).mp h) NEX
    simp [time_after_last_execution, hany]

/-- LEAN_HELPER: no service in an interval where the job is never scheduled. -/
private theorem service_flat {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (a b : Nat)
    (hab : a ≤ b) (H : ∀ x, a ≤ x → x < b → scheduled_at sched j x = false) :
    service sched j b = service sched j a := by
  unfold service service_during
  rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le a) hab]
  have : ∑ x ∈ Finset.Ico a b, service_at sched j x = 0 :=
    Finset.sum_eq_zero (fun x hx => by
      rw [Finset.mem_Ico] at hx; simp [service_at, H x hx.1 hx.2])
  rw [this, Nat.add_zero]

private theorem service_succ_sched {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (t : Nat)
    (h : scheduled_at sched j t = true) : service sched j (t + 1) = service sched j t + 1 := by
  unfold service service_during
  rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
  simp [service_at, h]

private theorem service_mono {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job) (a b : Nat)
    (hab : a ≤ b) : service sched j a ≤ service sched j b := by
  unfold service service_during
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.le_refl 0) hab)

/-! ### Lemmas -/

theorem last_execution_after_arrival {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (j : Job) :
    ∀ t, has_arrived job_arrival j (time_after_last_execution job_arrival sched j t) = true := by
  intro t
  by_cases EX : ∃ x, x < t ∧ scheduled_at sched j x = true
  · obtain ⟨hpos, _, hs, _⟩ := (tale_spec job_arrival sched j t).1 EX
    have := H_jobs_must_arrive_to_execute j _ hs
    simp only [has_arrived, decide_eq_true_eq] at this ⊢
    omega'
  · rw [(tale_spec job_arrival sched j t).2 EX]
    simp [has_arrived]

theorem last_execution_monotonic {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (j : Job) (t1 : time) :
    ∀ t2 : Nat, t1 ≤ t2 →
      time_after_last_execution job_arrival sched j t1 ≤ time_after_last_execution job_arrival sched j t2 := by
  intro t2 LE12
  by_cases EX1 : ∃ x, x < t1 ∧ scheduled_at sched j x = true
  · have EX2 : ∃ x, x < t2 ∧ scheduled_at sched j x = true := by
      obtain ⟨x, hx, hs⟩ := EX1; exact ⟨x, by omega', hs⟩
    obtain ⟨p1, _, s1, _⟩ := (tale_spec job_arrival sched j t1).1 EX1
    obtain ⟨_, _, _, m2⟩ := (tale_spec job_arrival sched j t2).1 EX2
    have h1 := (tale_spec job_arrival sched j t1).1 EX1
    have := m2 _ (by omega') s1
    omega'
  · rw [(tale_spec job_arrival sched j t1).2 EX1]
    by_cases EX2 : ∃ x, x < t2 ∧ scheduled_at sched j x = true
    · obtain ⟨p2, _, s2, _⟩ := (tale_spec job_arrival sched j t2).1 EX2
      have := H_jobs_must_arrive_to_execute j _ s2
      simp only [has_arrived, decide_eq_true_eq] at this
      omega'
    · rw [(tale_spec job_arrival sched j t2).2 EX2]

theorem last_execution_idempotent {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (j : Job) :
    ∀ t, time_after_last_execution job_arrival sched j (time_after_last_execution job_arrival sched j t) =
      time_after_last_execution job_arrival sched j t := by
  intro t
  by_cases EX : ∃ x, x < t ∧ scheduled_at sched j x = true
  · obtain ⟨hpos, hle, hs, hmax⟩ := (tale_spec job_arrival sched j t).1 EX
    set T := time_after_last_execution job_arrival sched j t
    have EX' : ∃ x, x < T ∧ scheduled_at sched j x = true := ⟨T - 1, by omega', hs⟩
    obtain ⟨_, hle', hs', hmax'⟩ := (tale_spec job_arrival sched j T).1 EX'
    have h1 := hmax' (T - 1) (by omega') hs
    have h2 := hmax _ (by omega') hs'
    omega'
  · rw [(tale_spec job_arrival sched j t).2 EX]
    apply (tale_spec job_arrival sched j (job_arrival j)).2
    rintro ⟨x, hx, hs⟩
    have := H_jobs_must_arrive_to_execute j x hs
    simp only [has_arrived, decide_eq_true_eq] at this
    omega'

theorem last_execution_bounded_by_identity {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (sched : schedule Job) (j : Job) (t : time) (H_after_arrival : has_arrived job_arrival j t = true) :
    time_after_last_execution job_arrival sched j t ≤ t := by
  by_cases EX : ∃ x, x < t ∧ scheduled_at sched j x = true
  · exact ((tale_spec job_arrival sched j t).1 EX).2.1
  · rw [(tale_spec job_arrival sched j t).2 EX]
    simpa [has_arrived] using H_after_arrival

/-- LEAN_HELPER: equal service at `t ≤ t'` means no scheduling in `[t, t')`. -/
private theorem same_service_not_scheduled {Job : Type u} [DecidableEq Job] (sched : schedule Job) (j : Job)
    (t t' : Nat) (hle : t ≤ t') (SERV : service sched j t = service sched j t') :
    ∀ x, t ≤ x → x < t' → scheduled_at sched j x = false := by
  intro x h1 h2
  cases hs : scheduled_at sched j x
  · rfl
  · have := service_succ_sched sched j x hs
    have m1 := service_mono sched j t x h1
    have m2 := service_mono sched j (x + 1) t' (by omega')
    omega'

/-- LEAN_HELPER: `time_after_last_execution` only depends on the instants at which `j` is scheduled. -/
private theorem tale_eq_of_same {Job : Type u} [DecidableEq Job] (job_arrival : Job → time) (sched : schedule Job)
    (j : Job) (t t' : Nat) (hle : t ≤ t') (H : ∀ x, t ≤ x → x < t' → scheduled_at sched j x = false) :
    time_after_last_execution job_arrival sched j t = time_after_last_execution job_arrival sched j t' := by
  by_cases EX : ∃ x, x < t ∧ scheduled_at sched j x = true
  · have EX' : ∃ x, x < t' ∧ scheduled_at sched j x = true := by
      obtain ⟨x, hx, hs⟩ := EX; exact ⟨x, by omega', hs⟩
    obtain ⟨p1, l1, s1, m1⟩ := (tale_spec job_arrival sched j t).1 EX
    obtain ⟨p2, l2, s2, m2⟩ := (tale_spec job_arrival sched j t').1 EX'
    have a := m2 _ (by omega') s1
    have hlt : time_after_last_execution job_arrival sched j t' - 1 < t := by
      by_contra hc
      have := H (time_after_last_execution job_arrival sched j t' - 1) (by omega') (by omega')
      rw [this] at s2; exact Bool.noConfusion s2
    have b := m1 _ hlt s2
    omega'
  · have EX' : ¬ ∃ x, x < t' ∧ scheduled_at sched j x = true := by
      rintro ⟨x, hx, hs⟩
      by_cases hxt : x < t
      · exact EX ⟨x, hxt, hs⟩
      · rw [H x (by omega') hx] at hs; exact Bool.noConfusion hs
    rw [(tale_spec job_arrival sched j t).2 EX, (tale_spec job_arrival sched j t').2 EX']

theorem same_service_implies_same_last_execution {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (sched : schedule Job) (j : Job) (t t' : time) (H_same_service : service sched j t = service sched j t') :
    time_after_last_execution job_arrival sched j t = time_after_last_execution job_arrival sched j t' := by
  rcases Nat.le_total t t' with h | h
  · exact tale_eq_of_same job_arrival sched j t t' h (same_service_not_scheduled sched j t t' h H_same_service)
  · exact (tale_eq_of_same job_arrival sched j t' t h
      (same_service_not_scheduled sched j t' t h H_same_service.symm)).symm

theorem same_service_since_last_execution {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (j : Job) :
    ∀ t, service sched j (time_after_last_execution job_arrival sched j t) = service sched j t := by
  intro t
  by_cases EX : ∃ x, x < t ∧ scheduled_at sched j x = true
  · obtain ⟨hpos, hle, hs, hmax⟩ := (tale_spec job_arrival sched j t).1 EX
    symm
    apply service_flat sched j _ t hle
    intro x h1 h2
    cases hsx : scheduled_at sched j x
    · rfl
    · have := hmax x h2 hsx; omega'
  · rw [(tale_spec job_arrival sched j t).2 EX]
    have z1 : service sched j t = 0 := by
      have := service_flat sched j 0 t (Nat.zero_le t) (fun x _ hx => by
        cases hs : scheduled_at sched j x
        · rfl
        · exact absurd ⟨x, hx, hs⟩ EX)
      rw [this]; simp [service, service_during]
    have z2 : service sched j (job_arrival j) = 0 := by
      unfold service service_during
      exact cumulative_service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive_to_execute j 0
        (job_arrival j) (Nat.le_refl _)
    rw [z1, z2]

theorem exists_last_execution_with_smaller_service {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (j : Job) (t : time)
    (H_j_has_completed : completed_by job_cost sched j t = true) (s : time) (H_less_than_cost : s < job_cost j) :
    ∃ t0 : time, service sched j (time_after_last_execution job_arrival sched j t0) = s := by
  simp only [completed_by, decide_eq_true_eq] at H_j_has_completed
  obtain ⟨t0, _, h⟩ := exists_intermediate_service sched j t s (by omega')
  exact ⟨t0, by rw [same_service_since_last_execution job_arrival sched H_jobs_must_arrive_to_execute j t0, h]⟩

theorem less_service_before_start_of_suspension {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (sched : schedule Job) (j : Job) (t t0 : time) (H_no_earlier_than_arrival : has_arrived job_arrival j t0 = true)
    (H_before_last_execution : t0 < time_after_last_execution job_arrival sched j t) :
    service sched j t0 < service sched j t := by
  by_cases EX : ∃ x, x < t ∧ scheduled_at sched j x = true
  · obtain ⟨hpos, hle, hs, _⟩ := (tale_spec job_arrival sched j t).1 EX
    have h1 := service_succ_sched sched j _ hs
    have h2 := service_mono sched j t0 (time_after_last_execution job_arrival sched j t - 1) (by omega')
    have h3 := service_mono sched j (time_after_last_execution job_arrival sched j t - 1 + 1) t (by omega')
    omega'
  · rw [(tale_spec job_arrival sched j t).2 EX] at H_before_last_execution
    simp only [has_arrived, decide_eq_true_eq] at H_no_earlier_than_arrival
    omega'

end Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution
