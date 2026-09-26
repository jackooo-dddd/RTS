-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/sporadic/arrival_bound.v

import Prosa.Util.All
import Prosa.Model.Task.Arrival.Sporadic
import Prosa.Analysis.Facts.Model.TaskArrivals

namespace Prosa.Analysis.Facts.Sporadic.ArrivalBound

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Sporadic
open Prosa.Util.Div_mod
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.TaskArrivals

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration] at *) <;> omega)

/-! Representation notes: `nth dummy s i` is `s.getD i dummy` (as in the
accepted task-arrival facts); `n.-1` is `n - 1`; `n >= 2` is `1 < n` (the
elaborated form); the Boolean `valid_task_min_inter_arrival_time` hypothesis
is `= true`. -/

/-- The classic `⌈Δ / T⌉` bound on sporadic arrivals. -/
def max_sporadic_arrivals {Task : TaskType} [DecidableEq Task] [SporadicModel Task]
    (tsk : Task) (delta : duration) : Nat :=
  div_ceil delta (task_min_inter_arrival_time tsk)

theorem arrival_of_nth_job {Task : TaskType} [DecidableEq Task] [SporadicModel Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, respects_sporadic_task_model arr_seq tsk →
        valid_task_min_inter_arrival_time tsk = true →
          ∀ (dummy : Job) (t1 t2 : instant) (n i : Nat) (j : Job),
            n = number_of_task_arrivals arr_seq tsk t1 t2 → i < n →
              j = (task_arrivals_between arr_seq tsk t1 t2).getD i dummy →
                t1 + task_min_inter_arrival_time tsk * i ≤ job_arrival j := by
  intro hvalid tsk hspor _ dummy t1 t2 n i j hn hi hj
  obtain ⟨hc, hu⟩ := hvalid
  subst hn hj
  unfold number_of_task_arrivals at hi
  set s := task_arrivals_between arr_seq tsk t1 t2 with hs
  have hnodup : s.Nodup := task_arrivals_between_uniq arr_seq hc tsk t1 t2 hu
  have hsorted := task_arrivals_between_sorted arr_seq hc tsk t1 t2
  rw [← hs] at hsorted
  have hmem : ∀ k (hk : k < s.length), decide (s[k] ∈ s) = true :=
    fun k hk => decide_eq_true (List.getElem_mem hk)
  induction i with
  | zero =>
      rw [List.getD_eq_getElem _ _ hi, Nat.mul_zero, Nat.add_zero]
      exact job_arrival_between_ge arr_seq hc _ t1 t2
        (task_arrivals_between_subset arr_seq tsk t1 t2 _ (hmem 0 hi))
  | succ i ih =>
      have hi' : i < s.length := Nat.lt_of_succ_lt hi
      have ih' := ih hi'
      rw [List.getD_eq_getElem _ _ hi'] at ih'
      rw [List.getD_eq_getElem _ _ hi]
      have hne : s[i] ≠ s[i + 1] := by
        intro h
        exact absurd ((List.Nodup.getElem_inj_iff hnodup).1 h) (by omega')
      have hord : by_arrival_times s[i] s[i + 1] = true := List.IsChain.getElem hsorted i hi
      simp only [by_arrival_times, decide_eq_true_eq] at hord
      have hsep := hspor s[i] s[i + 1] hne
        (arrives_in_task_arrivals_implies_arrived arr_seq tsk t1 t2 _ (hmem i hi'))
        (arrives_in_task_arrivals_implies_arrived arr_seq tsk t1 t2 _ (hmem (i + 1) hi))
        (in_task_arrivals_between_implies_job_of_task arr_seq tsk t1 t2 _ (hmem i hi'))
        (in_task_arrivals_between_implies_job_of_task arr_seq tsk t1 t2 _ (hmem (i + 1) hi))
        hord
      rw [Nat.mul_succ]
      omega'

theorem minimum_distance_for_n_sporadic_arrivals {Task : TaskType} [DecidableEq Task]
    [SporadicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, respects_sporadic_task_model arr_seq tsk →
        valid_task_min_inter_arrival_time tsk = true →
          ∀ (t1 t2 : instant) (n : Nat),
            number_of_task_arrivals arr_seq tsk t1 t2 = n → 1 < n →
              t1 + task_min_inter_arrival_time tsk * (n - 1) < t2 := by
  intro hvalid tsk hspor hT t1 t2 n hn hmany
  have hlen : (task_arrivals_between arr_seq tsk t1 t2).length = n := hn
  have hlast : n - 1 < (task_arrivals_between arr_seq tsk t1 t2).length := by omega'
  have hmem : decide ((task_arrivals_between arr_seq tsk t1 t2)[n - 1] ∈
      task_arrivals_between arr_seq tsk t1 t2) = true := decide_eq_true (List.getElem_mem hlast)
  have hlt := job_arrival_between_lt arr_seq hvalid.1 _ t1 t2
    (task_arrivals_between_subset arr_seq tsk t1 t2 _ hmem)
  have hdist := arrival_of_nth_job arr_seq hvalid tsk hspor hT
    (task_arrivals_between arr_seq tsk t1 t2)[n - 1] t1 t2 n (n - 1) _ hn.symm (by omega')
    (List.getD_eq_getElem _ _ hlast).symm
  omega'

theorem sporadic_task_arrivals_bound {Task : TaskType} [DecidableEq Task] [SporadicModel Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, respects_sporadic_task_model arr_seq tsk →
        valid_task_min_inter_arrival_time tsk = true →
          ∀ t1 t2 : instant,
            number_of_task_arrivals arr_seq tsk t1 t2 ≤ max_sporadic_arrivals tsk (t2 - t1) := by
  intro hvalid tsk hspor hT t1 t2
  have hTpos : 0 < task_min_inter_arrival_time tsk := of_decide_eq_true hT
  unfold max_sporadic_arrivals
  rcases Nat.lt_or_ge (number_of_task_arrivals arr_seq tsk t1 t2) 2 with h | h
  · rcases Nat.lt_or_ge (number_of_task_arrivals arr_seq tsk t1 t2) 1 with h0 | h1
    · omega'
    · have hlt := number_of_task_arrivals_nonzero arr_seq tsk t1 t2 (by omega')
      have := div_ceil_gt0 (t2 - t1) (task_min_inter_arrival_time tsk) (by omega') hTpos
      omega'
  · have hsep := minimum_distance_for_n_sporadic_arrivals arr_seq hvalid tsk hspor hT t1 t2
      _ rfl (by omega')
    have := div_ceil_multiple (t2 - t1) (task_min_inter_arrival_time tsk)
      (number_of_task_arrivals arr_seq tsk t1 t2 - 1) hTpos (by omega')
    omega'

end Prosa.Analysis.Facts.Sporadic.ArrivalBound
