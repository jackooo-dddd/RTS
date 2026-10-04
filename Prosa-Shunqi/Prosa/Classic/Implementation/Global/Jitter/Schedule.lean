-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/global/jitter/schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 152)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Global.Jitter.Platform
import Prosa.Classic.Model.Schedule.Global.Transformation.Construction

/-!
A concrete jitter-aware global scheduler picking the `cpu`-th highest-priority pending job (Rocq module
`ConcreteScheduler` of `classic/implementation/global/jitter/schedule.v`).

Representation notes:
* `[seq j <- s | P j]` is `s.filter P`; MathComp's `sort leT s` is the restated `mc_sort leT s` below; `sorted leT s`
  is `List.IsChain (fun a b => leT a b = true) s`; `nth_or_none` is the accepted `Prosa.Classic.Util.List` one, and a
  processor (an ordinal) used as an index is its value.
* MathComp `total R` is `∀ x y, (R x y || R y x) = true`.
* The section-local `Let`s (`is_pending`, `actual_arrivals`, `empty_schedule`, `sched`, `sorted_jobs`) are unfolded;
  pending jobs are taken among the actual arrivals (`actual_arrivals_up_to`) and `pending`/`backlogged` are the
  jitter-aware ones.
* The proofs follow the translation of the basic scheduler (`Prosa.Classic.Implementation.Global.Basic.Schedule`).
* Binder lists follow the Rocq contract.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Implementation.Global.Jitter.Schedule.ConcreteScheduler

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence.ArrivalSequenceWithJitter
  (actual_arrivals_up_to in_actual_arrivals_between_implies_arrived arrived_between_implies_in_actual_arrivals
   actual_arrivals_uniq actual_arrival_between)
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule hiding pending backlogged
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Util.List (nth_or_none nth_or_none_mem nth_or_none_mem_exists nth_or_none_size_none
  nth_or_none_size_some nth_or_none_uniq nth_or_none_nth)
open Prosa.Classic.Util.Sorting (sorted_lt_idx_implies_rel)

universe u

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### MathComp's `sort`

The Rocq definition sorts with MathComp's `sort` (`path.v`: `merge`, `merge_sort_push`, `merge_sort_pop`,
`merge_sort_rec`) by an arbitrary relation. It is restated here equation for equation (all structurally recursive), so the
translated scheduler is the source one for every relation, not only total and transitive ones. Only the permutation
and the sortedness (under totality and transitivity) facts used below are proved. -/

section MathcompSort
variable {T : Type u} (leT : T → T → Bool)

/-- The inner `merge_s1` of MathComp's `merge` (fixed first list `x1 :: s1'`, recursion on the second). -/
def mc_merge_s1 (x1 : T) (s1' : List T) (rec : List T → List T) : List T → List T
  | [] => x1 :: s1'
  | x2 :: s2' => if leT x1 x2 then x1 :: rec (x2 :: s2') else x2 :: mc_merge_s1 x1 s1' rec s2'

/-- MathComp's `merge` (`path.v`). -/
def mc_merge : List T → List T → List T
  | [] => fun s2 => s2
  | x1 :: s1' => mc_merge_s1 leT x1 s1' (mc_merge s1')

/-- MathComp's `merge_sort_push`. -/
def mc_merge_sort_push (s1 : List T) : List (List T) → List (List T)
  | [] => [s1]
  | [] :: ss' => s1 :: ss'
  | (x :: s2) :: ss' => [] :: mc_merge_sort_push (mc_merge leT (x :: s2) s1) ss'

/-- MathComp's `merge_sort_pop`. -/
def mc_merge_sort_pop (s1 : List T) : List (List T) → List T
  | [] => s1
  | s2 :: ss' => mc_merge_sort_pop (mc_merge leT s2 s1) ss'

/-- MathComp's `merge_sort_rec`. -/
def mc_merge_sort_rec (ss : List (List T)) : List T → List T
  | x1 :: x2 :: s' => mc_merge_sort_rec (mc_merge_sort_push leT (if leT x1 x2 then [x1, x2] else [x2, x1]) ss) s'
  | s => mc_merge_sort_pop leT s ss

/-- MathComp's `sort`. -/
def mc_sort (s : List T) : List T := mc_merge_sort_rec leT [] s

theorem mc_merge_perm : ∀ s1 s2 : List T, (mc_merge leT s1 s2).Perm (s1 ++ s2)
  | [], s2 => by simp [mc_merge]
  | x1 :: s1', s2 => by
    induction s2 with
    | nil => simp [mc_merge, mc_merge_s1]
    | cons x2 s2' ih =>
      simp only [mc_merge, mc_merge_s1] at ih ⊢
      split
      · exact List.Perm.cons _ (mc_merge_perm s1' (x2 :: s2'))
      · refine (List.Perm.cons _ ih).trans ?_
        exact (List.perm_middle).symm

theorem mc_merge_sort_push_perm : ∀ (s1 : List T) (ss : List (List T)),
    (mc_merge_sort_push leT s1 ss).flatten.Perm (s1 ++ ss.flatten)
  | s1, [] => by simp [mc_merge_sort_push]
  | s1, [] :: ss' => by simp [mc_merge_sort_push]
  | s1, (x :: s2) :: ss' => by
    simp only [mc_merge_sort_push, List.flatten_cons, List.nil_append]
    refine (mc_merge_sort_push_perm _ ss').trans ?_
    refine ((mc_merge_perm leT _ _).append_right _).trans ?_
    rw [← List.append_assoc]
    exact (List.perm_append_comm.append_right _)

theorem mc_merge_sort_pop_perm : ∀ (s1 : List T) (ss : List (List T)),
    (mc_merge_sort_pop leT s1 ss).Perm (s1 ++ ss.flatten)
  | s1, [] => by simp [mc_merge_sort_pop]
  | s1, s2 :: ss' => by
    simp only [mc_merge_sort_pop, List.flatten_cons]
    refine (mc_merge_sort_pop_perm _ ss').trans ?_
    refine ((mc_merge_perm leT _ _).append_right _).trans ?_
    rw [← List.append_assoc]
    exact (List.perm_append_comm.append_right _)

theorem mc_merge_sort_rec_perm : ∀ (ss : List (List T)) (s : List T),
    (mc_merge_sort_rec leT ss s).Perm (s ++ ss.flatten)
  | ss, [] => by simpa [mc_merge_sort_rec] using mc_merge_sort_pop_perm leT [] ss
  | ss, [x] => by simpa [mc_merge_sort_rec] using mc_merge_sort_pop_perm leT [x] ss
  | ss, x1 :: x2 :: s' => by
    simp only [mc_merge_sort_rec]
    refine (mc_merge_sort_rec_perm _ s').trans ?_
    refine ((mc_merge_sort_push_perm leT _ ss).append_left _).trans ?_
    have h2 : (if leT x1 x2 then [x1, x2] else [x2, x1]).Perm [x1, x2] := by
      split
      · exact List.Perm.refl _
      · exact List.Perm.swap _ _ _
    refine (List.perm_append_comm.trans ?_)
    rw [List.append_assoc]
    refine (h2.append_right _).trans ?_
    simp only [List.cons_append, List.nil_append]
    exact List.Perm.cons _ (List.Perm.cons _ (List.perm_append_comm))

theorem mc_sort_perm (s : List T) : (mc_sort leT s).Perm s := by
  simpa [mc_sort] using mc_merge_sort_rec_perm leT [] s

theorem mem_mc_sort {x : T} {s : List T} : x ∈ mc_sort leT s ↔ x ∈ s := (mc_sort_perm leT s).mem_iff

section Sorted
variable {leT}
variable (trans : ∀ a b c, leT a b = true → leT b c = true → leT a c = true)
  (total : ∀ a b, (leT a b || leT b a) = true)
include trans total

theorem mc_merge_pairwise : ∀ s1 s2 : List T, s1.Pairwise (fun a b => leT a b = true) →
    s2.Pairwise (fun a b => leT a b = true) → (mc_merge leT s1 s2).Pairwise (fun a b => leT a b = true)
  | [], s2, _, h2 => by simpa [mc_merge] using h2
  | x1 :: s1', s2, h1, h2 => by
    induction s2 with
    | nil => simpa [mc_merge, mc_merge_s1] using h1
    | cons x2 s2' ih =>
      have h2' := List.pairwise_cons.mp h2
      have h1' := List.pairwise_cons.mp h1
      simp only [mc_merge, mc_merge_s1] at ih ⊢
      split
      · rename_i hle
        refine List.pairwise_cons.mpr ⟨?_, mc_merge_pairwise s1' (x2 :: s2') h1'.2 h2⟩
        intro y hy
        rcases List.mem_append.mp ((mc_merge_perm leT s1' (x2 :: s2')).mem_iff.mp hy) with hy | hy
        · exact h1'.1 y hy
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact hle
          · exact trans _ _ _ hle (h2'.1 y hy)
      · rename_i hle
        have hle' : leT x2 x1 = true := by have := total x1 x2; simp_all
        refine List.pairwise_cons.mpr ⟨?_, ih h2'.2⟩
        intro y hy
        have hy' := (mc_merge_perm leT (x1 :: s1') s2').mem_iff.mp (by simpa [mc_merge] using hy)
        rcases List.mem_append.mp hy' with hy | hy
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact hle'
          · exact trans _ _ _ hle' (h1'.1 y hy)
        · exact h2'.1 y hy

theorem mc_merge_sort_push_pairwise : ∀ (s1 : List T) (ss : List (List T)),
    s1.Pairwise (fun a b => leT a b = true) → (∀ s ∈ ss, s.Pairwise (fun a b => leT a b = true)) →
    ∀ s ∈ mc_merge_sort_push leT s1 ss, s.Pairwise (fun a b => leT a b = true)
  | s1, [], h1, _ => by simpa [mc_merge_sort_push] using h1
  | s1, [] :: ss', h1, hss => by
    intro s hs
    simp only [mc_merge_sort_push, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact h1
    · exact hss s (List.mem_cons_of_mem _ hs)
  | s1, (x :: s2) :: ss', h1, hss => by
    intro s hs
    simp only [mc_merge_sort_push, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact List.Pairwise.nil
    · exact mc_merge_sort_push_pairwise _ ss'
        (mc_merge_pairwise trans total _ _ (hss _ List.mem_cons_self) h1)
        (fun s hs => hss s (List.mem_cons_of_mem _ hs)) s hs

theorem mc_merge_sort_pop_pairwise : ∀ (s1 : List T) (ss : List (List T)),
    s1.Pairwise (fun a b => leT a b = true) → (∀ s ∈ ss, s.Pairwise (fun a b => leT a b = true)) →
    (mc_merge_sort_pop leT s1 ss).Pairwise (fun a b => leT a b = true)
  | s1, [], h1, _ => by simpa [mc_merge_sort_pop] using h1
  | s1, s2 :: ss', h1, hss => by
    simp only [mc_merge_sort_pop]
    exact mc_merge_sort_pop_pairwise _ ss'
      (mc_merge_pairwise trans total _ _ (hss _ List.mem_cons_self) h1)
      (fun s hs => hss s (List.mem_cons_of_mem _ hs))

theorem mc_merge_sort_rec_pairwise : ∀ (ss : List (List T)) (s : List T),
    (∀ s ∈ ss, s.Pairwise (fun a b => leT a b = true)) →
    (mc_merge_sort_rec leT ss s).Pairwise (fun a b => leT a b = true)
  | ss, [], hss => by simpa [mc_merge_sort_rec] using mc_merge_sort_pop_pairwise trans total [] ss List.Pairwise.nil hss
  | ss, [x], hss => by
    simpa [mc_merge_sort_rec] using mc_merge_sort_pop_pairwise trans total [x] ss (List.pairwise_singleton _ _) hss
  | ss, x1 :: x2 :: s', hss => by
    simp only [mc_merge_sort_rec]
    refine mc_merge_sort_rec_pairwise _ s' (mc_merge_sort_push_pairwise trans total _ ss ?_ hss)
    split
    · rename_i h; simp [h]
    · rename_i h
      have h' : leT x2 x1 = true := by have := total x1 x2; simp_all
      simp [h']

theorem pairwise_mc_sort (s : List T) : (mc_sort leT s).Pairwise (fun a b => leT a b = true) :=
  mc_merge_sort_rec_pairwise trans total [] s (by simp)

end Sorted
end MathcompSort

/-! ### Implementation -/

def pending_jobs {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job)
    (sched_prefix : schedule Job num_cpus) (t : time) : List Job :=
  (actual_arrivals_up_to job_arrival job_jitter arr_seq t).filter
    (fun j => pending job_arrival job_cost job_jitter sched_prefix j t)

def sorted_pending_jobs {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job)
    (sched_prefix : schedule Job num_cpus) (t : time) : List Job :=
  mc_sort (higher_eq_priority t) (pending_jobs job_arrival job_cost job_jitter num_cpus arr_seq sched_prefix t)

def nth_highest_priority_job {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job)
    (sched_prefix : schedule Job num_cpus) (cpu : processor num_cpus) (t : time) : Option Job :=
  nth_or_none (sorted_pending_jobs job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority sched_prefix t) cpu

def scheduler {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) : schedule Job num_cpus :=
  build_schedule_from_prefixes num_cpus (nth_highest_priority_job job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) (fun _ _ => none)

theorem scheduler_depends_only_on_prefix {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) :
    ∀ (sched1 sched2 : schedule Job num_cpus) (cpu : processor num_cpus) (t : Nat),
      (∀ t0 cpu0, t0 < t → sched1 cpu0 t0 = sched2 cpu0 t0) →
      nth_highest_priority_job job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority sched1 cpu t =
        nth_highest_priority_job job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority sched2 cpu t := by
  intro sched1 sched2 cpu t ALL
  have SERV : ∀ j, service sched1 j t = service sched2 j t := by
    intro j
    unfold service
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    unfold service_at scheduled_on
    simp only [ALL i _ hi.2]
  unfold nth_highest_priority_job sorted_pending_jobs pending_jobs
  simp only [pending, completed, SERV]

theorem scheduler_uses_construction_function {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) :
    ∀ t cpu, (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) cpu t = nth_highest_priority_job job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) cpu t := by
  intro t cpu
  exact prefix_dependent_schedule_construction num_cpus _ _
    (scheduler_depends_only_on_prefix job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) cpu t

/-! ### Helper lemmas -/

theorem scheduler_nth_or_none_mapping {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) :
    ∀ t cpu, (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) cpu t = nth_or_none (sorted_pending_jobs job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) t) cpu := by
  intro t cpu
  rw [scheduler_uses_construction_function]
  rfl

/-- LEAN_HELPER: the jobs being scheduled have no duplicates. -/
private theorem sorted_pending_jobs_uniq {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (higher_eq_priority : JLDP_policy Job)
    (sched : schedule Job num_cpus) (t : time) :
    (sorted_pending_jobs job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority sched t).Nodup := by
  unfold sorted_pending_jobs pending_jobs
  apply (mc_sort_perm _ _).nodup_iff.mpr
  apply List.Nodup.filter
  exact actual_arrivals_uniq job_arrival job_jitter arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set
    0 (t + 1)

/-- LEAN_HELPER: a job mapped to some processor is a pending job. -/
private theorem mapped_pending {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (j : Job) (cpu : processor num_cpus)
    (t : time) (SCHED : (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) cpu t = some j) :
    j ∈ (actual_arrivals_up_to job_arrival job_jitter arr_seq t) ∧ pending job_arrival job_cost job_jitter (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) j t = true := by
  rw [scheduler_nth_or_none_mapping] at SCHED
  have := nth_or_none_mem _ _ _ SCHED
  unfold sorted_pending_jobs pending_jobs at this
  rw [mem_mc_sort, List.mem_filter] at this
  exact this

theorem scheduler_nth_or_none_backlogged {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) :
    ∀ j t, arrives_in arr_seq j → backlogged job_arrival job_cost job_jitter (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) j t = true →
      ∃ i, nth_or_none (sorted_pending_jobs job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) t) i = some j ∧ num_cpus ≤ i := by
  intro j t ARRj BACK
  simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true'] at BACK
  obtain ⟨PENDING, NOTSCHED⟩ := BACK
  have IN : j ∈ sorted_pending_jobs job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) t := by
    unfold sorted_pending_jobs pending_jobs
    rw [mem_mc_sort, List.mem_filter]
    refine ⟨?_, PENDING⟩
    have ARR := PENDING
    simp only [pending, Bool.and_eq_true] at ARR
    have A1 : job_arrival j + job_jitter j ≤ t := by
      have h := ARR.1
      unfold jitter_has_passed actual_arrival at h
      exact of_decide_eq_true h
    exact arrived_between_implies_in_actual_arrivals job_arrival job_jitter arr_seq H_arrival_times_are_consistent j 0
      (t + 1) ARRj
      (by
        unfold actual_arrival_between Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence.ArrivalSequenceWithJitter.actual_arrival
        rw [Bool.and_eq_true]
        exact ⟨decide_eq_true (Nat.zero_le _), decide_eq_true (by omega')⟩)
  obtain ⟨n, SOME⟩ := nth_or_none_mem_exists _ j IN
  refine ⟨n, SOME, ?_⟩
  by_contra LT
  have LT' : n < num_cpus := by omega
  have SCHED : (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) ⟨n, LT'⟩ t = some j := by
    rw [scheduler_nth_or_none_mapping]; exact SOME
  have : scheduled (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) j t = true :=
    List.any_eq_true.mpr ⟨⟨n, LT'⟩, List.mem_finRange _, by simp [scheduled_on, SCHED]⟩
  rw [NOTSCHED] at this; exact absurd this (by simp)

/-! ### Properties of the scheduler -/

theorem scheduler_jobs_come_from_arrival_sequence {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) :
    jobs_come_from_arrival_sequence (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) arr_seq := by
  intro j t SCHED
  obtain ⟨cpu, _, S⟩ := List.any_eq_true.mp SCHED
  simp only [scheduled_on, decide_eq_true_eq] at S
  exact in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq j 0 (t + 1) (mapped_pending job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority j cpu t S).1

theorem scheduler_jobs_execute_after_jitter {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) :
    jobs_execute_after_jitter job_arrival job_jitter (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) := by
  intro j t SCHED
  obtain ⟨cpu, _, S⟩ := List.any_eq_true.mp SCHED
  simp only [scheduled_on, decide_eq_true_eq] at S
  have PEND := (mapped_pending job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority j cpu t S).2
  simp only [pending, Bool.and_eq_true] at PEND
  exact PEND.1

theorem scheduler_sequential_jobs {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (higher_eq_priority : JLDP_policy Job) :
    sequential_jobs (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) := by
  intro j t cpu1 cpu2 SCHED1 SCHED2
  rw [scheduler_nth_or_none_mapping] at SCHED1 SCHED2
  exact Fin.ext (nth_or_none_uniq _ _ _ j
    (sorted_pending_jobs_uniq job_arrival job_cost job_jitter num_cpus arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority _ t)
    SCHED1 SCHED2)

theorem scheduler_completed_jobs_dont_execute {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (higher_eq_priority : JLDP_policy Job) :
    completed_jobs_dont_execute job_cost (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) := by
  have SEQ := scheduler_sequential_jobs job_arrival job_cost job_jitter num_cpus arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set
    higher_eq_priority
  intro j t
  induction t with
  | zero => simp [service]
  | succ t IHt =>
    have STEP : service (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) j (t + 1) = service (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) j t + service_at (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) j t := by
      unfold service
      rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]
    rw [STEP]
    rcases Nat.lt_or_ge (service (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) j t) (job_cost j) with LT | GE
    · have := service_at_most_one (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) j SEQ t
      omega'
    · have ZERO : service_at (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) j t = 0 := by
        unfold service_at
        apply Finset.sum_eq_zero
        intro cpu hcpu
        exfalso
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, scheduled_on, decide_eq_true_eq] at hcpu
        have PEND := (mapped_pending job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority j cpu t hcpu).2
        simp only [pending, completed, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at PEND
        exact PEND.2 GE
      rw [ZERO, Nat.add_zero]; exact IHt

theorem scheduler_work_conserving {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job) :
    work_conserving job_arrival job_cost job_jitter arr_seq (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) := by
  intro j t ARRj BACK cpu
  cases SCHED : (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) cpu t with
  | some j0 => exact ⟨j0, by simp [scheduled_on, SCHED]⟩
  | none =>
    exfalso
    obtain ⟨cpu_out, NTH, GE⟩ := scheduler_nth_or_none_backlogged job_arrival job_cost job_jitter num_cpus arr_seq H_arrival_times_are_consistent
      higher_eq_priority j t ARRj BACK
    rw [scheduler_nth_or_none_mapping] at SCHED
    have S1 := (nth_or_none_size_none _ _).mp SCHED
    have S2 := nth_or_none_size_some _ _ _ NTH
    have := cpu.isLt
    omega

theorem scheduler_respects_policy {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time) (num_cpus : Nat) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (higher_eq_priority : JLDP_policy Job)
    (H_priority_transitive : JLDP_is_transitive higher_eq_priority)
    (H_priority_total : ∀ t, ∀ x y, (higher_eq_priority t x y || higher_eq_priority t y x) = true) :
    respects_JLDP_policy job_arrival job_cost job_jitter arr_seq (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) higher_eq_priority := by
  intro j j_hp t ARRj BACK SCHED
  obtain ⟨cpu, _, S⟩ := List.any_eq_true.mp SCHED
  simp only [scheduled_on, decide_eq_true_eq] at S
  obtain ⟨cpu_out, SOME, GE⟩ := scheduler_nth_or_none_backlogged job_arrival job_cost job_jitter num_cpus arr_seq H_arrival_times_are_consistent
    higher_eq_priority j t ARRj BACK
  rw [scheduler_nth_or_none_mapping] at S
  have EQ1 := nth_or_none_nth _ _ j_hp j S
  have EQ2 := nth_or_none_nth _ _ j j SOME
  have REL := sorted_lt_idx_implies_rel Job (higher_eq_priority t)
    (sorted_pending_jobs job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority
      (scheduler job_arrival job_cost job_jitter num_cpus arr_seq higher_eq_priority) t) j (H_priority_transitive t) cpu cpu_out
    ((pairwise_mc_sort (fun a b c h1 h2 => H_priority_transitive t b a c h1 h2) (H_priority_total t)
      _).isChain)
    (by have := cpu.isLt; omega) (nth_or_none_size_some _ _ _ SOME)
  rw [EQ1, EQ2] at REL
  exact REL

end Prosa.Classic.Implementation.Global.Jitter.Schedule.ConcreteScheduler
