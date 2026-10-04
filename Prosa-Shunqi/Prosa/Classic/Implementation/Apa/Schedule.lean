-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/apa/schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 134)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Model.Schedule.Apa.Platform
import Prosa.Classic.Model.Schedule.Global.Transformation.Construction

/-!
A concrete weak-APA scheduler (Rocq module `ConcreteScheduler` of `classic/implementation/apa/schedule.v`).

Representation notes:
* `[seq j <- s | P j]` is `s.filter P`; MathComp's `sort leT s` is the restated `mc_sort leT s` below; `sorted leT s`
  is `List.IsChain (fun a b => leT a b = true) s` (as in the accepted `Prosa.Classic.Util.Sorting`); `uniq s` in
  proposition position is `s.Nodup`; `unzip1` is `List.map Prod.fst`; `x \notin s` is `x ∉ s`.
* `enum (processor num_cpus)` is `List.finRange num_cpus`; `nseq n x` is `List.replicate n x`; `foldl`, `zip`,
  `replace_first`, `set_pair_2nd` and `pairs_to_function` are the list functions of the accepted
  `Prosa.Classic.Util.List`; `let '(cpu, mapped_job) := p in if mapped_job is Some j' then … else …` is a `match`.
* MathComp `total R` is `∀ x y, (R x y || R y x) = true`.
* The section-local `Let`s (`is_pending`, `actual_arrivals`, `empty_mapping`, `empty_schedule`, `sched`,
  `schedule_jobs`, `schedule_pending_jobs`) are unfolded.
* Binder lists follow the Rocq contract.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Implementation.Apa.Schedule.ConcreteScheduler

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity
open Prosa.Classic.Model.Schedule.Apa.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Util.List (replace_first set_pair_2nd pairs_to_function replace_first_cases replace_first_new
  replace_first_previous replace_first_failed pairs_to_function_neq_default pairs_to_function_mem mem_zip_nseq_r)
open Prosa.Classic.Util.Sorting (sorted_rcons_prefix order_sorted_rcons)

universe u v

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

def pending_jobs {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time) (num_cpus : Nat)
    (arr_seq : arrival_sequence Job) (sched_prefix : schedule Job num_cpus) (t : time) : List Job :=
  (jobs_arrived_up_to arr_seq t).filter (fun j => pending job_arrival job_cost sched_prefix j t)

def sorted_pending_jobs {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time) (num_cpus : Nat)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (sched_prefix : schedule Job num_cpus)
    (t : time) : List Job :=
  mc_sort (higher_eq_priority t) (pending_jobs job_arrival job_cost num_cpus arr_seq sched_prefix t)

def should_be_scheduled {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_task : Job → sporadic_task) (num_cpus : Nat) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) (t : time) (j : Job) (p : processor num_cpus × Option Job) : Bool :=
  match p with
  | (cpu, some j') => can_execute_on alpha (job_task j) cpu && !higher_eq_priority t j' j
  | (cpu, none) => can_execute_on alpha (job_task j) cpu

def update_available_cpu {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_task : Job → sporadic_task) (num_cpus : Nat) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) (t : time) (allocation : List (processor num_cpus × Option Job)) (j : Job) :
    List (processor num_cpus × Option Job) :=
  replace_first (should_be_scheduled job_task num_cpus alpha higher_eq_priority t j) (set_pair_2nd (some j)) allocation

def schedule_jobs_from_list {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_task : Job → sporadic_task) (num_cpus : Nat) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) (t : time) (l : List Job) : List (processor num_cpus × Option Job) :=
  l.foldl (update_available_cpu job_task num_cpus alpha higher_eq_priority t) ((List.finRange num_cpus).zip (List.replicate num_cpus none))

def apa_schedule {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (arr_seq : arrival_sequence Job) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) (sched_prefix : schedule Job num_cpus) (cpu : processor num_cpus)
    (t : time) : Option Job :=
  pairs_to_function none
    (schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t (sorted_pending_jobs job_arrival job_cost num_cpus arr_seq higher_eq_priority sched_prefix t)) cpu

def scheduler {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (arr_seq : arrival_sequence Job) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) : schedule Job num_cpus :=
  build_schedule_from_prefixes num_cpus
    (apa_schedule job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) (fun _ _ => none)

theorem scheduler_depends_only_on_prefix {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (num_cpus : Nat) (arr_seq : arrival_sequence Job) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) :
    ∀ (sched1 sched2 : schedule Job num_cpus) (cpu : processor num_cpus) (t : Nat),
      (∀ t0 cpu0, t0 < t → sched1 cpu0 t0 = sched2 cpu0 t0) →
      apa_schedule job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority sched1 cpu t =
        apa_schedule job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority sched2 cpu t := by
  intro sched1 sched2 cpu t ALL
  have SERV : ∀ j, service sched1 j t = service sched2 j t := by
    intro j
    unfold service
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    unfold service_at scheduled_on
    simp only [ALL i _ hi.2]
  unfold apa_schedule sorted_pending_jobs pending_jobs
  simp only [pending, completed, SERV]

theorem scheduler_uses_construction_function {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (num_cpus : Nat) (arr_seq : arrival_sequence Job)
    (alpha : task_affinity sporadic_task num_cpus) (higher_eq_priority : JLDP_policy Job) :
    ∀ t cpu, (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) cpu t =
      apa_schedule job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) cpu t := by
  intro t cpu
  exact prefix_dependent_schedule_construction num_cpus _ _
    (scheduler_depends_only_on_prefix job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) cpu t

/-! ### Helper lemmas -/

/-- LEAN_HELPER: one step of the construction. -/
private theorem schedule_jobs_rcons {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_task : Job → sporadic_task) (num_cpus : Nat) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) (t : time) (l : List Job) (x : Job) :
    schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t (l ++ [x]) =
      replace_first (should_be_scheduled job_task num_cpus alpha higher_eq_priority t x) (set_pair_2nd (some x)) (schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l) := by
  simp [schedule_jobs_from_list, List.foldl_append, update_available_cpu]

/-- LEAN_HELPER: replacing a second component keeps the first components. -/
private theorem map_fst_replace_first {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (P : α × β → Bool) (y : β) (L : List (α × β)) :
    (replace_first P (set_pair_2nd y) L).map Prod.fst = L.map Prod.fst := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    unfold replace_first
    split <;> simp [set_pair_2nd, ih]

theorem scheduler_uniq_cpus {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_task : Job → sporadic_task) (num_cpus : Nat) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) (t : time) (l : List Job) :
    (List.map Prod.fst (schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l)).Nodup := by
  induction l using List.reverseRecOn with
  | nil =>
    simp only [schedule_jobs_from_list, List.foldl_nil]
    rw [List.map_fst_zip (by simp)]
    exact List.nodup_finRange num_cpus
  | append_singleton l x ih =>
    rw [schedule_jobs_rcons, map_fst_replace_first]
    exact ih

theorem scheduler_job_in_mapping {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_task : Job → sporadic_task) (num_cpus : Nat) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) :
    ∀ (l : List Job) (j : Job) (t : time) (cpu : processor num_cpus), (cpu, some j) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l → j ∈ l := by
  intro l j t cpu SOME
  induction l using List.reverseRecOn with
  | nil =>
    simp only [schedule_jobs_from_list, List.foldl_nil] at SOME
    have := (List.of_mem_zip SOME).2
    simp [List.mem_replicate] at this
  | append_singleton l x ih =>
    rw [schedule_jobs_rcons] at SOME
    rcases replace_first_cases SOME with IN | ⟨y, EQ, _, _⟩
    · exact List.mem_append_left _ (ih IN)
    · simp only [set_pair_2nd, Prod.mk.injEq, Option.some.injEq] at EQ
      rw [EQ.2]; exact List.mem_append_right _ (List.mem_singleton_self x)

/-- LEAN_HELPER: every mapped job may execute on its processor. -/
private theorem mapping_respects_affinity_any {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_task : Job → sporadic_task) (num_cpus : Nat) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) (t : time) :
    ∀ (l : List Job) (j : Job) (cpu : processor num_cpus), (cpu, some j) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l →
      can_execute_on alpha (job_task j) cpu = true := by
  intro l j cpu SOME
  induction l using List.reverseRecOn with
  | nil =>
    simp only [schedule_jobs_from_list, List.foldl_nil] at SOME
    have := (List.of_mem_zip SOME).2
    simp [List.mem_replicate] at this
  | append_singleton l x ih =>
    rw [schedule_jobs_rcons] at SOME
    rcases replace_first_cases SOME with IN | ⟨⟨c, y⟩, EQ, SHOULD, _⟩
    · exact ih IN
    · simp only [set_pair_2nd, Prod.mk.injEq, Option.some.injEq] at EQ
      obtain ⟨rfl, rfl⟩ := EQ
      cases y with
      | none => exact SHOULD
      | some j' =>
        simp only [should_be_scheduled, Bool.and_eq_true] at SHOULD
        exact SHOULD.1

theorem scheduler_mapping_respects_affinity {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (alpha : task_affinity sporadic_task num_cpus) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) :
    ∀ (j : Job) (t : time) (cpu : processor num_cpus), (cpu, some j) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t (sorted_pending_jobs job_arrival job_cost num_cpus arr_seq higher_eq_priority (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) t) →
      can_execute_on alpha (job_task j) cpu = true := by
  intro j t cpu SOME
  exact mapping_respects_affinity_any job_task num_cpus alpha higher_eq_priority t _ j cpu SOME

/-- LEAN_HELPER: the list of pending jobs being scheduled has no duplicates. -/
private theorem sorted_pending_jobs_uniq {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time) (num_cpus : Nat)
    (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (higher_eq_priority : JLDP_policy Job) (sched : schedule Job num_cpus) (t : time) :
    (sorted_pending_jobs job_arrival job_cost num_cpus arr_seq higher_eq_priority sched t).Nodup := by
  unfold sorted_pending_jobs pending_jobs
  apply (mc_sort_perm _ _).nodup_iff.mpr
  apply List.Nodup.filter
  exact arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set 0 (t + 1)

/-- LEAN_HELPER: no job is mapped to two processors (for any duplicate-free list). -/
private theorem no_duplicate_jobs_any {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_task : Job → sporadic_task) (num_cpus : Nat) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) (t : time) :
    ∀ (l : List Job), l.Nodup → ∀ (j : Job) (cpu1 cpu2 : processor num_cpus),
      (cpu1, some j) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l → (cpu2, some j) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l → cpu1 = cpu2 := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro _ j cpu1 cpu2 SOME1 _
    simp only [schedule_jobs_from_list, List.foldl_nil] at SOME1
    have := (List.of_mem_zip SOME1).2
    simp [List.mem_replicate] at this
  | append_singleton l x ih =>
    intro UNIQ j cpu1 cpu2 SOME1 SOME2
    rw [List.nodup_append] at UNIQ
    obtain ⟨UNIQl, _, DISJ⟩ := UNIQ
    have NOTIN : x ∉ l := fun h => DISJ x h x (List.mem_singleton_self x) rfl
    rw [schedule_jobs_rcons] at SOME1 SOME2
    by_cases EQ : j = x
    · subst EQ
      have N1 : (cpu1, some j) ∉ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l := fun h => NOTIN (scheduler_job_in_mapping job_task num_cpus alpha higher_eq_priority l j t cpu1 h)
      have N2 : (cpu2, some j) ∉ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l := fun h => NOTIN (scheduler_job_in_mapping job_task num_cpus alpha higher_eq_priority l j t cpu2 h)
      have := replace_first_new _ _ _ _ _ N1 N2 SOME1 SOME2
      simp only [Prod.mk.injEq] at this
      exact this.1
    · have P1 : (cpu1, some j) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l := by
        rcases replace_first_cases SOME1 with IN | ⟨y, E, _, _⟩
        · exact IN
        · simp only [set_pair_2nd, Prod.mk.injEq, Option.some.injEq] at E; exact absurd E.2 EQ
      have P2 : (cpu2, some j) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l := by
        rcases replace_first_cases SOME2 with IN | ⟨y, E, _, _⟩
        · exact IN
        · simp only [set_pair_2nd, Prod.mk.injEq, Option.some.injEq] at E; exact absurd E.2 EQ
      exact ih UNIQl j cpu1 cpu2 P1 P2

theorem scheduler_has_no_duplicate_jobs {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (alpha : task_affinity sporadic_task num_cpus) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (higher_eq_priority : JLDP_policy Job) :
    ∀ (j : Job) (t : time) (cpu1 cpu2 : processor num_cpus),
      (cpu1, some j) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t (sorted_pending_jobs job_arrival job_cost num_cpus arr_seq higher_eq_priority (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) t) → (cpu2, some j) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t (sorted_pending_jobs job_arrival job_cost num_cpus arr_seq higher_eq_priority (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) t) → cpu1 = cpu2 := by
  intro j t cpu1 cpu2 SOME1 SOME2
  exact no_duplicate_jobs_any job_task num_cpus alpha higher_eq_priority t _
    (sorted_pending_jobs_uniq job_arrival job_cost num_cpus arr_seq H_arrival_times_are_consistent
      H_arrival_sequence_is_a_set higher_eq_priority (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) t) j cpu1 cpu2 SOME1 SOME2

theorem scheduler_scheduled_on {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (alpha : task_affinity sporadic_task num_cpus) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) :
    ∀ (j : Job) (cpu : processor num_cpus) (t : time),
      scheduled_on (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j cpu t = decide ((cpu, some j) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t (sorted_pending_jobs job_arrival job_cost num_cpus arr_seq higher_eq_priority (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) t)) := by
  intro j cpu t
  apply Bool.eq_iff_iff.mpr
  simp only [scheduled_on, decide_eq_true_eq]
  rw [scheduler_uses_construction_function]
  unfold apa_schedule
  constructor
  · intro SCHED
    exact pairs_to_function_neq_default none _ cpu (some j) SCHED (by simp)
  · intro IN
    exact pairs_to_function_mem none _ cpu (some j) (scheduler_uniq_cpus job_task num_cpus alpha higher_eq_priority t _) IN

theorem scheduler_has_cpus {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_task : Job → sporadic_task) (num_cpus : Nat) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) :
    ∀ (cpu : processor num_cpus) (t : time) (l : List Job), ∃ x, (cpu, x) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l := by
  intro cpu t l
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨none, ?_⟩
    simp only [schedule_jobs_from_list, List.foldl_nil]
    rw [List.mem_iff_getElem]
    exact ⟨cpu.val, by simp, by simp⟩
  | append_singleton l x ih =>
    obtain ⟨y, IN⟩ := ih
    rw [schedule_jobs_rcons]
    rcases replace_first_previous (should_be_scheduled job_task num_cpus alpha higher_eq_priority t x) (set_pair_2nd (some x)) IN with IN' | ⟨_, IN'⟩
    · exact ⟨y, IN'⟩
    · exact ⟨some x, IN'⟩

/-- LEAN_HELPER: in a sorted list, a mapping of an earlier job survives the insertion of the last job. -/
private theorem mapping_kept {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_task : Job → sporadic_task) (num_cpus : Nat) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) (H_priority_transitive : JLDP_is_transitive higher_eq_priority) (t : time) (l : List Job) (x j : Job) (cpu0 : processor num_cpus)
    (SORT : List.IsChain (fun a b => higher_eq_priority t a b = true) (l ++ [x])) (INj : j ∈ l)
    (IN : (cpu0, some j) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l) : (cpu0, some j) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t (l ++ [x]) := by
  rw [schedule_jobs_rcons]
  rcases replace_first_previous (should_be_scheduled job_task num_cpus alpha higher_eq_priority t x) (set_pair_2nd (some x)) IN with IN' | ⟨P, _⟩
  · exact IN'
  · exfalso
    have HP := order_sorted_rcons Job (higher_eq_priority t) l (H_priority_transitive t) j x SORT INj
    simp only [should_be_scheduled, HP, Bool.not_true, Bool.and_false] at P
    exact absurd P (by simp)

theorem scheduler_mapping_is_work_conserving {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_task : Job → sporadic_task) (num_cpus : Nat) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) (H_priority_transitive : JLDP_is_transitive higher_eq_priority) :
    ∀ (j : Job) (cpu : processor num_cpus) (t : time) (l : List Job),
      j ∈ l →
      List.IsChain (fun a b => higher_eq_priority t a b = true) l →
      l.Nodup →
      (∀ cpu0, (cpu0, some j) ∉ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l) →
      can_execute_on alpha (job_task j) cpu = true →
      ∃ j_other, (cpu, some j_other) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l := by
  intro j cpu t l
  revert cpu
  induction l using List.reverseRecOn with
  | nil => intro cpu IN; simp at IN
  | append_singleton l x ih =>
    intro cpu IN SORT UNIQ NOTSCHED CAN
    rw [List.nodup_append] at UNIQ
    obtain ⟨UNIQl, _, DISJ⟩ := UNIQ
    rcases List.mem_append.mp IN with INl | LAST
    · have IH := ih cpu INl (sorted_rcons_prefix Job (higher_eq_priority t) l x SORT) UNIQl
        (fun cpu0 h => NOTSCHED cpu0 (mapping_kept job_task num_cpus alpha higher_eq_priority H_priority_transitive t l x j cpu0 SORT INl h)) CAN
      obtain ⟨j_old, INold⟩ := IH
      rw [schedule_jobs_rcons]
      rcases replace_first_previous (should_be_scheduled job_task num_cpus alpha higher_eq_priority t x) (set_pair_2nd (some x)) INold with
        IN' | ⟨_, IN'⟩
      · exact ⟨j_old, IN'⟩
      · exact ⟨x, IN'⟩
    · have EQ : j = x := List.mem_singleton.mp LAST
      subst EQ
      rw [schedule_jobs_rcons] at NOTSCHED ⊢
      have ALL := replace_first_failed (should_be_scheduled job_task num_cpus alpha higher_eq_priority t j) (set_pair_2nd (some j))
        (l := schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l) (fun ⟨c, y⟩ _ => NOTSCHED c)
      obtain ⟨y, INy⟩ := scheduler_has_cpus job_task num_cpus alpha higher_eq_priority cpu t l
      have NP := ALL (cpu, y) INy
      cases y with
      | none => simp [should_be_scheduled, CAN] at NP
      | some j' =>
        rcases replace_first_previous (should_be_scheduled job_task num_cpus alpha higher_eq_priority t j) (set_pair_2nd (some j)) INy with
          IN' | ⟨_, IN'⟩
        · exact ⟨j', IN'⟩
        · exact ⟨j, IN'⟩

/-- LEAN_HELPER: the generic priority property of the mapping, for sorted duplicate-free lists. -/
private theorem mapping_priority_any {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_task : Job → sporadic_task) (num_cpus : Nat) (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : JLDP_policy Job) (H_priority_transitive : JLDP_is_transitive higher_eq_priority) (t : time) :
    ∀ (l : List Job) (j j_hp : Job) (cpu : processor num_cpus),
      j ∈ l →
      List.IsChain (fun a b => higher_eq_priority t a b = true) l →
      l.Nodup →
      (∀ cpu0, (cpu0, some j) ∉ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l) →
      can_execute_on alpha (job_task j) cpu = true →
      (cpu, some j_hp) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l →
      higher_eq_priority t j_hp j = true := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro j j_hp cpu IN; simp at IN
  | append_singleton l x ih =>
    intro j j_hp cpu IN SORT UNIQ NOTSCHED CAN SCHED
    have UNIQ' := UNIQ
    rw [List.nodup_append] at UNIQ'
    obtain ⟨UNIQl, _, DISJ⟩ := UNIQ'
    have NOTINx : x ∉ l := fun h => DISJ x h x (List.mem_singleton_self x) rfl
    have INhp := scheduler_job_in_mapping job_task num_cpus alpha higher_eq_priority _ j_hp t cpu SCHED
    have SORTl := sorted_rcons_prefix Job (higher_eq_priority t) l x SORT
    rcases List.mem_append.mp IN with INl | LAST
    · -- `j` is an earlier job
      have NOTSCHEDl : ∀ cpu0, (cpu0, some j) ∉ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l :=
        fun cpu0 h => NOTSCHED cpu0 (mapping_kept job_task num_cpus alpha higher_eq_priority H_priority_transitive t l x j cpu0 SORT INl h)
      have SCHED' := SCHED
      rw [schedule_jobs_rcons] at SCHED'
      by_cases EQhp : j_hp = x
      · subst EQhp
        exfalso
        rcases replace_first_cases SCHED' with PREV | ⟨⟨c, y⟩, EQ, SHOULD, IN'⟩
        · exact NOTINx (scheduler_job_in_mapping job_task num_cpus alpha higher_eq_priority l j_hp t cpu PREV)
        · simp only [set_pair_2nd, Prod.mk.injEq] at EQ
          obtain ⟨rfl, _⟩ := EQ
          cases y with
          | some j' =>
            simp only [should_be_scheduled, Bool.and_eq_true, Bool.not_eq_true'] at SHOULD
            have INj' := scheduler_job_in_mapping job_task num_cpus alpha higher_eq_priority l j' t cpu IN'
            have := order_sorted_rcons Job (higher_eq_priority t) l (H_priority_transitive t) j' j_hp SORT INj'
            rw [this] at SHOULD; exact absurd SHOULD.2 (by simp)
          | none =>
            obtain ⟨j'', IN''⟩ := scheduler_mapping_is_work_conserving job_task num_cpus alpha higher_eq_priority H_priority_transitive j cpu t l INl SORTl
              UNIQl NOTSCHEDl CAN
            have E1 := pairs_to_function_mem none _ cpu (some j'') (scheduler_uniq_cpus job_task num_cpus alpha higher_eq_priority t l) IN''
            have E2 := pairs_to_function_mem none _ cpu none (scheduler_uniq_cpus job_task num_cpus alpha higher_eq_priority t l) IN'
            rw [E1] at E2; exact absurd E2 (by simp)
      · have PREV : (cpu, some j_hp) ∈ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l := by
          rcases replace_first_cases SCHED' with PREV | ⟨y, EQ, _, _⟩
          · exact PREV
          · simp only [set_pair_2nd, Prod.mk.injEq, Option.some.injEq] at EQ; exact absurd EQ.2 EQhp
        exact ih j j_hp cpu INl SORTl UNIQl NOTSCHEDl CAN PREV
    · -- `j` is the last job
      have EQ : j = x := List.mem_singleton.mp LAST
      subst EQ
      by_cases EQhp : j_hp = j
      · subst EQhp; exact absurd SCHED (NOTSCHED cpu)
      · have INhpl : j_hp ∈ l := by
          rcases List.mem_append.mp INhp with h | h
          · exact h
          · exact absurd (List.mem_singleton.mp h) EQhp
        exact order_sorted_rcons Job (higher_eq_priority t) l (H_priority_transitive t) j_hp j SORT INhpl

/-- LEAN_HELPER: a backlogged job of the arrival sequence is one of the jobs being scheduled. -/
private theorem pending_in_sorted {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time) (num_cpus : Nat)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (higher_eq_priority : JLDP_policy Job) (sched : schedule Job num_cpus) (j : Job) (t : time)
    (ARRj : arrives_in arr_seq j) (PEND : pending job_arrival job_cost sched j t = true) :
    j ∈ sorted_pending_jobs job_arrival job_cost num_cpus arr_seq higher_eq_priority sched t := by
  unfold sorted_pending_jobs pending_jobs
  rw [mem_mc_sort, List.mem_filter]
  refine ⟨?_, PEND⟩
  have ARR := PEND
  simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq] at ARR
  exact arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 (t + 1) ARRj
    (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')

/-- LEAN_HELPER: the jobs being scheduled are sorted by priority. -/
private theorem sorted_pending_jobs_sorted {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time) (num_cpus : Nat)
    (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (H_priority_transitive : JLDP_is_transitive higher_eq_priority) (H_priority_total : ∀ t, ∀ x y, (higher_eq_priority t x y || higher_eq_priority t y x) = true)
    (sched : schedule Job num_cpus) (t : time) :
    List.IsChain (fun a b => higher_eq_priority t a b = true)
      (sorted_pending_jobs job_arrival job_cost num_cpus arr_seq higher_eq_priority sched t) :=
  (pairwise_mc_sort (fun a b c h1 h2 => H_priority_transitive t b a c h1 h2) (H_priority_total t) _).isChain

theorem scheduler_priority {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (alpha : task_affinity sporadic_task num_cpus) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (higher_eq_priority : JLDP_policy Job) (H_priority_transitive : JLDP_is_transitive higher_eq_priority) (H_priority_total : ∀ t, ∀ x y, (higher_eq_priority t x y || higher_eq_priority t y x) = true) :
    ∀ (j j_hp : Job) (cpu : processor num_cpus) (t : time),
      arrives_in arr_seq j →
      backlogged job_arrival job_cost (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j t = true →
      can_execute_on alpha (job_task j) cpu = true →
      scheduled_on (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j_hp cpu t = true →
      higher_eq_priority t j_hp j = true := by
  intro j j_hp cpu t ARRj BACK CAN SCHED
  simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true'] at BACK
  have NOTSCHED : ∀ cpu0, (cpu0, some j) ∉ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t (sorted_pending_jobs job_arrival job_cost num_cpus arr_seq higher_eq_priority (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) t) := by
    intro cpu0 IN
    have S := scheduler_scheduled_on job_arrival job_cost job_task num_cpus alpha arr_seq higher_eq_priority j cpu0 t
    rw [decide_eq_true IN] at S
    have : scheduled (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j t = true := List.any_eq_true.mpr ⟨cpu0, List.mem_finRange cpu0, S⟩
    rw [BACK.2] at this; exact absurd this (by simp)
  rw [scheduler_scheduled_on] at SCHED
  exact mapping_priority_any job_task num_cpus alpha higher_eq_priority H_priority_transitive t _ j j_hp cpu
    (pending_in_sorted job_arrival job_cost num_cpus arr_seq H_arrival_times_are_consistent higher_eq_priority
      (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j t ARRj BACK.1)
    (sorted_pending_jobs_sorted job_arrival job_cost num_cpus arr_seq higher_eq_priority H_priority_transitive
      H_priority_total (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) t)
    (sorted_pending_jobs_uniq job_arrival job_cost num_cpus arr_seq H_arrival_times_are_consistent
      H_arrival_sequence_is_a_set higher_eq_priority (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) t)
    NOTSCHED CAN (of_decide_eq_true SCHED)

/-! ### Properties of the scheduler -/

/-- LEAN_HELPER: a job scheduled by the scheduler is one of the pending jobs. -/
private theorem scheduled_in_pending {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (alpha : task_affinity sporadic_task num_cpus) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (j : Job) (t : time)
    (SCHED : scheduled (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j t = true) :
    j ∈ pending_jobs job_arrival job_cost num_cpus arr_seq (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) t := by
  obtain ⟨cpu, _, S⟩ := List.any_eq_true.mp SCHED
  rw [scheduler_scheduled_on] at S
  have := scheduler_job_in_mapping job_task num_cpus alpha higher_eq_priority _ j t cpu (of_decide_eq_true S)
  unfold sorted_pending_jobs at this
  exact (mem_mc_sort _).mp this

theorem scheduler_jobs_come_from_arrival_sequence {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (alpha : task_affinity sporadic_task num_cpus) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) :
    jobs_come_from_arrival_sequence (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) arr_seq := by
  intro j t SCHED
  have IN := scheduled_in_pending job_arrival job_cost job_task num_cpus alpha arr_seq higher_eq_priority j t SCHED
  unfold pending_jobs at IN
  exact in_arrivals_implies_arrived arr_seq j 0 (t + 1) (List.mem_filter.mp IN).1

theorem scheduler_jobs_must_arrive_to_execute {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (alpha : task_affinity sporadic_task num_cpus) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) :
    jobs_must_arrive_to_execute job_arrival (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) := by
  intro j t SCHED
  have IN := scheduled_in_pending job_arrival job_cost job_task num_cpus alpha arr_seq higher_eq_priority j t SCHED
  unfold pending_jobs at IN
  have PEND := (List.mem_filter.mp IN).2
  simp only [pending, Bool.and_eq_true] at PEND
  exact PEND.1

theorem scheduler_sequential_jobs {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (alpha : task_affinity sporadic_task num_cpus) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (higher_eq_priority : JLDP_policy Job) :
    sequential_jobs (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) := by
  intro j t cpu1 cpu2 SCHED1 SCHED2
  have S1 := scheduler_scheduled_on job_arrival job_cost job_task num_cpus alpha arr_seq higher_eq_priority j cpu1 t
  have S2 := scheduler_scheduled_on job_arrival job_cost job_task num_cpus alpha arr_seq higher_eq_priority j cpu2 t
  simp only [scheduled_on, SCHED1, SCHED2, decide_true] at S1 S2
  exact scheduler_has_no_duplicate_jobs job_arrival job_cost job_task num_cpus alpha arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority j t cpu1 cpu2
    (of_decide_eq_true S1.symm) (of_decide_eq_true S2.symm)

theorem scheduler_completed_jobs_dont_execute {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (alpha : task_affinity sporadic_task num_cpus) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (higher_eq_priority : JLDP_policy Job) :
    completed_jobs_dont_execute job_cost (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) := by
  have SEQ := scheduler_sequential_jobs job_arrival job_cost job_task num_cpus alpha arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
  intro j t
  induction t with
  | zero => simp [service]
  | succ t IHt =>
    have STEP : service (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j (t + 1) = service (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j t + service_at (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j t := by
      unfold service
      rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]
    rw [STEP]
    rcases Nat.lt_or_ge (service (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j t) (job_cost j) with LT | GE
    · have := service_at_most_one (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j SEQ t
      omega'
    · have ZERO : service_at (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j t = 0 := by
        unfold service_at
        apply Finset.sum_eq_zero
        intro cpu hcpu
        exfalso
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcpu
        have SCHED : scheduled (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j t = true := List.any_eq_true.mpr ⟨cpu, List.mem_finRange cpu, hcpu⟩
        have IN := scheduled_in_pending job_arrival job_cost job_task num_cpus alpha arr_seq higher_eq_priority j t SCHED
        unfold pending_jobs at IN
        have PEND := (List.mem_filter.mp IN).2
        simp only [pending, completed, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at PEND
        exact PEND.2 GE
      rw [ZERO, Nat.add_zero]; exact IHt

theorem scheduler_apa_work_conserving {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (alpha : task_affinity sporadic_task num_cpus) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (higher_eq_priority : JLDP_policy Job) (H_priority_transitive : JLDP_is_transitive higher_eq_priority) (H_priority_total : ∀ t, ∀ x y, (higher_eq_priority t x y || higher_eq_priority t y x) = true) :
    apa_work_conserving job_arrival job_cost job_task arr_seq (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) alpha := by
  intro j t ARRj BACK cpu CAN
  simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true'] at BACK
  have NOTSCHED : ∀ cpu0, (cpu0, some j) ∉ schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t (sorted_pending_jobs job_arrival job_cost num_cpus arr_seq higher_eq_priority (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) t) := by
    intro cpu0 IN
    have S := scheduler_scheduled_on job_arrival job_cost job_task num_cpus alpha arr_seq higher_eq_priority j cpu0 t
    rw [decide_eq_true IN] at S
    have : scheduled (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j t = true := List.any_eq_true.mpr ⟨cpu0, List.mem_finRange cpu0, S⟩
    rw [BACK.2] at this; exact absurd this (by simp)
  obtain ⟨j_other, IN⟩ := scheduler_mapping_is_work_conserving job_task num_cpus alpha higher_eq_priority H_priority_transitive j cpu t _
    (pending_in_sorted job_arrival job_cost num_cpus arr_seq H_arrival_times_are_consistent higher_eq_priority
      (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) j t ARRj BACK.1)
    (sorted_pending_jobs_sorted job_arrival job_cost num_cpus arr_seq higher_eq_priority H_priority_transitive
      H_priority_total (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) t)
    (sorted_pending_jobs_uniq job_arrival job_cost num_cpus arr_seq H_arrival_times_are_consistent
      H_arrival_sequence_is_a_set higher_eq_priority (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) t)
    NOTSCHED CAN
  refine ⟨j_other, ?_⟩
  rw [scheduler_scheduled_on]
  exact decide_eq_true IN

theorem scheduler_respects_affinity {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (alpha : task_affinity sporadic_task num_cpus) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) :
    respects_affinity job_task (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) alpha := by
  intro j cpu t SCHED
  rw [scheduler_scheduled_on] at SCHED
  exact scheduler_mapping_respects_affinity job_arrival job_cost job_task num_cpus alpha arr_seq higher_eq_priority j t cpu (of_decide_eq_true SCHED)

theorem scheduler_respects_policy {Job : Type u} [DecidableEq Job] {sporadic_task : Type v} [DecidableEq sporadic_task] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (num_cpus : Nat)
    (alpha : task_affinity sporadic_task num_cpus) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (higher_eq_priority : JLDP_policy Job) (H_priority_transitive : JLDP_is_transitive higher_eq_priority) (H_priority_total : ∀ t, ∀ x y, (higher_eq_priority t x y || higher_eq_priority t y x) = true) :
    respects_JLDP_policy_under_weak_APA job_arrival job_cost job_task arr_seq (scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority) alpha higher_eq_priority := by
  intro j j_hp cpu t ARRj BACK SCHED ALPHA
  exact scheduler_priority job_arrival job_cost job_task num_cpus alpha arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority H_priority_transitive H_priority_total j j_hp cpu t ARRj BACK
    ALPHA SCHED

end Prosa.Classic.Implementation.Apa.Schedule.ConcreteScheduler
