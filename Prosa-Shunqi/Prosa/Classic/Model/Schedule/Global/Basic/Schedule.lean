-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/global/basic/schedule.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 27)

import Prosa.Classic.Util.Notation
import Prosa.Classic.Util.Bigcat
import Prosa.Classic.Util.OrdQuantifier
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Dedup

/-!
Global multiprocessor schedules (Rocq modules `Schedule` and
`ScheduleOfSporadicTask`).

Representation notes:
* `processor num_cpus := 'I_num_cpus` is `Fin num_cpus`; a schedule is
  `processor num_cpus → time → Option Job` (processor first, as in the source).
* Binder lists follow the Rocq contract: schedule notions take
  `{Job} {num_cpus} sched` (implicit carriers), `completed` adds `job_cost`,
  `pending`/`backlogged`/`carried_in`/`carried_out` add `job_arrival job_cost`;
  each lemma takes exactly the section hypotheses its Rocq proof uses.
* `sched cpu t == Some j` is `decide (sched cpu t = some j)`; the Boolean finite
  quantifier `[exists cpu, P cpu]` over `'I_n` is `(List.finRange n).any P`
  (as in `ord_quantifier`).
* `\sum_(cpu < n | P cpu) 1` is `∑ cpu ∈ Finset.univ.filter (P · = true), 1`;
  `\sum_(t1 <= t < t2) F t` is `∑ t ∈ Finset.Ico t1 t2, F t`.
* `\cat_(cpu < n) F cpu` is the v0.6 helper `bigCatFin F`; `\cat_(t1 <= t < t2)`
  is `bigCat t1 t2`; MathComp `undup` (keeps last occurrences) is
  `List.dedup` (same behaviour, as used throughout the v0.6 translation).
* Boolean statements: `b1 = b2` between Booleans is kept as an equation of
  `Bool`s; `x != 0` in proposition position is `(!decide (x = 0)) = true`; Boolean
  chains `a <= b < c` are `(decide (a ≤ b) && decide (b < c)) = true`.
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Schedule.Global.Basic.Schedule

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Util.Notation (make_sequence)
open Prosa.Util.Notation (bigCat)
open Prosa.Util.Bigcat (bigCatFin)
open BigOperators

universe u v

/-- LEAN_HELPER: `omega` after unfolding the classic time aliases. -/
local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

namespace Schedule

export Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
  (arrival_sequence jobs_arriving_at arrives_at arrives_in arrival_times_are_consistent
   arrival_sequence_is_a_set has_arrived arrived_before arrived_between
   jobs_arrived_between jobs_arrived_up_to jobs_arrived_before)

abbrev processor (num_cpus : Nat) := Fin num_cpus

abbrev schedule (Job : Type u) [DecidableEq Job] (num_cpus : Nat) :=
  processor num_cpus → time → Option Job

/-! ### Scheduled jobs -/

def scheduled_on {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (cpu : processor num_cpus) (t : time) : Bool :=
  decide (sched cpu t = some j)

def scheduled {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t : time) : Bool :=
  (List.finRange num_cpus).any (fun cpu => scheduled_on sched j cpu t)

def is_idle {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (cpu : processor num_cpus) (t : time) : Prop :=
  sched cpu t = none

def service_at {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t : time) : Nat :=
  ∑ cpu ∈ Finset.univ.filter (fun cpu => scheduled_on sched j cpu t = true), 1

def service {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t' : time) : Nat :=
  ∑ t ∈ Finset.Ico 0 t', service_at sched j t

def service_during {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t1 t2 : time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, service_at sched j t

def completed {Job : Type u} [DecidableEq Job] (job_cost : Job → time) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t : time) : Bool :=
  decide (job_cost j ≤ service sched j t)

def pending {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job) (t : time) : Bool :=
  has_arrived job_arrival j t && !completed job_cost sched j t

def backlogged {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job) (t : time) : Bool :=
  pending job_arrival job_cost sched j t && !scheduled sched j t

def carried_in {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job) (t1 : time) : Bool :=
  arrived_before job_arrival j t1 && !completed job_cost sched j t1

def carried_out {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job) (_t1 t2 : time) : Bool :=
  arrived_before job_arrival j t2 && !completed job_cost sched j t2

def jobs_scheduled_at {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (t : time) : List Job :=
  bigCatFin (fun cpu => make_sequence (sched cpu t))

def jobs_scheduled_between {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (t1 t2 : time) : List Job :=
  (bigCat t1 t2 (fun t => jobs_scheduled_at sched t)).dedup

/-! ### Valid schedules -/

def sequential_jobs {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) : Prop :=
  ∀ j t cpu1 cpu2, sched cpu1 t = some j → sched cpu2 t = some j → cpu1 = cpu2

def jobs_must_arrive_to_execute {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus) : Prop :=
  ∀ j t, scheduled sched j t = true → has_arrived job_arrival j t = true

def completed_jobs_dont_execute {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus) : Prop :=
  ∀ j t, service sched j t ≤ job_cost j

def jobs_come_from_arrival_sequence {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (arr_seq : arrival_sequence Job) : Prop :=
  ∀ j t, scheduled sched j t = true → arrives_in arr_seq j

/-! ### Basic lemmas -/

/-- LEAN_HELPER: zero service means no processor schedules `j`. -/
private theorem service_at_eq_zero_iff {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t : time) :
    service_at sched j t = 0 ↔ scheduled sched j t = false := by
  unfold service_at scheduled
  simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies, Bool.not_eq_true,
    List.any_eq_false, List.mem_finRange]

theorem not_scheduled_no_service {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) :
    ∀ t, (!scheduled sched j t) = decide (service_at sched j t = 0) := by
  intro t
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, service_at_eq_zero_iff]
  cases scheduled sched j t <;> simp

theorem cumulative_service_implies_service {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) :
    ∀ t1 t2 : time,
      (!decide (service_during sched j t1 t2 = 0)) = true →
      ∃ t, (decide (t1 ≤ t) && decide (t < t2)) = true ∧
        (!decide (service_at sched j t = 0)) = true := by
  intro t1 t2 NONZERO
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at NONZERO
  obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero NONZERO
  rw [Finset.mem_Ico] at ht
  exact ⟨t, by simp [ht.1, ht.2], by simpa using hne⟩

theorem service_implies_cumulative_service {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) :
    ∀ t t1 t2 : time,
      (decide (t1 ≤ t) && decide (t < t2)) = true →
      (!decide (service_at sched j t = 0)) = true →
      (!decide (service_during sched j t1 t2 = 0)) = true := by
  intro t t1 t2 LE NONZERO
  simp only [Bool.and_eq_true, decide_eq_true_eq] at LE
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at NONZERO ⊢
  have := Finset.single_le_sum (f := fun x => service_at sched j x)
    (fun _ _ => Nat.zero_le _) (Finset.mem_Ico.mpr LE)
  unfold service_during
  omega

/-! ### Sequential jobs -/

theorem service_at_most_one {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (H_sequential_jobs : sequential_jobs sched) :
    ∀ t, service_at sched j t ≤ 1 := by
  intro t
  unfold service_at
  simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, scheduled_on,
    decide_eq_true_eq] at ha hb
  exact H_sequential_jobs j t a b ha hb

theorem cumulative_service_le_delta {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (H_sequential_jobs : sequential_jobs sched) :
    ∀ t delta, service_during sched j t (t + delta) ≤ delta := by
  intro t delta
  unfold service_during
  calc ∑ x ∈ Finset.Ico t (t + delta), service_at sched j x
      ≤ ∑ _x ∈ Finset.Ico t (t + delta), 1 :=
        Finset.sum_le_sum fun x _ => service_at_most_one sched j H_sequential_jobs x
    _ = delta := by simp

/-! ### Completion -/

theorem completion_monotonic {Job : Type u} [DecidableEq Job] (job_cost : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job) :
    ∀ t t' : time,
      t ≤ t' →
      completed job_cost sched j t = true →
      completed job_cost sched j t' = true := by
  intro t t' LE COMPt
  simp only [completed, decide_eq_true_eq] at COMPt ⊢
  apply Nat.le_trans COMPt
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.le_refl 0) LE)

/-- LEAN_HELPER: service up to `t + 1` adds the service at `t`. -/
private theorem service_succ {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t : time) :
    service sched j (t + 1) = service sched j t + service_at sched j t := by
  unfold service
  exact Finset.sum_Ico_succ_top (Nat.zero_le t) _

theorem completed_implies_not_scheduled {Job : Type u} [DecidableEq Job]
    (job_cost : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job)
    (H_completed_jobs : completed_jobs_dont_execute job_cost sched) :
    ∀ t : time,
      completed job_cost sched j t = true →
      (!scheduled sched j t) = true := by
  intro t COMPLETED
  simp only [completed, decide_eq_true_eq] at COMPLETED
  by_contra SCHED
  simp only [Bool.not_eq_true', Bool.not_eq_false] at SCHED
  have hpos : service_at sched j t ≠ 0 := by
    intro h; rw [service_at_eq_zero_iff] at h; simp [h] at SCHED
  have BUG := H_completed_jobs j (t + 1)
  rw [service_succ] at BUG
  omega'

theorem cumulative_service_le_job_cost {Job : Type u} [DecidableEq Job]
    (job_cost : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job)
    (H_completed_jobs : completed_jobs_dont_execute job_cost sched) :
    ∀ t t' : time, service_during sched j t t' ≤ job_cost j := by
  intro t t'
  apply Nat.le_trans _ (H_completed_jobs j t')
  unfold service_during service
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.zero_le t) (Nat.le_refl t'))

/-! ### Arrival -/

theorem service_before_job_arrival_zero {Job : Type u} [DecidableEq Job]
    (job_arrival : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job)
    (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched) :
    ∀ t : time, t < job_arrival j → service_at sched j t = 0 := by
  intro t LT
  rw [service_at_eq_zero_iff]
  cases h : scheduled sched j t with
  | false => rfl
  | true =>
      have := H_jobs_must_arrive j t h
      simp only [has_arrived, decide_eq_true_eq] at this
      omega'

theorem cumulative_service_before_job_arrival_zero {Job : Type u} [DecidableEq Job]
    (job_arrival : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job)
    (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched) :
    ∀ t1 t2 : time,
      t2 ≤ job_arrival j →
      ∑ i ∈ Finset.Ico t1 t2, service_at sched j i = 0 := by
  intro t1 t2 LE
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_Ico] at hi
  exact service_before_job_arrival_zero job_arrival sched j H_jobs_must_arrive i (by omega')

theorem service_before_arrival_eq_service_during {Job : Type u} [DecidableEq Job]
    (job_arrival : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job)
    (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched) :
    ∀ t0 t : time,
      t0 ≤ job_arrival j →
      ∑ x ∈ Finset.Ico t0 (job_arrival j + t), service_at sched j x =
        ∑ x ∈ Finset.Ico (job_arrival j) (job_arrival j + t), service_at sched j x := by
  intro t0 t LE
  rw [← Finset.sum_Ico_consecutive _ LE (Nat.le_add_right _ _),
    cumulative_service_before_job_arrival_zero job_arrival sched j H_jobs_must_arrive t0
      (job_arrival j) (Nat.le_refl _), Nat.zero_add]

/-! ### Pending jobs -/

theorem scheduled_implies_pending {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (j : Job) (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs : completed_jobs_dont_execute job_cost sched) :
    ∀ t : time,
      scheduled sched j t = true →
      pending job_arrival job_cost sched j t = true := by
  intro t SCHED
  unfold pending
  rw [H_jobs_must_arrive j t SCHED, Bool.true_and]
  cases hc : completed job_cost sched j t with
  | false => rfl
  | true =>
      have := completed_implies_not_scheduled job_cost sched j H_completed_jobs t hc
      simp [SCHED] at this

/-! ### Jobs scheduled at a time -/

theorem mem_scheduled_jobs_eq_scheduled {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) :
    ∀ (j : Job) (t : time),
      decide (j ∈ jobs_scheduled_at sched t) = scheduled sched j t := by
  intro j t
  have key : j ∈ jobs_scheduled_at sched t ↔ ∃ cpu, sched cpu t = some j := by
    unfold jobs_scheduled_at bigCatFin
    rw [List.ofFn_eq_map, List.mem_flatten]
    constructor
    · rintro ⟨l, hl, hj⟩
      obtain ⟨cpu, _, rfl⟩ := List.mem_map.mp hl
      refine ⟨cpu, ?_⟩
      unfold make_sequence at hj
      cases h : sched cpu t with
      | none => simp [h] at hj
      | some k => simp [h] at hj; subst hj; rfl
    · rintro ⟨cpu, hcpu⟩
      exact ⟨make_sequence (sched cpu t), List.mem_map.mpr ⟨cpu, List.mem_finRange cpu, rfl⟩,
        by simp [make_sequence, hcpu]⟩
  have key2 : scheduled sched j t = true ↔ ∃ cpu, sched cpu t = some j := by
    simp [scheduled, scheduled_on, List.any_eq_true]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, key, key2]

theorem scheduled_jobs_uniq {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_sequential_jobs : sequential_jobs sched) :
    ∀ t : time, (jobs_scheduled_at sched t).Nodup := by
  intro t
  apply Prosa.Classic.Util.Bigcat.bigcat_ord_uniq
  · intro i
    unfold make_sequence
    split <;> simp
  · intro x i1 i2 IN1 IN2
    unfold make_sequence at IN1 IN2
    cases h1 : sched i1 t with
    | none => simp [h1] at IN1
    | some a =>
        cases h2 : sched i2 t with
        | none => simp [h2] at IN2
        | some b =>
            simp only [h1, List.mem_singleton] at IN1
            simp only [h2, List.mem_singleton] at IN2
            subst IN1; subst IN2
            exact H_sequential_jobs _ t i1 i2 h1 h2

theorem num_scheduled_jobs_le_num_cpus {Job : Type u} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) :
    ∀ t : time, (jobs_scheduled_at sched t).length ≤ num_cpus := by
  intro t
  have := Prosa.Classic.Util.Bigcat.size_bigcat_ord_max num_cpus
    (fun cpu => make_sequence (sched cpu t)) 1
    (by intro cpu; unfold make_sequence; split <;> simp)
  simpa [jobs_scheduled_at] using this

end Schedule

/-! ## Schedules of sporadic tasks -/

namespace ScheduleOfSporadicTask

open Schedule
open Prosa.Classic.Model.Arrival.Basic.Job.Job

export Schedule (processor schedule scheduled_on scheduled is_idle service_at service
  service_during completed pending backlogged carried_in carried_out jobs_scheduled_at
  jobs_scheduled_between sequential_jobs jobs_must_arrive_to_execute
  completed_jobs_dont_execute jobs_come_from_arrival_sequence)

def task_scheduled_on {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_task : Job → sporadic_task) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (tsk : sporadic_task) (cpu : processor num_cpus)
    (t : time) : Bool :=
  match sched cpu t with
  | some j => decide (job_task j = tsk)
  | none => false

def task_is_scheduled {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_task : Job → sporadic_task) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (tsk : sporadic_task) (t : time) : Bool :=
  (List.finRange num_cpus).any (fun cpu => task_scheduled_on job_task sched tsk cpu t)

def jobs_of_task_scheduled_between {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task) (t1 t2 : time) :
    List Job :=
  (jobs_scheduled_between sched t1 t2).filter (fun j => decide (job_task j = tsk))

def jobs_of_same_task_dont_execute_in_parallel {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) : Prop :=
  ∀ j j' t,
    job_task j = job_task j' →
    scheduled sched j t = true →
    scheduled sched j' t = true →
    j = j'

theorem cumulative_service_le_task_cost {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (jobs_dont_execute_after_completion : completed_jobs_dont_execute job_cost sched)
    (tsk : sporadic_task) (j : Job) (H_job_of_task : job_task j = tsk)
    (valid_job : valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) :
    ∀ t t' : time, service_during sched j t t' ≤ task_cost tsk := by
  intro t t'
  have h1 := cumulative_service_le_job_cost job_cost sched j jobs_dont_execute_after_completion t t'
  have h2 := valid_job.2.1
  simp only [job_cost_le_task_cost, decide_eq_true_eq] at h2
  rw [H_job_of_task] at h2
  exact Nat.le_trans h1 h2

end ScheduleOfSporadicTask

end Prosa.Classic.Model.Schedule.Global.Basic.Schedule
