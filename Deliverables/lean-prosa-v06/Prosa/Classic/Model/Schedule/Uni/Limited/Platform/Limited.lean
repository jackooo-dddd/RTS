-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/platform/limited.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 103)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
import Prosa.Util.Nondecreasing

/-!
Models with limited preemptions: fixed preemption points and floating nonpreemptive regions
(Rocq module `ModelWithLimitedPreemptions`).

Representation notes:
* `distances`, `nondecreasing_sequence` (v0.6 `util/nondecreasing.v`) and `max0`, `first0`, `last0`
  (v0.6 `util/list.v`) are the accepted v0.6 Lean definitions; `nth 0 s n` is `s.getD n 0`; `size s` is
  `s.length`; `[:: 0; 0]` is `[0, 0]`; `x \in s` is `x ∈ s` (as a Boolean, `decide (x ∈ s)`); `ε` is the v0.6 util
  notation for `1`.
* Boolean tests in proposition position are `= true`; `~~ b` is `(!b) = true`.
* `Require Export …definitions` / `…nondecreasing` are `import`s.
* Binder lists follow the Rocq contract.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Util.List (max0 first0 last0)
open Prosa.Util.Nondecreasing
open Prosa.Util.Epsilon

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def lengths_of_segments {Job : Type v} [DecidableEq Job] (job_preemption_points : Job → List time) (j : Job) : List Nat :=
  distances (job_preemption_points j)

def job_max_nps {Job : Type v} [DecidableEq Job] (job_preemption_points : Job → List time) (j : Job) : Nat :=
  max0 (lengths_of_segments job_preemption_points j)

def job_last_nps {Job : Type v} [DecidableEq Job] (job_preemption_points : Job → List time) (j : Job) : Nat :=
  last0 (lengths_of_segments job_preemption_points j)

def job_with_zero_cost_consists_of_one_empty_segment {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (arr_seq : arrival_sequence Job)
    (job_preemption_points : Job → List time) : Prop :=
  ∀ j, arrives_in arr_seq j → job_cost j = 0 → job_preemption_points j = [0, 0]

def last_segment_is_positive {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) : Prop :=
  ∀ j, arrives_in arr_seq j → 0 < job_cost j → 0 < job_last_nps job_preemption_points j

def beginning_of_execution_in_preemption_points {Job : Type v} [DecidableEq Job] (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) : Prop :=
  ∀ j, arrives_in arr_seq j → first0 (job_preemption_points j) = 0

def end_of_execution_in_preemption_points {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) :
    Prop :=
  ∀ j, arrives_in arr_seq j → last0 (job_preemption_points j) = job_cost j

def preemption_points_is_nondecreasing_sequence {Job : Type v} [DecidableEq Job] (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) : Prop :=
  ∀ j : Job, arrives_in arr_seq j → nondecreasing_sequence (job_preemption_points j)

def limited_preemptions_job_model {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) : Prop :=
  job_with_zero_cost_consists_of_one_empty_segment job_cost arr_seq job_preemption_points ∧
  last_segment_is_positive job_cost arr_seq job_preemption_points ∧
  beginning_of_execution_in_preemption_points arr_seq job_preemption_points ∧
  end_of_execution_in_preemption_points job_cost arr_seq job_preemption_points ∧
  preemption_points_is_nondecreasing_sequence arr_seq job_preemption_points

def task_last_nps {Task : Type u} [DecidableEq Task] (task_preemption_points : Task → List time) (tsk : Task) : Nat :=
  last0 (distances (task_preemption_points tsk))

def task_max_nps {Task : Type u} [DecidableEq Task] (task_preemption_points : Task → List time) (tsk : Task) : Nat :=
  max0 (distances (task_preemption_points tsk))

def task_beginning_of_execution_in_preemption_points {Task : Type u} [DecidableEq Task] (task_preemption_points : Task → List time) (ts : List Task) : Prop :=
  ∀ tsk, tsk ∈ ts → first0 (task_preemption_points tsk) = 0

def task_end_of_execution_in_preemption_points {Task : Type u} [DecidableEq Task] (task_cost : Task → time) (task_preemption_points : Task → List time) (ts : List Task) : Prop :=
  ∀ tsk, tsk ∈ ts → last0 (task_preemption_points tsk) = task_cost tsk

def task_preemption_points_is_nondecreasing_sequence {Task : Type u} [DecidableEq Task] (task_preemption_points : Task → List time) (ts : List Task) : Prop :=
  ∀ tsk, tsk ∈ ts → nondecreasing_sequence (task_preemption_points tsk)

def job_consists_of_the_same_number_of_segments_as_task {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) (task_preemption_points : Task → List time) : Prop :=
  ∀ j, arrives_in arr_seq j → (job_preemption_points j).length = (task_preemption_points (job_task j)).length

def lengths_of_task_segments_bound_length_of_job_segments {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) (task_preemption_points : Task → List time) : Prop :=
  ∀ j n, arrives_in arr_seq j →
    (distances (job_preemption_points j)).getD n 0 ≤ (distances (task_preemption_points (job_task j))).getD n 0

def task_segments_are_nonempty {Task : Type u} [DecidableEq Task] (task_preemption_points : Task → List time) (ts : List Task) : Prop :=
  ∀ tsk n, tsk ∈ ts → n < (distances (task_preemption_points tsk)).length →
    ε ≤ (distances (task_preemption_points tsk)).getD n 0

def fixed_preemption_points_task_model {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job] (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) (task_preemption_points : Task → List time) (ts : List Task) : Prop :=
  task_beginning_of_execution_in_preemption_points task_preemption_points ts ∧
  task_end_of_execution_in_preemption_points task_cost task_preemption_points ts ∧
  task_preemption_points_is_nondecreasing_sequence task_preemption_points ts ∧
  job_consists_of_the_same_number_of_segments_as_task job_task arr_seq job_preemption_points task_preemption_points ∧
  lengths_of_task_segments_bound_length_of_job_segments job_task arr_seq job_preemption_points
    task_preemption_points ∧
  task_segments_are_nonempty task_preemption_points ts

def fixed_preemption_points_model {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) (task_preemption_points : Task → List time) (ts : List Task) : Prop :=
  limited_preemptions_job_model job_cost arr_seq job_preemption_points ∧
  fixed_preemption_points_task_model task_cost job_task arr_seq job_preemption_points task_preemption_points ts

def job_max_np_segment_le_task_max_np_segment {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (job_preemption_points : Job → List time) (task_max_nps : Task → time) : Prop :=
  ∀ j : Job, arrives_in arr_seq j → job_max_nps job_preemption_points j ≤ task_max_nps (job_task j)

def model_with_floating_nonpreemptive_regions {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) (task_max_nps : Task → time) : Prop :=
  limited_preemptions_job_model job_cost arr_seq job_preemption_points ∧
  job_max_np_segment_le_task_max_np_segment job_task arr_seq job_preemption_points task_max_nps

def can_be_preempted_for_model_with_limited_preemptions {Job : Type v} [DecidableEq Job] (job_preemption_points : Job → List time) (j : Job) (progr : time) : Bool :=
  decide (progr ∈ job_preemption_points j)

def is_schedule_with_limited_preemptions {Job : Type v} [DecidableEq Job] (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) (sched : schedule Job) : Prop :=
  ∀ j t, arrives_in arr_seq j →
    (!can_be_preempted_for_model_with_limited_preemptions job_preemption_points j (service sched j t)) = true →
    scheduled_at sched j t = true

/-! ### Lemmas -/

theorem list_of_preemption_point_is_not_empty {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time)
    (H_limited_preemptions_job_model : limited_preemptions_job_model job_cost arr_seq job_preemption_points) (j : Job) (H_j_arrives : arrives_in arr_seq j) :
    0 < (job_preemption_points j).length := by
  obtain ⟨EMPT, _, _, END, _⟩ := H_limited_preemptions_job_model
  rcases Nat.eq_zero_or_pos (job_cost j) with ZERO | POS
  · rw [EMPT j H_j_arrives ZERO]; decide
  · have E := END j H_j_arrives
    cases h : job_preemption_points j with
    | nil => rw [h] at E; simp [last0] at E; omega'
    | cons a l => simp

theorem zero_in_preemption_points {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) (H_limited_preemptions_job_model : limited_preemptions_job_model job_cost arr_seq job_preemption_points)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) :
    0 ∈ job_preemption_points j := by
  have NE := list_of_preemption_point_is_not_empty job_cost arr_seq job_preemption_points
    H_limited_preemptions_job_model j H_j_arrives
  have BEG := H_limited_preemptions_job_model.2.2.1 j H_j_arrives
  cases h : job_preemption_points j with
  | nil => rw [h] at NE; simp at NE
  | cons a l => rw [h] at BEG; simp [first0] at BEG; simp [BEG]

theorem job_cost_in_nonpreemptive_points {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) (H_limited_preemptions_job_model : limited_preemptions_job_model job_cost arr_seq job_preemption_points)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) :
    job_cost j ∈ job_preemption_points j := by
  have NE := list_of_preemption_point_is_not_empty job_cost arr_seq job_preemption_points
    H_limited_preemptions_job_model j H_j_arrives
  have END := H_limited_preemptions_job_model.2.2.2.1 j H_j_arrives
  rw [← END]
  unfold last0
  have hne : job_preemption_points j ≠ [] := by
    intro h; rw [h] at NE; simp at NE
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hne]
  exact List.getLast_mem hne

theorem number_of_preemption_points_at_least_two {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time)
    (H_limited_preemptions_job_model : limited_preemptions_job_model job_cost arr_seq job_preemption_points) (j : Job) (H_j_arrives : arrives_in arr_seq j) :
    2 ≤ (job_preemption_points j).length := by
  rcases Nat.eq_zero_or_pos (job_cost j) with ZERO | POS
  · rw [H_limited_preemptions_job_model.1 j H_j_arrives ZERO]; decide
  · have Z := zero_in_preemption_points job_cost arr_seq job_preemption_points H_limited_preemptions_job_model j
      H_j_arrives
    have C := job_cost_in_nonpreemptive_points job_cost arr_seq job_preemption_points H_limited_preemptions_job_model
      j H_j_arrives
    by_contra LT
    match h : job_preemption_points j with
    | [] => rw [h] at Z; simp at Z
    | [a] => rw [h] at Z C; simp at Z C; omega'
    | _ :: _ :: _ => rw [h] at LT; simp at LT

theorem model_with_fixed_preemption_points_is_correct {Job : Type v} [DecidableEq Job] (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time)
    (sched : schedule Job)
    (H_is_schedule_with_limited_preemptions :
      is_schedule_with_limited_preemptions arr_seq job_preemption_points sched) :
    correct_preemption_model arr_seq sched (can_be_preempted_for_model_with_limited_preemptions job_preemption_points) := by
  intro j ARR
  constructor
  · intro t NPP
    exact H_is_schedule_with_limited_preemptions j t ARR NPP
  · intro t NSCHED SCHED
    have SERV : service sched j t = service sched j (t + 1) := by
      unfold service service_during
      rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]
      simp only [Bool.not_eq_true'] at NSCHED
      simp [service_at, NSCHED]
    cases hc : can_be_preempted_for_model_with_limited_preemptions job_preemption_points j (service sched j (t + 1))
    · exfalso
      have := H_is_schedule_with_limited_preemptions j t ARR (by rw [SERV, hc]; rfl)
      rw [this] at NSCHED; exact Bool.noConfusion NSCHED
    · rfl

theorem model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (job_preemption_points : Job → List time) (sched : schedule Job)
    (H_is_schedule_with_limited_preemptions :
      is_schedule_with_limited_preemptions arr_seq job_preemption_points sched)
    (task_max_nps : Task → time) (H_limited_preemptions_job_model : limited_preemptions_job_model job_cost arr_seq job_preemption_points)
    (H_job_max_np_segment_le_task_max_np_segment :
      job_max_np_segment_le_task_max_np_segment job_task arr_seq job_preemption_points task_max_nps) :
    model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq
      (can_be_preempted_for_model_with_limited_preemptions job_preemption_points)
      (job_max_nps job_preemption_points) task_max_nps := by
  intro j ARR
  have Z := zero_in_preemption_points job_cost arr_seq job_preemption_points H_limited_preemptions_job_model j ARR
  have C := job_cost_in_nonpreemptive_points job_cost arr_seq job_preemption_points H_limited_preemptions_job_model
    j ARR
  refine ⟨?_, ?_, fun _ => H_job_max_np_segment_le_task_max_np_segment j ARR, ?_⟩
  · simp [job_cannot_become_nonpreemptive_before_execution, can_be_preempted_for_model_with_limited_preemptions, Z]
  · simp [job_cannot_be_nonpreemptive_after_completion, can_be_preempted_for_model_with_limited_preemptions, C]
  · intro progr H
    simp only [Bool.and_eq_true, decide_eq_true_eq] at H
    by_cases IN : progr ∈ job_preemption_points j
    · refine ⟨progr, ?_, by simp [can_be_preempted_for_model_with_limited_preemptions, IN]⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega'
    · obtain ⟨_, _, BEG, END, NDEC⟩ := H_limited_preemptions_job_model
      have LTc : progr < job_cost j := by
        rcases Nat.lt_or_ge progr (job_cost j) with h | h
        · exact h
        · have : progr = job_cost j := by omega'
          rw [this] at IN; exact absurd C IN
      have SIZE := number_of_preemption_points_at_least_two job_cost arr_seq job_preemption_points
        ⟨‹_›, ‹_›, BEG, END, NDEC⟩ j ARR
      obtain ⟨n, SIZE2, N1, N2⟩ := belonging_to_segment_of_seq_is_total (job_preemption_points j) progr SIZE
        ⟨by rw [BEG j ARR]; exact Nat.zero_le _, by rw [END j ARR]; exact LTc⟩
      have MEMn : (job_preemption_points j).getD n 0 ∈ job_preemption_points j := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      have MEMn1 : (job_preemption_points j).getD (n + 1) 0 ∈ job_preemption_points j := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      have NEQ : (job_preemption_points j).getD n 0 ≠ progr := fun E => IN (E ▸ MEMn)
      have DIST := distance_between_neighboring_elements_le_max_distance_in_seq (job_preemption_points j) n
      refine ⟨(job_preemption_points j).getD (n + 1) 0, ?_, ?_⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq]
        have N1' : (job_preemption_points j).getD n 0 ≤ progr := N1
        have N2' : progr < (job_preemption_points j).getD (n + 1) 0 := N2
        have DIST' : (job_preemption_points j).getD (n + 1) 0 - (job_preemption_points j).getD n 0 ≤
            max0 (distances (job_preemption_points j)) := DIST
        unfold job_max_nps lengths_of_segments
        constructor <;> omega'
      · unfold can_be_preempted_for_model_with_limited_preemptions
        exact decide_eq_true MEMn1

end Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited.ModelWithLimitedPreemptions
