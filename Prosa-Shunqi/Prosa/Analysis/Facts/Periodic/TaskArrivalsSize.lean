-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/periodic/task_arrivals_size.v

import Prosa.Analysis.Facts.Periodic.ArrivalTimes
import Prosa.Analysis.Definitions.InfiniteJobs
import Prosa.Analysis.Facts.Sporadic.ArrivalSequence
import Prosa.Model.Task.Arrival.PeriodicAsSporadic

namespace Prosa.Analysis.Facts.Periodic.TaskArrivalsSize

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Offset
open Prosa.Model.Task.Arrival.Periodic
open Prosa.Model.Task.Arrival.Sporadic
open Prosa.Model.Task.Arrival.PeriodicAsSporadic
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.InfiniteJobs
open Prosa.Analysis.Facts.Model.Offset
open Prosa.Analysis.Facts.Model.TaskArrivals
open Prosa.Analysis.Facts.Sporadic.ArrivalSequence
open Prosa.Analysis.Facts.Periodic.ArrivalTimes

/-! Sizes of the task-arrival lists of a periodic task with an offset. Binders
follow the elaborated source types (unused section context and hypotheses are
absent, as in the elaborated source). Representation: `size s` is `s.length`;
`[::]` is `[]`; `x.+1` is `x + 1`; `t <> u` is `t ≠ u`; the statement-level
`let`s are kept; a Boolean in `Prop` position is `= true`; the sporadic facts
are used through the accepted `periodic_as_sporadic` instance, as in the
source. -/

macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

private theorem two_distinct_of_length {α : Type _} (l : List α) (hnd : l.Nodup) (hl : 1 < l.length) :
    ∃ a b, a ∈ l ∧ b ∈ l ∧ a ≠ b := by
  match l, hnd, hl with
  | a :: b :: _, hnd, _ =>
    refine ⟨a, b, List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    intro h; subst h
    exact (List.nodup_cons.mp hnd).1 List.mem_cons_self

private theorem sumSeq_eq_zero {I : Type _} (r : List I) (F : I → Nat) (h : ∀ x, x ∈ r → F x = 0) :
    sumSeq r F = 0 := by
  induction r with
  | nil => rfl
  | cons a r ih =>
      unfold sumSeq at ih ⊢
      rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem task_arrivals_size_at_non_arrival {Task : TaskType} [DecidableEq Task] [TaskOffset Task]
    [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, valid_offset arr_seq tsk → valid_period tsk = true →
        respects_periodic_task_model arr_seq tsk →
        ∀ t : Nat, (∀ n : Nat, t ≠ task_offset tsk + n * task_period tsk) →
          task_arrivals_at arr_seq tsk t = [] := by
  intro hva tsk hvo hvp hper t hT
  rw [List.eq_nil_iff_forall_not_mem]
  intro a ha
  unfold task_arrivals_at at ha
  rw [List.mem_filter] at ha
  have hta : job_task (Task := Task) a = tsk := of_decide_eq_true ha.2
  have hra : job_arrival a = t := hva.1 a _ (decide_eq_true ha.1)
  obtain ⟨n, hn⟩ := job_arrival_times arr_seq hva tsk hvo hvp hper a ⟨_, decide_eq_true ha.1⟩ hta
  exact hT n (hra ▸ hn)

theorem task_arrivals_at_size_cases {Task : TaskType} [DecidableEq Task] [PeriodicModel Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, valid_period tsk = true → respects_periodic_task_model arr_seq tsk →
        ∀ t : instant,
          (task_arrivals_at arr_seq tsk t).length = 0 ∨ (task_arrivals_at arr_seq tsk t).length = 1 := by
  intro hva tsk hvp hper t
  rcases Nat.lt_or_ge (task_arrivals_at arr_seq tsk t).length 2 with h | h
  · omega
  · exfalso
    have hnd : (task_arrivals_at arr_seq tsk t).Nodup := (hva.2 t).filter _
    obtain ⟨a, b, ha, hb, hab⟩ := two_distinct_of_length _ hnd (by omega)
    unfold task_arrivals_at at ha hb
    rw [List.mem_filter] at ha hb
    have hta : job_task (Task := Task) a = tsk := of_decide_eq_true ha.2
    have htb : job_task (Task := Task) b = tsk := of_decide_eq_true hb.2
    have hra : job_arrival a = t := hva.1 a _ (decide_eq_true ha.1)
    have hrb : job_arrival b = t := hva.1 b _ (decide_eq_true hb.1)
    have hsp := periodic_task_respects_sporadic_task_model arr_seq hva tsk hvp hper
    have hsep := hsp a b hab ⟨_, decide_eq_true ha.1⟩ ⟨_, decide_eq_true hb.1⟩ hta htb
      (by rw [hra, hrb])
    have hp : 0 < task_period tsk := of_decide_eq_true hvp
    have hmin : task_min_inter_arrival_time tsk = task_period tsk := rfl
    rw [hra, hrb, hmin] at hsep
    omega'

theorem size_task_arrivals_between_eq0 {Task : TaskType} [DecidableEq Task] [TaskOffset Task]
    [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, valid_offset arr_seq tsk → valid_period tsk = true →
        respects_periodic_task_model arr_seq tsk →
        ∀ n : Nat,
          let l := task_offset tsk + n * task_period tsk + 1
          let r := task_offset tsk + (n + 1) * task_period tsk
          (task_arrivals_between arr_seq tsk l r).length = 0 := by
  intro hva tsk hvo hvp hper n
  show (task_arrivals_between arr_seq tsk (task_offset tsk + n * task_period tsk + 1)
    (task_offset tsk + (n + 1) * task_period tsk)).length = 0
  rw [size_of_task_arrivals_between]
  apply sumSeq_eq_zero
  intro t ht
  rw [List.mem_range'_1] at ht
  rw [task_arrivals_size_at_non_arrival arr_seq hva tsk hvo hvp hper t, List.length_nil]
  intro n1 heq
  rw [heq] at ht
  have hlo : n * task_period tsk < n1 * task_period tsk := by omega'
  have hhi : n1 * task_period tsk < (n + 1) * task_period tsk := by omega'
  have h1 : n < n1 := Nat.lt_of_mul_lt_mul_right hlo
  have h2 : n1 < n + 1 := Nat.lt_of_mul_lt_mul_right hhi
  omega

theorem jobs_exists_later {Task : TaskType} [DecidableEq Task] [TaskOffset Task]
    [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, valid_offset arr_seq tsk → valid_period tsk = true →
        respects_periodic_task_model arr_seq tsk → infinite_jobs (Task := Task) arr_seq →
        ∀ n : Nat, ∃ j : Job, arrives_in arr_seq j ∧ job_task (Task := Task) j = tsk ∧
          job_arrival j = task_offset tsk + n * task_period tsk ∧
          job_index (Task := Task) arr_seq j = n := by
  intro hva tsk hvo hvp hper hinf n
  obtain ⟨j, harr, htsk, hidx⟩ := hinf tsk n
  exact ⟨j, harr, htsk, periodic_arrival_times arr_seq hva tsk hvo hvp hper n j harr htsk hidx, hidx⟩

theorem task_arrivals_at_size {Task : TaskType} [DecidableEq Task] [TaskOffset Task]
    [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, valid_offset arr_seq tsk → valid_period tsk = true →
        respects_periodic_task_model arr_seq tsk → infinite_jobs (Task := Task) arr_seq →
        ∀ n : Nat,
          let l := task_offset tsk + n * task_period tsk
          (task_arrivals_at arr_seq tsk l).length = 1 := by
  intro hva tsk hvo hvp hper hinf n
  obtain ⟨j', harr, htsk, hja, _⟩ := jobs_exists_later arr_seq hva tsk hvo hvp hper hinf n
  have hsp := periodic_task_respects_sporadic_task_model arr_seq hva tsk hvp hper
  have hvs := valid_period_is_valid_inter_arrival_time tsk hvp
  have h := only_j_in_task_arrivals_at_j arr_seq hva tsk hsp hvs j' harr htsk
  unfold task_arrivals_at_job_arrival at h
  rw [htsk, hja] at h
  show (task_arrivals_at arr_seq tsk (task_offset tsk + n * task_period tsk)).length = 1
  rw [h]
  rfl

theorem size_task_arrivals_up_to_offset {Task : TaskType} [DecidableEq Task] [TaskOffset Task]
    [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, valid_offset arr_seq tsk → valid_period tsk = true →
        respects_periodic_task_model arr_seq tsk → infinite_jobs (Task := Task) arr_seq →
        (task_arrivals_up_to arr_seq tsk (task_offset tsk)).length = 1 := by
  intro hva tsk hvo hvp hper hinf
  unfold task_arrivals_up_to
  rw [task_arrivals_between_cat arr_seq tsk 0 (task_offset tsk) (task_offset tsk + 1)
    (Nat.zero_le _) (Nat.le_succ _), List.length_append, size_of_task_arrivals_between,
    size_of_task_arrivals_between]
  have hz : sumSeq (List.range' 0 (task_offset tsk - 0))
      (fun t => (task_arrivals_at arr_seq tsk t).length) = 0 := by
    apply sumSeq_eq_zero
    intro t ht
    rw [List.mem_range'_1] at ht
    rw [task_arrivals_size_at_non_arrival arr_seq hva tsk hvo hvp hper t, List.length_nil]
    intro n heq
    omega'
  rw [hz, Nat.zero_add, Nat.add_sub_cancel_left]
  have h0 := task_arrivals_at_size arr_seq hva tsk hvo hvp hper hinf 0
  simp only [Nat.zero_mul, Nat.add_zero] at h0
  simp only [sumSeq, List.range'_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero]
  exact h0

theorem task_arrivals_up_to_size {Task : TaskType} [DecidableEq Task] [TaskOffset Task]
    [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, valid_offset arr_seq tsk → valid_period tsk = true →
        respects_periodic_task_model arr_seq tsk → infinite_jobs (Task := Task) arr_seq →
        ∀ n : Nat,
          let l := task_offset tsk + n * task_period tsk
          let r := task_offset tsk + (n + 1) * task_period tsk
          (task_arrivals_up_to arr_seq tsk l).length = n + 1 := by
  intro hva tsk hvo hvp hper hinf n
  have hp : 0 < task_period tsk := of_decide_eq_true hvp
  show (task_arrivals_up_to arr_seq tsk (task_offset tsk + n * task_period tsk)).length = n + 1
  induction n with
  | zero =>
      simp only [Nat.zero_mul, Nat.add_zero]
      exact size_task_arrivals_up_to_offset arr_seq hva tsk hvo hvp hper hinf
  | succ n ih =>
      have hle : task_offset tsk + n * task_period tsk ≤ task_offset tsk + (n + 1) * task_period tsk := by
        rw [Nat.succ_mul]; omega'
      rw [task_arrivals_cat arr_seq tsk _ _ hle, List.length_append, ih]
      have hlt : task_offset tsk + n * task_period tsk + 1 ≤ task_offset tsk + (n + 1) * task_period tsk := by
        rw [Nat.succ_mul]; omega'
      rw [task_arrivals_between_cat arr_seq tsk _ (task_offset tsk + (n + 1) * task_period tsk)
        (task_offset tsk + (n + 1) * task_period tsk + 1) hlt (Nat.le_succ _), List.length_append]
      have h0 := size_task_arrivals_between_eq0 arr_seq hva tsk hvo hvp hper n
      have h1 := task_arrivals_at_size arr_seq hva tsk hvo hvp hper hinf (n + 1)
      simp only at h0 h1
      rw [h0, size_of_task_arrivals_between, Nat.add_sub_cancel_left]
      simp only [sumSeq, List.range'_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero]
      rw [h1]

theorem eq_size_of_task_arrivals_seperated_by_period {Task : TaskType} [DecidableEq Task]
    [TaskOffset Task] [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, valid_offset arr_seq tsk → valid_period tsk = true →
        respects_periodic_task_model arr_seq tsk → infinite_jobs (Task := Task) arr_seq →
        ∀ n t : Nat, task_offset tsk ≤ t →
          (task_arrivals_at arr_seq tsk t).length =
            (task_arrivals_at arr_seq tsk (t + n * task_period tsk)).length := by
  intro hva tsk hvo hvp hper hinf n t hot
  have hp : 0 < task_period tsk := of_decide_eq_true hvp
  by_cases hmod : (t - task_offset tsk) % task_period tsk = 0
  · have hdiv := Nat.div_add_mod (t - task_offset tsk) (task_period tsk)
    rw [hmod, Nat.add_zero] at hdiv
    set k := (t - task_offset tsk) / task_period tsk
    have ht : t = task_offset tsk + k * task_period tsk := by
      rw [Nat.mul_comm] at hdiv; omega'
    have ht' : t + n * task_period tsk = task_offset tsk + (k + n) * task_period tsk := by
      rw [ht, Nat.add_mul]; omega'
    have h1 := task_arrivals_at_size arr_seq hva tsk hvo hvp hper hinf k
    have h2 := task_arrivals_at_size arr_seq hva tsk hvo hvp hper hinf (k + n)
    simp only at h1 h2
    rw [ht', h2, ht]
    exact h1
  · rw [task_arrivals_size_at_non_arrival arr_seq hva tsk hvo hvp hper t,
      task_arrivals_size_at_non_arrival arr_seq hva tsk hvo hvp hper (t + n * task_period tsk)]
    · intro n' heq
      apply hmod
      have : t - task_offset tsk + n * task_period tsk = n' * task_period tsk := by omega'
      have hm := congrArg (· % task_period tsk) this
      simp only [Nat.add_mul_mod_self_right, Nat.mul_mod_left] at hm
      exact hm
    · intro n' heq
      apply hmod
      have : t - task_offset tsk = n' * task_period tsk := by omega'
      rw [this, Nat.mul_mod_left]

end Prosa.Analysis.Facts.Periodic.TaskArrivalsSize
