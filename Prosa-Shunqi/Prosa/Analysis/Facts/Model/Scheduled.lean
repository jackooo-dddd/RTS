-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/scheduled.v

import Prosa.Model.Schedule.Scheduled
import Prosa.Analysis.Definitions.Service
import Prosa.Model.Processor.PlatformProperties
import Prosa.Analysis.Facts.Behavior.Arrivals

namespace Prosa.Analysis.Facts.Model.Scheduled

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Schedule.Scheduled
open Prosa.Analysis.Definitions.Service
open Prosa.Model.Processor.PlatformProperties
open Prosa.Analysis.Facts.Behavior.Arrivals

/-- Membership in the filtered list of scheduled jobs. -/
private theorem mem_scheduled_jobs_at {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (j : Job) (t : instant) :
    j ∈ scheduled_jobs_at arr_seq sched t ↔
      j ∈ arrivals_up_to arr_seq t ∧ scheduled_at sched j t = true := by
  simp [scheduled_jobs_at, List.mem_filter]

theorem scheduled_jobs_at_iff {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ (j : Job) (t : instant),
          decide (j ∈ scheduled_jobs_at arr_seq sched t) = scheduled_at sched j t := by
  intro hva sched hfrom hmust j t
  by_cases hs : scheduled_at sched j t = true
  · have hup := arrivals_up_to_scheduled_at arr_seq hva.1 sched hfrom hmust j t hs t (Nat.le_refl _)
    rw [hs]; simp only [decide_eq_true_eq] at hup ⊢
    exact (mem_scheduled_jobs_at arr_seq sched j t).2 ⟨hup, hs⟩
  · have hf : scheduled_at sched j t = false := by simpa using hs
    rw [hf]; simp only [decide_eq_false_iff_not]
    intro hm; exact hs ((mem_scheduled_jobs_at arr_seq sched j t).1 hm).2

theorem scheduled_jobs_at_nil {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ t : instant,
          (scheduled_jobs_at arr_seq sched t).isEmpty = true ↔
            ∀ j : Job, (!scheduled_at sched j t) = true := by
  intro hva sched hfrom hmust t
  have hiff := scheduled_jobs_at_iff arr_seq hva sched hfrom hmust
  constructor
  · intro hnil j
    have hmem : j ∉ scheduled_jobs_at arr_seq sched t := by
      rw [List.isEmpty_iff] at hnil; rw [hnil]; exact List.not_mem_nil
    have := hiff j t
    rw [decide_eq_false hmem] at this
    rw [← this]; rfl
  · intro hall
    rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
    intro j hm
    have h1 := hiff j t
    rw [decide_eq_true hm] at h1
    have h2 := hall j
    rw [← h1] at h2
    exact absurd h2 (by decide)

theorem not_scheduled_when_idle {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ (j : Job) (t : instant),
          is_idle arr_seq sched t = true → (!scheduled_at sched j t) = true := by
  intro hva sched hfrom hmust j t hidle
  exact (scheduled_jobs_at_nil arr_seq hva sched hfrom hmust t).1 hidle j

theorem scheduled_at_implies_in_served_at {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ideal_progress_proc_model PState →
        ∀ (j : Job) (t : instant),
          scheduled_at sched j t = true →
            decide (j ∈ served_jobs_at arr_seq sched t) = true := by
  intro hva sched hfrom hmust hideal j t hs
  have hup := arrivals_up_to_scheduled_at arr_seq hva.1 sched hfrom hmust j t hs t (Nat.le_refl _)
  simp only [decide_eq_true_eq] at hup ⊢
  simp only [served_jobs_at, List.mem_filter]
  refine ⟨hup, ?_⟩
  simp only [receives_service_at, service_at]
  exact decide_eq_true (hideal j (sched t) hs)

/-- The scheduled jobs are duplicate-free. -/
private theorem scheduled_jobs_at_nodup {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (hva : valid_arrival_sequence arr_seq) (sched : schedule PState) (t : instant) :
    (scheduled_jobs_at arr_seq sched t).Nodup :=
  List.Nodup.filter _ (arrivals_uniq arr_seq hva.1 hva.2 0 (t + 1))

theorem scheduled_jobs_at_seq1 {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        uniprocessor_model PState →
        ∀ t : instant, (scheduled_jobs_at arr_seq sched t).length ≤ 1 := by
  intro hva sched _ _ huni t
  have hnd := scheduled_jobs_at_nodup arr_seq hva sched t
  have hmem := fun j => mem_scheduled_jobs_at arr_seq sched j t
  generalize hs : scheduled_jobs_at arr_seq sched t = s at hnd hmem
  match s, hnd, hmem with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: rest, hnd, hmem =>
      exfalso
      have hab : a ≠ b := by
        intro h; subst h; exact (List.nodup_cons.1 hnd).1 (List.mem_cons_self)
      have ha := ((hmem a).1 List.mem_cons_self).2
      have hb := ((hmem b).1 (List.mem_cons_of_mem _ List.mem_cons_self)).2
      exact hab (huni a b sched t ha hb)

theorem scheduled_jobs_at_uni_cases {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        uniprocessor_model PState →
        ∀ t : instant,
          decide (scheduled_jobs_at arr_seq sched t = []) = true ∨
            ∃ j : Job, decide (scheduled_jobs_at arr_seq sched t = [j]) = true := by
  intro hva sched hfrom hmust huni t
  have hlen := scheduled_jobs_at_seq1 arr_seq hva sched hfrom hmust huni t
  generalize scheduled_jobs_at arr_seq sched t = s at hlen
  match s, hlen with
  | [], _ => left; simp
  | [j], _ => right; exact ⟨j, by simp⟩
  | _ :: _ :: _, h => simp at h

theorem scheduled_jobs_at_uni {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        uniprocessor_model PState →
        ∀ (j : Job) (t : instant),
          decide (scheduled_jobs_at arr_seq sched t = [j]) =
            decide (scheduled_job_at arr_seq sched t = some j) := by
  intro hva sched hfrom hmust huni j t
  unfold scheduled_job_at
  rcases scheduled_jobs_at_uni_cases arr_seq hva sched hfrom hmust huni t with h | ⟨j', h⟩
  · simp only [decide_eq_true_eq] at h; rw [h]; simp
  · simp only [decide_eq_true_eq] at h; rw [h]; simp [eq_comm]

theorem scheduled_job_at_scheduled_at {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        uniprocessor_model PState →
        ∀ (j : Job) (t : instant),
          decide (scheduled_job_at arr_seq sched t = some j) = scheduled_at sched j t := by
  intro hva sched hfrom hmust huni j t
  rw [← scheduled_jobs_at_uni arr_seq hva sched hfrom hmust huni j t,
    ← scheduled_jobs_at_iff arr_seq hva sched hfrom hmust j t]
  rcases scheduled_jobs_at_uni_cases arr_seq hva sched hfrom hmust huni t with h | ⟨j', h⟩
  · simp only [decide_eq_true_eq] at h; rw [h]; simp
  · simp only [decide_eq_true_eq] at h; rw [h]; simp [eq_comm]

theorem scheduled_jobs_at_scheduled_at {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        uniprocessor_model PState →
        ∀ (j : Job) (t : instant),
          decide (scheduled_jobs_at arr_seq sched t = [j]) = scheduled_at sched j t := by
  intro hva sched hfrom hmust huni j t
  rw [scheduled_jobs_at_uni arr_seq hva sched hfrom hmust huni j t,
    scheduled_job_at_scheduled_at arr_seq hva sched hfrom hmust huni j t]

theorem scheduled_job_at_none {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ t : instant,
          scheduled_job_at arr_seq sched t = none ↔
            ∀ j : Job, (!scheduled_at sched j t) = true := by
  intro hva sched hfrom hmust t
  rw [← scheduled_jobs_at_nil arr_seq hva sched hfrom hmust t]
  unfold scheduled_job_at
  cases scheduled_jobs_at arr_seq sched t <;> simp

theorem is_idle_iff {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (t : instant) :
    is_idle arr_seq sched t = decide (scheduled_job_at arr_seq sched t = none) := by
  unfold is_idle scheduled_job_at
  cases scheduled_jobs_at arr_seq sched t <;> simp

theorem is_nonidle_iff {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        uniprocessor_model PState →
        ∀ t : instant,
          (!is_idle arr_seq sched t) = true ↔ ∃ j : Job, scheduled_at sched j t = true := by
  intro hva sched hfrom hmust _ t
  have hnil := scheduled_jobs_at_nil arr_seq hva sched hfrom hmust t
  constructor
  · intro hni
    by_contra hno
    have hall : ∀ j : Job, (!scheduled_at sched j t) = true := by
      intro j; cases h : scheduled_at sched j t
      · rfl
      · exact absurd ⟨j, h⟩ hno
    have := hnil.2 hall
    simp [is_idle, this] at hni
  · rintro ⟨j, hj⟩
    cases hid : is_idle arr_seq sched t
    · rfl
    · have := hnil.1 hid j; rw [hj] at this; exact absurd this (by decide)

/-- Informative case analysis (the source's `{_} + {_}` view). -/
def scheduled_at_dec {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ t : instant,
          PSum (∃ j : Job, scheduled_at sched j t = true)
            (∀ j : Job, (!scheduled_at sched j t) = true) :=
  fun hva sched hfrom hmust t =>
    match h : scheduled_jobs_at arr_seq sched t with
    | [] => PSum.inr ((scheduled_jobs_at_nil arr_seq hva sched hfrom hmust t).1 (by rw [h]; rfl))
    | j :: _ => PSum.inl ⟨j, by
        have := scheduled_jobs_at_iff arr_seq hva sched hfrom hmust j t
        rw [h] at this; simpa using this.symm⟩

theorem scheduled_at_cases {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ t : instant,
          is_idle arr_seq sched t = true ∨ ∃ j : Job, scheduled_at sched j t = true := by
  intro hva sched hfrom hmust t
  match scheduled_at_dec arr_seq hva sched hfrom hmust t with
  | PSum.inl h => exact Or.inr h
  | PSum.inr h => exact Or.inl ((scheduled_jobs_at_nil arr_seq hva sched hfrom hmust t).2 h)

end Prosa.Analysis.Facts.Model.Scheduled
