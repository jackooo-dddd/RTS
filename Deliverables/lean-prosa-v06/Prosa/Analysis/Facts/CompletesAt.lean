-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/completes_at.v

import Prosa.Analysis.Definitions.BusyInterval.Classical
import Prosa.Analysis.Facts.Model.Preemption

namespace Prosa.Analysis.Facts.CompletesAt

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Model.Preemption
open Prosa.Util.Sum
open scoped BigOperators

/-! Facts about `completes_at`.
Binders follow the elaborated source types: every lemma takes only the section
inputs and hypotheses it uses, in their elaborated order; instance inputs
quantified after a hypothesis are `∀ [..]` binders at that position.
Representation: a Boolean in `Prop` position is `= true`; `~~ b` is
`(!b) = true`; `t.-1` is `t - 1`; `a < b <= c` is
`(decide (a < b) && decide (b ≤ c)) = true`; `x \in s` is
`decide (x ∈ s) = true`; a MathComp `pred Job` is `Job → Bool`;
`\sum_(t1 <= t < t2) F t` is `∑ t ∈ (Finset.Ico t1 t2 : Finset Nat), F t` and
`\sum_(j <- s | P j) F j` is `sumFiltered s P F`, with a Boolean summand
coerced by `Bool.toNat`. -/

section CompletesAtLemmas

variable {Job : JobType} [DecidableEq Job]

/-- A job completing at `t > 0` was scheduled at `t - 1`. -/
theorem scheduled_at_precedes_completes_at [JobCost Job] {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t : instant) :
    0 < t → completes_at sched j t = true → scheduled_at sched j (t - 1) = true := by
  intro hpos hc
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega'⟩
  unfold completes_at at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_true_eq] at hc
  obtain ⟨hnc, hcomp⟩ := hc
  have hnc' : completed_by sched j k = false := by
    rcases hnc with h | h
    · simpa using h
    · omega'
  unfold completed_by at hnc' hcomp
  simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hnc' hcomp
  have hsplit := service_last_plus_before sched j k
  simp only [Nat.add_sub_cancel]
  apply service_at_implies_scheduled_at sched j k
  omega'

/-- A job that completes at `a` does not complete at any later `b`. -/
private theorem completes_at_unique [JobCost Job] {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (a b : instant) (hab : a < b)
    (ha : completes_at sched j a = true) : completes_at sched j b = false := by
  unfold completes_at at ha ⊢
  simp only [Bool.and_eq_true] at ha
  have hcb : completed_by sched j (b - 1) = true :=
    completion_monotonic sched j a (b - 1) (by omega') ha.2
  have hb0 : decide (b = 0) = false := decide_eq_false (by omega')
  rw [hcb, hb0]
  rfl

/-- A job completes at most once. -/
theorem job_completes_at_most_once [JobCost Job] {PState : ProcessorState Job}
    (sched : schedule PState) (j : Job) (t1 t2 : instant) :
    ∑ t ∈ (Finset.Ico t1 t2 : Finset Nat), (completes_at sched j t).toNat ≤ 1 := by
  induction t2 with
  | zero => simp
  | succ t2 ih =>
    rcases Nat.lt_or_ge t2 t1 with hlt | hge
    · have : Finset.Ico t1 (t2 + 1) = ∅ := Finset.Ico_eq_empty (by omega')
      rw [this]; simp
    · rw [Finset.sum_Ico_succ_top hge]
      cases hc : completes_at sched j t2
      · simpa using ih
      · have hz : ∑ t ∈ (Finset.Ico t1 t2 : Finset Nat), (completes_at sched j t).toNat = 0 := by
          apply Finset.sum_eq_zero
          intro t ht
          rw [Finset.mem_Ico] at ht
          cases hct : completes_at sched j t
          · rfl
          · have := completes_at_unique sched j t t2 ht.2 hct
            rw [hc] at this; exact absurd this (by decide)
        rw [hz]; simp

/-- Filtered sums of a Boolean indicator over a duplicate-free list are at
most one when at most one listed element satisfies it. -/
private theorem sumFiltered_indicator_le_one (l : List Job) (P : Job → Bool) (f : Job → Bool)
    (hnd : l.Nodup) (huniq : ∀ x y, x ∈ l → y ∈ l → f x = true → f y = true → x = y) :
    sumFiltered l P (fun x => (f x).toNat) ≤ 1 := by
  induction l with
  | nil => simp [sumFiltered]
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    have ih' := ih hnd.2 (fun x y hx hy => huniq x y (List.mem_cons_of_mem a hx)
      (List.mem_cons_of_mem a hy))
    unfold sumFiltered at ih' ⊢
    rw [List.filter_cons]
    cases hP : P a
    · simpa using ih'
    · cases hf : f a
      · simpa [hf] using ih'
      · have hz : ((l.filter P).map fun x => (f x).toNat).sum = 0 := by
          rw [List.sum_eq_zero_iff]
          intro n hn
          rw [List.mem_map] at hn
          obtain ⟨x, hx, rfl⟩ := hn
          rw [List.mem_filter] at hx
          cases hfx : f x
          · rfl
          · have := huniq x a (List.mem_cons_of_mem a hx.1) List.mem_cons_self hfx hf
            rw [this] at hx; exact absurd hx.1 hnd.1
        simp [hf, hz]

/-- At any `t > 0` at most one job (among the arrivals before `B`
satisfying `P`) completes. -/
theorem only_one_job_completes_at_a_time [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) (P : Job → Bool) (t B : instant), 0 < t →
      sumFiltered (arrivals_before arr_seq B) P (fun j => (completes_at sched j t).toNat) ≤ 1 := by
  intro huni arr_seq hva sched P t B hpos
  apply sumFiltered_indicator_le_one _ P (fun j => completes_at sched j t)
  · exact arrivals_uniq arr_seq hva.1 hva.2 0 B
  · intro x y _ _ hx hy
    exact huni x y sched (t - 1) (scheduled_at_precedes_completes_at sched x t hpos hx)
      (scheduled_at_precedes_completes_at sched y t hpos hy)

/-- Every completion time is a preemption time. -/
theorem completetion_time_is_preemption_time [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ (j : Job) (t : instant), completes_at sched j t = true →
      preemption_time arr_seq sched t = true := by
  intro huni arr_seq hva sched hfrom hmust hcomp _ hvalid j t hc
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · rw [h0]; exact zero_is_pt arr_seq hva PState huni sched hfrom hmust hvalid
  · have hsprev := scheduled_at_precedes_completes_at sched j t hpos hc
    have hcompt : completed_by sched j t = true := by
      unfold completes_at at hc; simp only [Bool.and_eq_true] at hc; exact hc.2
    have hns := completed_implies_not_scheduled sched j hcomp t hcompt
    cases hpt : preemption_time arr_seq sched t
    · have := neg_pt_scheduled_before arr_seq hva PState huni sched hfrom hmust hvalid j t
        (by rw [hpt]; rfl) hsprev
      rw [this] at hns; exact absurd hns (by decide)
    · rfl

/-- No higher-or-equal-priority job that arrived before a busy-interval prefix
completes during it. -/
theorem no_early_hep_job_completes_during_busy_prefix [JobArrival Job] [JobCost Job]
    [JLFP_policy Job] {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) (j : Job) (t t1 t2 : instant),
      busy_interval_prefix arr_seq sched j t1 t2 →
      (decide (t1 < t) && decide (t ≤ t2)) = true →
    ∀ jhp : Job, decide (jhp ∈ arrivals_before arr_seq t1) = true → hep_job jhp j = true →
      (!completes_at sched jhp t) = true := by
  intro hva sched j t t1 t2 hbusy ht jhp hin hhep
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  have harr : arrives_in arr_seq jhp := in_arrivals_implies_arrived arr_seq jhp 0 t1 hin
  have hbef := in_arrivals_implies_arrived_before arr_seq hva.1 jhp t1 hin
  have hc1 : completed_by sched jhp t1 = true := hbusy.2.1 jhp harr hhep hbef
  have hcprev : completed_by sched jhp (t - 1) = true :=
    completion_monotonic sched jhp t1 (t - 1) (by omega') hc1
  have ht0 : decide (t = 0) = false := decide_eq_false (by omega')
  unfold completes_at
  rw [hcprev, ht0]
  rfl

end CompletesAtLemmas

end Prosa.Analysis.Facts.CompletesAt
