-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/preemption.v

import Prosa.Model.Schedule.PriorityDriven
import Prosa.Analysis.Facts.Behavior.Completion
import Prosa.Analysis.Facts.Model.Scheduled
import Prosa.Util.SearchArg

namespace Prosa.Analysis.Facts.Model.Preemption

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Util.SearchArg

/-! Facts about preemption times.
Binders follow the elaborated source types: every lemma takes only the section
inputs and hypotheses it uses, in their elaborated order; instance inputs
quantified after a hypothesis are `∀ [..]` binders at that position.
Representation: a Boolean in `Prop` position is `= true`; `~~ b` is
`(!b) = true`; `a <= b < c` is `(decide (a ≤ b) && decide (b < c)) = true`
(and similarly for the other chained comparisons); `t.+1` is `t + 1`; `t.-1`
is `t - 1`; `a != b` is `decide (a ≠ b) = true`; `exists2 x, P & Q` is
`∃ x, P ∧ Q`. -/

section PreemptionTimes

variable {Job : JobType} [DecidableEq Job]

/-- An interval either contains no preemption time or an earliest one. -/
theorem preemption_time_interval_case [JobPreemptable Job] (arr_seq : arrival_sequence Job)
    {PState : ProcessorState Job} (sched : schedule PState) :
    ∀ t1 t2 : Nat,
      (∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true →
        (!preemption_time arr_seq sched t) = true) ∨
      (∃ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true ∧
        preemption_time arr_seq sched t = true ∧
        ∀ t' : Nat, t1 ≤ t' → preemption_time arr_seq sched t' = true → t ≤ t') := by
  intro t1 t2
  rcases earliest_pred_element_exists_case (preemption_time arr_seq sched) t1 t2 with h | h
  · left
    intro t ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    simp [h t ht]
  · right
    obtain ⟨t, ht, hp, hmin⟩ := h
    exact ⟨t, by simp [ht.1, ht.2], hp, hmin⟩

/-- An idle instant is a preemption time. -/
theorem idle_time_is_pt [JobPreemptable Job] (arr_seq : arrival_sequence Job)
    {PState : ProcessorState Job} (sched : schedule PState) (t : instant) :
    is_idle arr_seq sched t = true → preemption_time arr_seq sched t = true := by
  intro h
  rw [is_idle_iff] at h
  have hn : scheduled_job_at arr_seq sched t = none := of_decide_eq_true h
  unfold preemption_time
  rw [hn]

variable [JobArrival Job] [JobCost Job] [JobPreemptable Job]

/-- Time zero is a preemption time. -/
theorem zero_is_pt (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      valid_preemption_model arr_seq sched →
      preemption_time arr_seq sched 0 = true := by
  intro hva PState huni sched hfrom hmust hvalid
  unfold preemption_time
  cases hs : scheduled_job_at arr_seq sched 0 with
  | none => rfl
  | some j =>
    have hsched : scheduled_at sched j 0 = true := by
      rw [← scheduled_job_at_scheduled_at arr_seq hva sched hfrom hmust huni j 0, hs]; simp
    have harr := hfrom j 0 hsched
    dsimp only
    rw [service0]
    exact (hvalid j harr).1

/-- The first instant of an execution segment is a preemption time. -/
theorem first_moment_is_pt (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      valid_preemption_model arr_seq sched →
    ∀ (j : Job) (prt : instant), arrives_in arr_seq j →
      (!scheduled_at sched j prt) = true → scheduled_at sched j (prt + 1) = true →
      preemption_time arr_seq sched (prt + 1) = true := by
  intro hva PState huni sched hfrom hmust hvalid j prt harr hns hs
  have hsj : scheduled_job_at arr_seq sched (prt + 1) = some j := by
    have := scheduled_job_at_scheduled_at arr_seq hva sched hfrom hmust huni j (prt + 1)
    rw [hs] at this
    exact of_decide_eq_true this
  unfold preemption_time
  rw [hsj]
  exact (hvalid j harr).2.2.2 prt hns hs

/-- A job scheduled at a non-preemption time `t + 1` was scheduled at `t`. -/
theorem neg_pt_scheduled_at (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      valid_preemption_model arr_seq sched →
    ∀ (j : Job) (t : Nat), scheduled_at sched j (t + 1) = true →
      (!preemption_time arr_seq sched (t + 1)) = true → scheduled_at sched j t = true := by
  intro hva PState huni sched hfrom hmust hvalid j t hs hnp
  cases h : scheduled_at sched j t
  · have hpt := first_moment_is_pt arr_seq hva PState huni sched hfrom hmust hvalid j t
      (hfrom j (t + 1) hs) (by rw [h]; rfl) hs
    rw [hpt] at hnp
    exact absurd hnp (by decide)
  · rfl

/-- A job scheduled at `t - 1` remains scheduled at a non-preemption time `t`. -/
theorem neg_pt_scheduled_before (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      valid_preemption_model arr_seq sched →
    ∀ (j : Job) (t : instant), (!preemption_time arr_seq sched t) = true →
      scheduled_at sched j (t - 1) = true → scheduled_at sched j t = true := by
  intro hva PState huni sched hfrom hmust hvalid j t hnp hs
  cases t with
  | zero => exact hs
  | succ t =>
    rcases scheduled_at_cases arr_seq hva sched hfrom hmust (t + 1) with hidle | ⟨s, hss⟩
    · rw [idle_time_is_pt arr_seq sched (t + 1) hidle] at hnp
      exact absurd hnp (by decide)
    · have hst := neg_pt_scheduled_at arr_seq hva PState huni sched hfrom hmust hvalid s t hss hnp
      have hs1 : scheduled_at sched j t = true := by simpa using hs
      have heq : s = j := huni s j sched t hst hs1
      rw [← heq]
      exact hss

/-- Without preemption times in `(t1, t2]`, a job scheduled at `t1` is
scheduled at `t2`. -/
theorem neg_pt_scheduled_continuously_before (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      valid_preemption_model arr_seq sched →
    ∀ (j : Job) (t1 : instant) (t2 : Nat), scheduled_at sched j t1 = true → t1 ≤ t2 →
      (∀ t : Nat, (decide (t1 < t) && decide (t ≤ t2)) = true →
        (!preemption_time arr_seq sched t) = true) →
      scheduled_at sched j t2 = true := by
  intro hva PState huni sched hfrom hmust hvalid j t1 t2 hs hle hnpt
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    have hk := ih (fun t ht => hnpt t (by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; omega'))
    apply neg_pt_scheduled_before arr_seq hva PState huni sched hfrom hmust hvalid j (t1 + (k + 1))
    · exact hnpt _ (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    · have : t1 + (k + 1) - 1 = t1 + k := by omega'
      rw [this]; exact hk

/-- Without preemption times in `[t1, t2]`, a job scheduled at `t2` is
scheduled at `t1`. -/
theorem neg_pt_scheduled_continuously_after (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      valid_preemption_model arr_seq sched →
    ∀ (j : Job) (t1 : Nat) (t2 : instant), scheduled_at sched j t2 = true → t1 ≤ t2 →
      (∀ t : Nat, (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
        (!preemption_time arr_seq sched t) = true) →
      scheduled_at sched j t1 = true := by
  intro hva PState huni sched hfrom hmust hvalid j t1 t2 hs hle hnpt
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    apply ih
    · apply neg_pt_scheduled_at arr_seq hva PState huni sched hfrom hmust hvalid j (t1 + k)
      · have : t1 + k + 1 = t1 + (k + 1) := by omega'
        rw [this]; exact hs
      · exact hnpt _ (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    · intro t ht
      exact hnpt t (by simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; omega')

/-- Without preemption times in `[t1, t2)`, the job scheduled at one instant
of the interval is scheduled at every instant of it. -/
theorem neg_pt_scheduled_continuous (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      valid_preemption_model arr_seq sched →
    ∀ (j : Job) (t1 t2 t t' : Nat),
      (decide (t1 ≤ t) && decide (t < t2)) = true →
      (decide (t1 ≤ t') && decide (t' < t2)) = true →
      (∀ t0 : Nat, (decide (t1 ≤ t0) && decide (t0 < t2)) = true →
        (!preemption_time arr_seq sched t0) = true) →
      scheduled_at sched j t = true → scheduled_at sched j t' = true := by
  intro hva PState huni sched hfrom hmust hvalid j t1 t2 t t' h1 h2 hnp hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  rcases Nat.le_total t t' with hle | hle
  · apply neg_pt_scheduled_continuously_before arr_seq hva PState huni sched hfrom hmust hvalid j t t'
      hs hle
    intro x hx
    exact hnp x (by simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢; omega')
  · apply neg_pt_scheduled_continuously_after arr_seq hva PState huni sched hfrom hmust hvalid j t' t
      hs hle
    intro x hx
    exact hnp x (by simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢; omega')

/-- Two different jobs scheduled at two instants are separated by a
preemption time. -/
theorem neq_scheduled_at_pt (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      valid_preemption_model arr_seq sched →
    ∀ (j : Job) (t : instant), scheduled_at sched j t = true →
    ∀ (j' : Job) (t' : instant), scheduled_at sched j' t' = true →
      decide (j ≠ j') = true → t ≤ t' →
      ∃ pt : instant, preemption_time arr_seq sched pt = true ∧
        (decide (t < pt) && decide (pt ≤ t')) = true := by
  intro hva PState huni sched hfrom hmust hvalid j t hs j' t' hs' hne hle
  have hne' : j ≠ j' := of_decide_eq_true hne
  revert hs' hle
  induction t' with
  | zero =>
    intro hs' hle
    have ht : t = 0 := Nat.le_zero.mp hle
    rw [ht] at hs
    exact absurd (huni j j' sched 0 hs hs') hne'
  | succ t' ih =>
    intro hs' hle
    rcases Nat.lt_or_ge t (t' + 1) with hlt | hge
    · cases hpt : preemption_time arr_seq sched (t' + 1)
      · have hprev := neg_pt_scheduled_at arr_seq hva PState huni sched hfrom hmust hvalid j' t' hs'
          (by rw [hpt]; rfl)
        obtain ⟨pt, hp, hin⟩ := ih hprev (by omega')
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
        exact ⟨pt, hp, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'⟩
      · exact ⟨t' + 1, hpt, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'⟩
    · have ht : t = t' + 1 := Nat.le_antisymm hle hge
      rw [ht] at hs
      exact absurd (huni j j' sched _ hs hs') hne'

/-- The separating preemption time can be chosen so that the second job is
scheduled at it. -/
theorem neq_scheduled_at_pt_continuous_sched (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      valid_preemption_model arr_seq sched →
    ∀ (j : Job) (t : instant), scheduled_at sched j t = true →
    ∀ (j' : Job) (t' : instant), scheduled_at sched j' t' = true →
      decide (j ≠ j') = true → t ≤ t' →
      ∃ pt : instant, preemption_time arr_seq sched pt = true ∧
        (decide (t < pt) && decide (pt ≤ t')) = true ∧ scheduled_at sched j' pt = true := by
  intro hva PState huni sched hfrom hmust hvalid j t hs j' t' hs' hne hle
  have hne' : j ≠ j' := of_decide_eq_true hne
  revert hs' hle
  induction t' with
  | zero =>
    intro hs' hle
    have ht : t = 0 := Nat.le_zero.mp hle
    rw [ht] at hs
    exact absurd (huni j j' sched 0 hs hs') hne'
  | succ t' ih =>
    intro hs' hle
    rcases Nat.lt_or_ge t (t' + 1) with hlt | hge
    · cases hpt : preemption_time arr_seq sched (t' + 1)
      · have hprev := neg_pt_scheduled_at arr_seq hva PState huni sched hfrom hmust hvalid j' t' hs'
          (by rw [hpt]; rfl)
        obtain ⟨pt, hp, hin, hsp⟩ := ih hprev (by omega')
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
        exact ⟨pt, hp, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega', hsp⟩
      · exact ⟨t' + 1, hpt, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega', hs'⟩
    · have ht : t = t' + 1 := Nat.le_antisymm hle hge
      rw [ht] at hs
      exact absurd (huni j j' sched _ hs hs') hne'

end PreemptionTimes

section PreemptionFacts

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}

/-- In a valid schedule, jobs must arrive to execute (readiness implies
pendency). -/
private theorem must_arrive_of_valid [JobReady Job PState] (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (hvs : valid_schedule sched arr_seq) :
    jobs_must_arrive_to_execute sched := by
  intro j t hs
  have hp := ready_implies_pending sched j t (hvs.2 j t hs)
  unfold pending at hp
  simp only [Bool.and_eq_true] at hp
  exact hp.1

/-- Every non-preemptive segment begins with a preemption time. -/
theorem scheduling_of_any_segment_starts_with_preemption_time :
    uniprocessor_model PState →
    ∀ [JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ (j : Job) (t : instant), scheduled_at sched j t = true →
      ∃ pt : Nat, (decide (job_arrival j ≤ pt) && decide (pt ≤ t)) = true ∧
        preemption_time arr_seq sched pt = true ∧
        ∀ t' : Nat, (decide (pt ≤ t') && decide (t' ≤ t)) = true → scheduled_at sched j t' = true := by
  intro huni _ arr_seq hva sched hvs _ hvalid j t hs
  have hmust := must_arrive_of_valid arr_seq sched hvs
  have hfrom := hvs.1
  let P : Nat → Prop := fun n => n ≤ t ∧ ∀ t', n ≤ t' → t' ≤ t → scheduled_at sched j t' = true
  have hex : ∃ n, P n := ⟨t, Nat.le_refl t, fun t' h1 h2 => by
    have : t' = t := by omega'
    rw [this]; exact hs⟩
  classical
  have hm := Nat.find_spec hex
  have hmin := fun n => Nat.find_min' hex (m := n)
  obtain ⟨hmt, hall⟩ := hm
  have hsm : scheduled_at sched j (Nat.find hex) = true := hall _ (Nat.le_refl _) hmt
  have harrm : job_arrival j ≤ Nat.find hex := of_decide_eq_true (hmust j _ hsm)
  cases hk : Nat.find hex with
  | zero =>
    rw [hk] at hall harrm
    refine ⟨0, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega', ?_, ?_⟩
    · exact zero_is_pt arr_seq hva PState huni sched hfrom hmust hvalid
    · intro t' ht'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
      exact hall t' ht'.1 ht'.2
  | succ k =>
    rw [hk] at hall harrm hsm hmt
    have hns : (!scheduled_at sched j k) = true := by
      cases hsk : scheduled_at sched j k
      · rfl
      · exfalso
        have hPk : P k := ⟨by omega', fun t' h1 h2 => by
          rcases Nat.lt_or_ge t' (k + 1) with hlt | hge
          · have : t' = k := by omega'
            rw [this]; exact hsk
          · exact hall t' hge h2⟩
        have := hmin k hPk
        omega'
    refine ⟨k + 1, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega', ?_, ?_⟩
    · exact first_moment_is_pt arr_seq hva PState huni sched hfrom hmust hvalid j k
        (hfrom j _ hsm) hns hsm
    · intro t' ht'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
      exact hall t' ht'.1 ht'.2

/-- The preemption time that starts the segment lies between a known earlier
preemption time and the instant the job is scheduled. -/
theorem scheduling_of_any_segment_starts_with_preemption_time_continuously_sched :
    uniprocessor_model PState →
    ∀ [JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ (j : Job) (t1 t2 : Nat), t1 ≤ t2 → preemption_time arr_seq sched t1 = true →
      scheduled_at sched j t2 = true →
      ∃ ptst : Nat, (decide (t1 ≤ ptst) && decide (ptst ≤ t2)) = true ∧
        preemption_time arr_seq sched ptst = true ∧ scheduled_at sched j ptst = true := by
  intro huni _ arr_seq hva sched hvs _ hvalid j t1 t2 hle hpt hs
  obtain ⟨pt, hin, hppt, hcont⟩ :=
    scheduling_of_any_segment_starts_with_preemption_time huni arr_seq hva sched hvs hvalid j t2 hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
  rcases Nat.le_total t1 pt with h | h
  · exact ⟨pt, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega', hppt,
      hcont pt (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')⟩
  · exact ⟨t1, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega', hpt,
      hcont t1 (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')⟩

/-- A job scheduled throughout an interval in which it stays ready is only
interrupted by jobs of higher or equal priority. -/
theorem priority_higher_than_pending_job_priority :
    uniprocessor_model PState →
    ∀ [JobReady Job PState] (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ JLFP : JLFP_policy Job, reflexive_job_priorities JLFP →
      valid_schedule sched arr_seq →
      respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ (j : Job) (t1 t2 : instant), scheduled_at sched j t1 = true → scheduled_at sched j t2 = true →
      (∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true → job_ready sched j t = true) →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t2)) = true →
    ∀ jhp : Job, scheduled_at sched jhp t = true → JLFP.hep_job jhp j = true := by
  intro huni _ arr_seq hva sched _ hvalid JLFP hrefl hvs hresp j t1 t2 hs1 _ hready t ht jhp hsj
  have hmust := must_arrive_of_valid arr_seq sched hvs
  have hfrom := hvs.1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  rcases Nat.lt_or_ge t1 t with hlt | hge
  · by_cases heq : j = jhp
    · rw [← heq]; exact hrefl j
    · obtain ⟨pt, hpt, hin, hspt⟩ :=
        neq_scheduled_at_pt_continuous_sched arr_seq hva PState huni sched hfrom hmust hvalid j t1 hs1
          jhp t hsj (decide_eq_true heq) (Nat.le_of_lt hlt)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
      have hback : backlogged sched j pt = true := by
        unfold backlogged
        rw [hready pt (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')]
        cases hsp : scheduled_at sched j pt
        · rfl
        · exact absurd (huni j jhp sched pt hsp hspt) heq
      exact hresp j jhp pt (hfrom j t1 hs1) hpt hback hspt
  · have ht1 : t = t1 := by omega'
    rw [ht1] at hsj
    rw [huni jhp j sched t1 hsj hs1]
    exact hrefl j

end PreemptionFacts

end Prosa.Analysis.Facts.Model.Preemption
