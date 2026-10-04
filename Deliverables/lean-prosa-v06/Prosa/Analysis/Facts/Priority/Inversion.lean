-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/priority/inversion.v

import Prosa.Analysis.Definitions.PriorityInversion
import Prosa.Analysis.Facts.Model.Scheduled

namespace Prosa.Analysis.Facts.Priority.Inversion

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Priority.Definitions
open Prosa.Model.Schedule.Scheduled
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Facts.Model.Scheduled

/-! Representation notes: a Boolean in `Prop` position is `= true`;
`~~ b` is `!b`; `exists2 x, P x & Q x` is `∃ x, P x ∧ Q x`; the source
`reflect` view is the accepted informative `BoolReflect` family. Binder
orders follow the elaborated types (hypotheses unused by a statement are
absent, as in the elaborated source). -/

section PI

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job)

/-- A scheduled job incurs no priority inversion. -/
theorem sched_itself_implies_no_priority_inversion :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ [JLFP : JLFP_policy Job] (j : Job) (t : instant),
          scheduled_at sched j t = true → (!priority_inversion arr_seq sched j t) = true := by
  intro hva sched hfrom hmust _ j t hs
  have hmem := scheduled_jobs_at_iff arr_seq hva sched hfrom hmust j t
  simp [priority_inversion, hmem, hs]

/-- Priority inversion implies that some job is scheduled. -/
theorem priority_inversion_scheduled_at :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ [JLFP : JLFP_policy Job] (j : Job) (t : instant),
          priority_inversion arr_seq sched j t = true → ∃ j' : Job, scheduled_at sched j' t = true := by
  intro hva sched hfrom hmust _ j t hpi
  simp only [priority_inversion, Bool.and_eq_true, List.any_eq_true] at hpi
  obtain ⟨_, jlp, hin, _⟩ := hpi
  refine ⟨jlp, ?_⟩
  have hmem := scheduled_jobs_at_iff arr_seq hva sched hfrom hmust jlp t
  rw [← hmem]; simpa using hin

/-- There is no priority inversion when the processor is idle. -/
theorem no_priority_inversion_when_idle :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ [JLFP : JLFP_policy Job] (j : Job) (t : instant),
          is_idle arr_seq sched t = true → (!priority_inversion arr_seq sched j t) = true := by
  intro _ sched _ _ _ j t hidle
  simp only [is_idle, List.isEmpty_iff] at hidle
  simp [priority_inversion, hidle]

/-- LEAN_HELPER: on a uniprocessor, the scheduled jobs are exactly the
scheduled job. -/
private theorem scheduled_jobs_at_single (hva : valid_arrival_sequence arr_seq)
    (sched : schedule PState) (hfrom : jobs_come_from_arrival_sequence sched arr_seq)
    (hmust : jobs_must_arrive_to_execute sched) (huni : uniprocessor_model PState)
    (t : instant) (j' : Job) (hs : scheduled_at sched j' t = true) :
    scheduled_jobs_at arr_seq sched t = [j'] := by
  have hin : j' ∈ scheduled_jobs_at arr_seq sched t := by
    have hmem := scheduled_jobs_at_iff arr_seq hva sched hfrom hmust j' t
    rw [hs] at hmem; simpa using hmem
  rcases scheduled_jobs_at_uni_cases arr_seq hva sched hfrom hmust huni t with h | ⟨k, h⟩
  · simp only [decide_eq_true_eq] at h; rw [h] at hin; simp at hin
  · simp only [decide_eq_true_eq] at h; rw [h] at hin ⊢
    simp only [List.mem_singleton] at hin; rw [hin]

/-- On a uniprocessor, priority inversion is decided by the scheduled job. -/
theorem priority_inversion_hep_job :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
        ∀ j : Job, uniprocessor_model PState →
        ∀ (t : instant) (j' : Job),
          scheduled_at sched j' t = true → priority_inversion arr_seq sched j t = !hep_job j' j := by
  intro hva sched hfrom hmust JLFP hrefl j huni t j' hs
  rw [priority_inversion, scheduled_jobs_at_single arr_seq hva sched hfrom hmust huni t j' hs]
  by_cases h : j = j'
  · subst h; simp [hrefl j]
  · simp [h]

/-- A scheduled higher-or-equal-priority job rules out priority inversion. -/
theorem no_priority_inversion_when_hep_job_scheduled :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
        ∀ j : Job, uniprocessor_model PState →
        ∀ (t : instant) (j' : Job),
          scheduled_at sched j' t = true → hep_job j' j = true →
            (!priority_inversion arr_seq sched j t) = true := by
  intro hva sched hfrom hmust JLFP hrefl j huni t j' hs hhep
  rw [priority_inversion_hep_job arr_seq hva sched hfrom hmust hrefl j huni t j' hs, hhep]
  rfl

/-- Reflection view of priority inversion on uniprocessors. -/
def uni_priority_inversion_P :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
        ∀ j : Job, uniprocessor_model PState →
        ∀ t : instant,
          BoolReflect (∃ j' : Job, scheduled_at sched j' t = true ∧ (!hep_job j' j) = true)
            (priority_inversion arr_seq sched j t) := by
  intro hva sched hfrom hmust JLFP hrefl j huni t
  cases hb : priority_inversion arr_seq sched j t with
  | true =>
    refine BoolReflect.isTrue ?_
    obtain ⟨j', hs⟩ := priority_inversion_scheduled_at arr_seq hva sched hfrom hmust j t hb
    refine ⟨j', hs, ?_⟩
    rw [← priority_inversion_hep_job arr_seq hva sched hfrom hmust hrefl j huni t j' hs]
    exact hb
  | false =>
    refine BoolReflect.isFalse ?_
    rintro ⟨j', hs, hn⟩
    rw [← priority_inversion_hep_job arr_seq hva sched hfrom hmust hrefl j huni t j' hs, hb] at hn
    exact Bool.false_ne_true hn

end PI

/-- Cumulative priority inversion splits at any intermediate point. -/
theorem cumulative_priority_inversion_cat {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    [JLFP : JLFP_policy Job] (j : Job) :
    ∀ t_mid t1 t2 : instant, t1 ≤ t_mid → t_mid ≤ t2 →
      cumulative_priority_inversion arr_seq sched j t1 t2 =
        cumulative_priority_inversion arr_seq sched j t1 t_mid +
          cumulative_priority_inversion arr_seq sched j t_mid t2 := by
  intro t_mid t1 t2 h1 h2
  unfold cumulative_priority_inversion
  exact (Finset.sum_Ico_consecutive _ h1 h2).symm

end Prosa.Analysis.Facts.Priority.Inversion
