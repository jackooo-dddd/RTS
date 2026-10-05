-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/readiness_interference.v

import Prosa.Analysis.Definitions.ReadinessInterference
import Prosa.Analysis.Definitions.Interference
import Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware
import Prosa.Analysis.Facts.Behavior.Service

namespace Prosa.Analysis.Facts.ReadinessInterference

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions
open Prosa.Analysis.Definitions.Service
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Definitions.ReadinessInterference
open Prosa.Analysis.Facts.Behavior.Service

/-! Facts about readiness interference.

Binders follow the elaborated source types: each statement takes the section inputs and hypotheses it uses, in
their elaborated order (the unused validity of the arrival sequence is absent). Representation: a Boolean in `Prop`
position is `= true`; `~~ b` is `(!b) = true`. -/

section ReadinessInterference

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job} [JobReady Job PState]

/-- If no higher-or-equal-priority job is ready, no other higher-or-equal-priority job interferes. -/
theorem no_hep_ready_implies_no_another_hep_interference (arr_seq : arrival_sequence Job)
    (sched : schedule PState) :
    valid_schedule sched arr_seq →
    ∀ [JLFP_policy Job] (j : Job) (t : instant),
      (!some_hep_job_ready arr_seq sched j t) = true →
      (!another_hep_job_interference arr_seq sched j t) = true := by
  intro hvalid _ j t hno
  have hnone : some_hep_job_ready arr_seq sched j t = false := by simpa using hno
  unfold another_hep_job_interference
  cases hany : (served_jobs_at arr_seq sched t).any (fun x => another_hep_job x j) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨jo, hjo, hhep⟩ := List.any_eq_true.mp hany
    unfold served_jobs_at at hjo
    have hjo' := List.mem_filter.mp hjo
    have hserv : 0 < service_at sched jo t := by
      have := hjo'.2
      unfold receives_service_at at this
      exact of_decide_eq_true this
    have hsched := service_at_implies_scheduled_at sched jo t hserv
    have hready := hvalid.2 jo t hsched
    have hhep' : hep_job jo j = true := (Bool.and_eq_true_iff.mp hhep).1
    have hsome : some_hep_job_ready arr_seq sched j t = true := by
      unfold some_hep_job_ready
      exact List.any_eq_true.mpr ⟨jo, List.mem_filter.mpr ⟨hjo'.1, hhep'⟩, hready⟩
    rw [hsome] at hnone
    exact absurd hnone (by decide)

/-- If no higher-or-equal-priority job is ready, there is no readiness-aware service inversion. -/
theorem no_hep_ready_implies_no_service_inversion (arr_seq : arrival_sequence Job)
    (sched : schedule PState) [JLFP_policy Job] (j : Job) (t : instant) :
    (!some_hep_job_ready arr_seq sched j t) = true →
      (!Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.service_inversion arr_seq sched j t) = true := by
  intro hno
  have hnone : some_hep_job_ready arr_seq sched j t = false := by simpa using hno
  unfold Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.service_inversion
  rw [hnone]
  rfl

end ReadinessInterference

end Prosa.Analysis.Facts.ReadinessInterference
