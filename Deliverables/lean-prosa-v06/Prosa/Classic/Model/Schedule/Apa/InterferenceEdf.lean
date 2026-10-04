-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/apa/interference_edf.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 118)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Model.Schedule.Apa.Interference
import Prosa.Classic.Model.Schedule.Apa.Platform

/-!
Interference under EDF in APA schedules (Rocq module `InterferenceEDF` of `model/schedule/apa/interference_edf.v`).

Representation notes (as in the accepted `classic/model/schedule/global/basic/interference_edf.v`): `x != 0` in
proposition position is `(!decide (x = 0)) = true`. Binder lists follow the Rocq contract (`num_cpus` is an explicit
section `Variable` here).
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Schedule.Apa.InterferenceEdf.InterferenceEDF

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity
open Prosa.Classic.Model.Schedule.Apa.Platform.Platform
open Prosa.Classic.Model.Schedule.Apa.Interference.Interference
open BigOperators

universe u v

theorem interference_under_edf_implies_shorter_deadlines {sporadic_task : Type u} [DecidableEq sporadic_task]
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (alpha : task_affinity sporadic_task num_cpus)
    (H_scheduler_uses_EDF :
      respects_JLFP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched alpha
        (EDF job_arrival job_deadline)) :
    ∀ (j j' : Job) (t1 t2 : time),
      arrives_in arr_seq j' →
      (!decide (job_interference job_arrival job_cost job_task sched alpha j' j t1 t2 = 0)) = true →
      job_arrival j + job_deadline j ≤ job_arrival j' + job_deadline j' := by
  intro j j' t1 t2 ARR' INTERF
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at INTERF
  unfold job_interference at INTERF
  obtain ⟨t, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero INTERF
  obtain ⟨cpu, _, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  cases hb : backlogged job_arrival job_cost sched j' t
  · simp [hb] at hne'
  cases hc : can_execute_on alpha (job_task j') cpu
  · simp [hc] at hne'
  cases hs : scheduled_on sched j cpu t
  · simp [hs] at hne'
  have := H_scheduler_uses_EDF j' j cpu t ARR' hb hs hc
  simpa [EDF] using this

end Prosa.Classic.Model.Schedule.Apa.InterferenceEdf.InterferenceEDF
