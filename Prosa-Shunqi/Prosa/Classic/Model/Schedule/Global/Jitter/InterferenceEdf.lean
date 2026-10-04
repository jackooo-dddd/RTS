-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/global/jitter/interference_edf.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 139)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Global.Jitter.Interference
import Prosa.Classic.Model.Schedule.Global.Jitter.Platform

/-!
Interference under EDF in global schedules with release jitter (Rocq module `InterferenceEDF` of
`classic/model/schedule/global/jitter/interference_edf.v`).

Representation notes: `x != 0` in proposition position is `(!decide (x = 0)) = true`.
Binder lists follow the Rocq contract (here `arr_seq` and `num_cpus` are explicit). The proof follows the accepted
basic translation (`Prosa.Classic.Model.Schedule.Global.Basic.InterferenceEdf`), with the jitter-aware `backlogged`.
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Schedule.Global.Jitter.InterferenceEdf.InterferenceEDF

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule hiding pending backlogged
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Jitter.Interference.Interference
open BigOperators

universe v

theorem interference_under_edf_implies_shorter_deadlines {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_scheduler_uses_EDF :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline)) :
    ∀ (j j' : Job) (t1 t2 : time),
      arrives_in arr_seq j →
      arrives_in arr_seq j' →
      (!decide (job_interference job_arrival job_cost job_jitter sched j' j t1 t2 = 0)) = true →
      job_arrival j + job_deadline j ≤ job_arrival j' + job_deadline j' := by
  intro j j' t1 t2 _ ARR2 INTERF
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at INTERF
  unfold job_interference at INTERF
  obtain ⟨t, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero INTERF
  obtain ⟨cpu, _, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  cases hb : backlogged job_arrival job_cost job_jitter sched j' t
  · simp [hb] at hne'
  cases hs : scheduled_on sched j cpu t
  · simp [hs] at hne'
  have SCHED : scheduled sched j t = true := by
    simp only [scheduled, List.any_eq_true, List.mem_finRange, true_and]
    exact ⟨cpu, hs⟩
  have := H_scheduler_uses_EDF j' j t ARR2 hb SCHED
  simpa [EDF] using this

end Prosa.Classic.Model.Schedule.Global.Jitter.InterferenceEdf.InterferenceEDF
