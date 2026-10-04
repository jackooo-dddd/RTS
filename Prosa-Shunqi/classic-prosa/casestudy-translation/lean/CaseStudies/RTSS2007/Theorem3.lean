-- Case study: RTS_Papers/2007-RTSS-Theorem3/Theorem3.v
-- (Bertogna & Cirinei, RTSS 2007, Theorem 3); sha256 and elaborated contract:
-- classic-prosa/casestudy-translation/contracts/
import CaseStudies.CommonFp
import Prosa.Util.Sum
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Schedule.Global.Basic.Interference

/-!
Theorem 3 of RTSS 2007: if the sum over the other tasks of their interference on a job of `tsk`
in `[a_j, a_j + R)`, each truncated at `R - e_tsk + 1`, is below `m (R - e_tsk + 1)`, then `R` is
a response-time bound of `tsk` (Rocq module `ResponseTimeAnalysisFP`, section `Theorem3_07`).
The case study assumes that `j` has maximal total interference among the jobs of `tsk` and,
as a hypothesis named `Lemma1`, the equivalence between total interference and the truncated
task interferences.

Representation notes: `\sum_(t <- ts | t != tsk) F t` is
`sumFiltered ts.val (fun t => !decide (t = tsk)) F`; `PeanoNat.Nat.min` is `min`; the
section-local `Let`s are unfolded (`x tsk_other` is the task interference in
`[job_arrival j, job_arrival j + R)`, `response_time_bounded_by` is
`is_response_time_bound_of_task … sched`).  The hypothesis `H_constrained_deadlines` is
`constrained_deadline_model task_deadline task_period ts` in the source, i.e. with the period and
deadline arguments swapped relative to the definition; it is translated as written.  Binder lists
follow the Rocq contract.
-/

set_option linter.unusedVariables false

namespace CaseStudies.RTSS2007.Theorem3.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Util.Sum (sumFiltered)

universe u v

theorem Theorem3_07 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (tsk : sporadic_task) (H_tsk_in_ts : tsk ∈ ts)
    (R : time) (H_R_ge_cost : task_cost tsk ≤ R)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (H_constrained_deadlines : constrained_deadline_model task_deadline task_period ts.val)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (j_has_max_interference : ∀ j0 : Job, job_task j0 = tsk → arrives_in arr_seq j0 →
      total_interference job_arrival job_cost sched j0 (job_arrival j0) (job_arrival j0 + R) ≤
        total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R))
    (Lemma1 : ∀ (j0 : Job) (a b : time) (c : Nat),
      arrives_in arr_seq j0 → job_task j0 = tsk →
      (c ≤ total_interference job_arrival job_cost sched j0 a b ↔
        num_cpus * c ≤ sumFiltered ts.val (fun t => !decide (t = tsk))
          (fun t => min (task_interference job_arrival job_cost job_task sched j0 t a b) c))) :
    sumFiltered ts.val (fun t => !decide (t = tsk))
        (fun t => min (task_interference job_arrival job_cost job_task sched j t
            (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1)) <
      num_cpus * (R - task_cost tsk + 1) →
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  intro hlt
  -- by `Lemma1` (right to left, contrapositive), `j` suffers at most `R - e_tsk` interference
  have hj : total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R) ≤
      R - task_cost tsk := by
    by_contra h
    have h' := (Lemma1 j (job_arrival j) (job_arrival j + R) (R - task_cost tsk + 1) H_j_arrives
      H_job_of_tsk).mp (by omega)
    omega
  -- hence so does every job of `tsk`, which therefore completes within `R`
  intro j0 harr htsk
  by_contra hnc
  have hnc' : (!completed job_cost sched j0 (job_arrival j0 + R)) = true := by simpa using hnc
  have := CaseStudies.CommonFp.too_much_interference task_cost task_deadline job_arrival job_cost
    job_deadline job_task arr_seq H_valid_job_parameters sched H_jobs_must_arrive_to_execute tsk R
    H_R_ge_cost j0 harr htsk hnc'
  have := le_trans (j_has_max_interference j0 htsk harr) hj
  tomega

end CaseStudies.RTSS2007.Theorem3.ResponseTimeAnalysisFP
