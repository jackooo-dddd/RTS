-- Translated from: ../rt-proofs/classic/model/schedule/uni/response_time.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Uni.Schedule

namespace Prosa.Classic.Model.Schedule.Uni.Response_time

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

namespace ResponseTime

section ResponseTimeBound

  variable {sporadic_task : Type _} [DecidableEq sporadic_task]
  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → sporadic_task)

  variable (arr_seq : arrival_sequence Job)

  variable (sched : schedule Job)

  section Job

    variable (j : Job)

    variable (R : Time)

    def is_response_time_bound_of_job :=
      completed_by job_cost sched j (job_arrival j + R)

  end Job

  section Task

    variable (tsk : sporadic_task)

    variable (R : Time)

    def is_response_time_bound_of_task :=
      ∀ j,
        arrives_in arr_seq j →
        job_task j = tsk →
        is_response_time_bound_of_job job_arrival job_cost sched j R

  end Task

end ResponseTimeBound

section BasicLemmas

  variable {sporadic_task : Type _} [DecidableEq sporadic_task]
  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → sporadic_task)

  variable (arr_seq : arrival_sequence Job)

  variable (sched : schedule Job)

  variable (H_completed_jobs_dont_execute :
    completed_jobs_dont_execute job_cost sched)

  include H_completed_jobs_dont_execute

  section SpecificJob

    variable (j : Job)

    variable (R : Time)
    variable (response_time_bound :
      is_response_time_bound_of_job job_arrival job_cost sched j R)

    include response_time_bound

    theorem service_after_job_rt_zero :
      ∀ t',
        t' ≥ job_arrival j + R →
        service_at sched j t' = 0 := by
      intro t' ht'
      have hcomp : completed_by job_cost sched j t' :=
        completion_monotonic job_cost sched j _ t' ht' response_time_bound
      have h1 : service sched j (t' + 1) ≤ job_cost j := H_completed_jobs_dont_execute j (t' + 1)
      have h3 : job_cost j ≤ service sched j t' := hcomp
      -- service sched j (t'+1) = service_during sched j 0 (t'+1) = service_during sched j 0 t' + service_at sched j t'
      -- = service sched j t' + service_at sched j t'
      -- So: service sched j t' + service_at sched j t' ≤ job_cost j ≤ service sched j t'
      -- Hence service_at sched j t' = 0
      suffices h : service sched j t' + service_at sched j t' ≤ service sched j t' by omega
      calc service sched j t' + service_at sched j t'
          = service sched j (t' + 1) := by
            simp only [service, service_during]
            rw [Finset.sum_Ico_succ_top (Nat.zero_le t')]
        _ ≤ job_cost j := h1
        _ ≤ service sched j t' := h3

    theorem cumulative_service_after_job_rt_zero :
      ∀ t' t'',
        t' ≥ job_arrival j + R →
        ∑ t ∈ Finset.Ico t' t'', service_at sched j t = 0 := by
      intro t' t'' ht'
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_Ico] at hi
      apply service_after_job_rt_zero job_arrival job_cost sched H_completed_jobs_dont_execute j R response_time_bound
      simp only [Time] at *; omega

  end SpecificJob

  section AllJobs

    variable (tsk : sporadic_task)

    variable (R : Time)
    variable (response_time_bound :
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R)

    include response_time_bound

    variable (j : Job)
    variable (H_from_arrival_sequence : arrives_in arr_seq j)
    variable (H_job_of_task : job_task j = tsk)

    include H_from_arrival_sequence H_job_of_task

    theorem service_after_task_rt_zero :
      ∀ t',
        t' ≥ job_arrival j + R →
        service_at sched j t' = 0 := by
      intro t' ht'
      exact service_after_job_rt_zero job_arrival job_cost sched H_completed_jobs_dont_execute j R
        (response_time_bound j H_from_arrival_sequence H_job_of_task) t' ht'

    theorem cumulative_service_after_task_rt_zero :
      ∀ t' t'',
        t' ≥ job_arrival j + R →
        ∑ t ∈ Finset.Ico t' t'', service_at sched j t = 0 := by
      intro t' t'' ht'
      exact cumulative_service_after_job_rt_zero job_arrival job_cost sched H_completed_jobs_dont_execute j R
        (response_time_bound j H_from_arrival_sequence H_job_of_task) t' t'' ht'

  end AllJobs

end BasicLemmas

end ResponseTime

end Prosa.Classic.Model.Schedule.Uni.Response_time
