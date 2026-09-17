-- Translated from: ../rt-proofs/classic/model/schedule/global/response_time.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule

namespace Prosa.Classic.Model.Schedule.Global.Response_time

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Schedule

namespace ResponseTime

section ResponseTimeBound

  variable {sporadic_task : Type _} [DecidableEq sporadic_task]
  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → sporadic_task)

  variable (arr_seq : arrival_sequence Job)

  variable {num_cpus : ℕ}
  variable (sched : schedule Job num_cpus)

  section Definitions

    variable (tsk : sporadic_task)

    variable (R : Time)

    def is_response_time_bound_of_task :=
      ∀ j,
        arrives_in arr_seq j →
        job_task j = tsk →
        completed job_cost sched j (job_arrival j + R)

  end Definitions

  section BasicLemmas

    variable (H_completed_jobs_dont_execute :
      completed_jobs_dont_execute job_cost sched)

    section SpecificJob

      variable (j : Job)
      variable (H_j_arrives : arrives_in arr_seq j)

      variable (R : Time)
      variable (response_time_bound :
        completed job_cost sched j (job_arrival j + R))
      include H_completed_jobs_dont_execute response_time_bound

      theorem service_after_job_rt_zero :
          ∀ t',
            t' ≥ job_arrival j + R →
            service_at sched j t' = 0 := by
        intro t' h_ge
        have h_comp : completed job_cost sched j t' :=
          completion_monotonic job_cost sched j H_completed_jobs_dont_execute
            (job_arrival j + R) t' h_ge response_time_bound
        have h_not_sched : ¬ scheduled sched j t' :=
          completed_implies_not_scheduled job_cost sched j H_completed_jobs_dont_execute t' h_comp
        exact (not_scheduled_no_service sched j t').mp h_not_sched

      theorem cumulative_service_after_job_rt_zero :
          ∀ t' t'',
            t' ≥ job_arrival j + R →
            ∑ t ∈ Finset.Ico t' t'', service_at sched j t = 0 := by
        intro t' t'' h_ge
        apply Finset.sum_eq_zero
        intro t ht
        rw [Finset.mem_Ico] at ht
        exact service_after_job_rt_zero job_arrival job_cost sched
          H_completed_jobs_dont_execute j R response_time_bound t (le_trans h_ge ht.1)

    end SpecificJob

    section AllJobs

      variable (tsk : sporadic_task)

      variable (R : Time)
      variable (response_time_bound :
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R)

      variable (j : Job)
      variable (H_j_arrives : arrives_in arr_seq j)
      variable (H_job_of_task : job_task j = tsk)
      include H_completed_jobs_dont_execute response_time_bound H_j_arrives H_job_of_task

      theorem service_after_task_rt_zero :
          ∀ t',
            t' ≥ job_arrival j + R →
            service_at sched j t' = 0 := by
        intro t' h_ge
        exact service_after_job_rt_zero job_arrival job_cost sched
          H_completed_jobs_dont_execute j R
          (response_time_bound j H_j_arrives H_job_of_task) t' h_ge

      theorem cumulative_service_after_task_rt_zero :
          ∀ t' t'',
            t' ≥ job_arrival j + R →
            ∑ t ∈ Finset.Ico t' t'', service_at sched j t = 0 := by
        intro t' t'' h_ge
        exact cumulative_service_after_job_rt_zero job_arrival job_cost sched
          H_completed_jobs_dont_execute j R
          (response_time_bound j H_j_arrives H_job_of_task) t' t'' h_ge

    end AllJobs

  end BasicLemmas

end ResponseTimeBound

end ResponseTime

end Prosa.Classic.Model.Schedule.Global.Response_time
