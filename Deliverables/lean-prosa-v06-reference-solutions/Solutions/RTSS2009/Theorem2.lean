import CaseStudies.RTSS2009.Theorem2
import Solutions.Support.Common

/-! Reference solution of benchmark task `2009-RTSS-Theorem2`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.RTSS2009.Theorem2.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Classic.Util.DivMod (div_floor div_ceil)
open Prosa.Util.Sum (sumSeq sumFiltered)

/-- LEAN_HELPER: each `R_phi_term` is at most the corresponding `R_term`. -/
theorem R_phi_term_le_R_term {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) (tsk : sporadic_task) (chi_min : Nat → time) (phi : time) (h : Nat) :
    R_phi_term task_period tsk chi_min phi h ≤ R_term task_period tsk chi_min h := by
  unfold R_phi_term R_term
  exact Nat.sub_le_sub_left (Nat.le_add_right _ _) _

/-- LEAN_HELPER: the running maxima compare termwise. -/
theorem max_R_phi_term_le_max_R_term {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) (tsk : sporadic_task) (chi_min : Nat → time) (phi : time) :
    ∀ h : Nat, max_R_phi_term task_period tsk chi_min phi h ≤ max_R_term task_period tsk chi_min h
  | 0 => by simp [max_R_phi_term, max_R_term]
  | h + 1 => by
      simp only [max_R_phi_term, max_R_term]
      exact max_le_max (max_R_phi_term_le_max_R_term task_period tsk chi_min phi h)
        (R_phi_term_le_R_term task_period tsk chi_min phi (h + 1))

/-- LEAN_HELPER: `max_R_term` is monotone in the number of jobs. -/
theorem max_R_term_mono {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time) (tsk : sporadic_task) (chi_min : Nat → time) :
    ∀ {a b : Nat}, a ≤ b → max_R_term task_period tsk chi_min a ≤ max_R_term task_period tsk chi_min b := by
  intro a b hab
  induction b with
  | zero => rw [Nat.le_zero.mp hab]
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · exact le_trans (ih (Nat.lt_succ_iff.mp h)) (by simp only [max_R_term]; exact le_max_left _ _)
      · rw [Nat.le_antisymm hab h]

theorem Theorem2 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts)
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks : ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
      higher_priority_task higher_eq_priority tsk hp_tsk = true → ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_response_time_bounds_ge_cost : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → task_cost hp_tsk ≤ R)
    (H_interfering_tasks_miss_no_deadlines : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (chi_min : Nat → time)
    (chi_min_spec : ∀ h : Nat, 0 < h → chi_is_least_solution task_cost task_period num_cpus tsk hp_bounds h (chi_min h))
    (Huniq_hp_bounds : hp_bounds.Nodup)
    (j : Job) (t0 : schedule Job num_cpus → Job → time)
    (t0_leq_arrival_time : t0 sched j ≤ job_arrival j)
    (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
      job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j) = true)
    (cpu_busy_during_t0_rk : ∀ t : Nat, (decide (t0 sched j ≤ t) && decide (t < job_arrival j)) = true →
      hp_busy job_task ts num_cpus sched higher_eq_priority tsk t)
    (t0_left_boundary : t0 sched j = 0 ∨ ¬ hp_busy job_task ts num_cpus sched higher_eq_priority tsk (t0 sched j - 1))
    (phi : time) (phi_is_defined : phi = job_arrival j - t0 sched j)
    (H_phi : Nat)
    (H_phi_is_minimal : 0 < H_phi ∧ H_phi_satisfy task_period tsk chi_min phi H_phi = true ∧
      ∀ x : Nat, 0 < x → H_phi_satisfy task_period tsk chi_min phi x = true → H_phi ≤ x)
    (H : Nat)
    (H_is_minimal : 0 < H ∧ H_satisfy task_period tsk chi_min H = true ∧
      ∀ x : Nat, 0 < x → H_satisfy task_period tsk chi_min x = true → H ≤ x)
    (Lemma5 : is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (max_R_phi_term task_period tsk chi_min phi H_phi)) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (max_R_term task_period tsk chi_min H) := by
  obtain ⟨hH0, hHs, _⟩ := H_is_minimal
  obtain ⟨_, _, hmin⟩ := H_phi_is_minimal
  have hsat : H_phi_satisfy task_period tsk chi_min phi H = true := by
    simp only [H_satisfy, Term, decide_eq_true_eq] at hHs
    simp only [H_phi_satisfy, decide_eq_true_eq]
    exact le_trans hHs (Nat.le_add_right _ _)
  have hle : H_phi ≤ H := hmin H hH0 hsat
  exact Solutions.Support.Common.rtb_mono
    (le_trans (max_R_phi_term_le_max_R_term task_period tsk chi_min phi H_phi) (max_R_term_mono task_period tsk chi_min hle))
    Lemma5

end CaseStudies.RTSS2009.Theorem2.ResponseTimeAnalysisFP

theorem Solutions.RTSS2009.Theorem2.solution : CaseStudies.RTSS2009.Theorem2.ResponseTimeAnalysisFP.Theorem2_statement.{u, v} :=
  @CaseStudies.RTSS2009.Theorem2.ResponseTimeAnalysisFP.Theorem2
