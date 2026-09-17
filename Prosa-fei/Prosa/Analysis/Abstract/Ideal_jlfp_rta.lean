-- Translated from: ../rt-proofs/analysis/abstract/ideal_jlfp_rta.v
import Prosa.Analysis.Definitions.Priority_inversion
import Prosa.Analysis.Abstract.Abstract_seq_rta
import Prosa.Model.Processor.Ideal
import Prosa.Model.Readiness.Basic
import Prosa.Analysis.Facts.Model.Service_of_jobs
import Prosa.Analysis.Facts.Behavior.Arrivals
import Prosa.Analysis.Facts.Model.Workload

namespace Prosa.Analysis.Abstract.Ideal_jlfp_rta

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Classes
open Prosa.Model.Processor.Ideal
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.Service_of_jobs
open Prosa.Analysis.Definitions.Priority_inversion
open Prosa.Analysis.Definitions.Busy_interval
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.Abstract_seq_rta
open Prosa.Analysis.Facts.Behavior.Completion

set_option linter.dupNamespace false

section JLFPInstantiation

variable {Task : TaskType}
variable [TaskCost Task]
variable [DecidableEq Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)
variable (H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq)

variable (sched : schedule (processor_state Job))
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable (H_sequential_tasks : Prosa.Model.Task.Sequentiality.sequential_tasks
  (Task := Task) (Job := Job) sched)

variable [JLFP_policy Job]

attribute [local instance] JLFP_to_JLDP

variable (H_priority_is_reflexive : reflexive_priorities (Job := Job))
variable (H_priority_is_transitive : transitive_priorities (Job := Job))

variable (H_JLFP_respects_sequential_tasks :
  policy_respects_sequential_tasks (Task := Task) (Job := Job))

variable (tsk : Task)

private noncomputable def another_hep_job (j1 j2 : Job) : Bool :=
  hep_job j1 j2 && (j1 != j2)

private noncomputable def hep_job_from_another_task (j1 j2 : Job) : Bool :=
  hep_job j1 j2 && (job_task (Task := Task) j1 != job_task j2)

noncomputable def is_interference_from_another_hep_job (j : Job) (t : instant) : Bool :=
  match sched t with
  | some jhp => another_hep_job jhp j
  | none => false

noncomputable def is_interference_from_hep_job_from_another_task (j : Job) (t : instant) : Bool :=
  match sched t with
  | some jhp => hep_job_from_another_task (Task := Task) jhp j
  | none => false

noncomputable def interfering_workload_of_hep_jobs (j : Job) (t : instant) : Nat :=
  ((arrivals_at arr_seq t).filter (fun jhp => another_hep_job jhp j)).map (fun jhp => job_cost jhp) |>.sum

noncomputable def interference (j : Job) (t : instant) : Bool :=
  is_priority_inversion sched j t || is_interference_from_another_hep_job sched j t

noncomputable def interfering_workload (j : Job) (t : instant) : Nat :=
  (is_priority_inversion sched j t).toNat + interfering_workload_of_hep_jobs arr_seq j t

noncomputable def cumulative_priority_inversion (j : Job) (t1 t2 : instant) : Nat :=
  Finset.sum (Finset.Ico t1 t2) (fun t => (is_priority_inversion sched j t).toNat)

private noncomputable def cumulative_interference_from_other_hep_jobs
    (j : Job) (t1 t2 : instant) : Nat :=
  Finset.sum (Finset.Ico t1 t2) (fun t => (is_interference_from_another_hep_job sched j t).toNat)

noncomputable def cumulative_interference_from_hep_jobs_from_other_tasks
    (j : Job) (t1 t2 : instant) : Nat :=
  Finset.sum (Finset.Ico t1 t2) (fun t => (is_interference_from_hep_job_from_another_task (Task := Task) sched j t).toNat)

private noncomputable def cumulative_interference (j : Job) (t1 t2 : instant) : Nat :=
  Finset.sum (Finset.Ico t1 t2) (fun t => (interference sched j t).toNat)

private noncomputable def cumulative_interfering_workload_of_hep_jobs
    (j : Job) (t1 t2 : instant) : Nat :=
  Finset.sum (Finset.Ico t1 t2) (fun t => interfering_workload_of_hep_jobs arr_seq j t)

private noncomputable def cumulative_interfering_workload
    (j : Job) (t1 t2 : instant) : Nat :=
  Finset.sum (Finset.Ico t1 t2) (fun t => interfering_workload arr_seq sched j t)

private noncomputable def workload_of_other_hep_jobs
    (j : Job) (t1 t2 : instant) : work :=
  workload_of_jobs (fun jhp => another_hep_job jhp j)
    (arrivals_between arr_seq t1 t2)

private noncomputable def service_of_hep_jobs_from_other_tasks
    (j : Job) (t1 t2 : instant) : work :=
  service_of_jobs sched (fun jhp => hep_job_from_another_task (Task := Task) jhp j)
    (arrivals_between arr_seq t1 t2) t1 t2

private noncomputable def service_of_other_hep_jobs
    (j : Job) (t1 t2 : instant) : work :=
  service_of_jobs sched (fun jhp => another_hep_job jhp j)
    (arrivals_between arr_seq t1 t2) t1 t2

-- Bridge lemmas between concrete and abstract busy intervals
-- Translated from: ../rt-proofs/analysis/abstract/ideal_jlfp_rta.v

variable (j : Job)

theorem cumulative_interference_split (t1 t2 : instant) :
    cumulative_interference sched j t1 t2 =
    cumulative_priority_inversion sched j t1 t2 +
    cumulative_interference_from_other_hep_jobs sched j t1 t2 := by
  simp only [cumulative_interference, cumulative_priority_inversion,
    cumulative_interference_from_other_hep_jobs, ← Finset.sum_add_distrib]
  congr 1; ext t
  simp only [interference, is_priority_inversion, is_interference_from_another_hep_job, another_hep_job]
  cases sched t with
  | none => simp
  | some s =>
    cases h : hep_job s j <;> simp [h]

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_tasks
  H_priority_is_reflexive H_priority_is_transitive
  H_JLFP_respects_sequential_tasks in
theorem cumulative_task_interference_split
    (t1 t2 upp_t : instant)
    (TSK : job_task (Task := Task) j = tsk)
    (ARR : j ∈ arrivals_before arr_seq upp_t)
    (NCOMPL : ¬ completed_by sched j t2) :
    Prosa.Analysis.Abstract.Abstract_seq_rta.cumul_task_interference
      arr_seq sched tsk (interference sched) upp_t t1 t2 =
    cumulative_priority_inversion sched j t1 t2 +
    cumulative_interference_from_hep_jobs_from_other_tasks (Task := Task) sched j t1 t2 := by
  simp only [Prosa.Analysis.Abstract.Abstract_seq_rta.cumul_task_interference,
    cumulative_priority_inversion, cumulative_interference_from_hep_jobs_from_other_tasks,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  simp only [Prosa.Analysis.Abstract.Abstract_seq_rta.task_interference_received_before,
    is_priority_inversion, is_interference_from_hep_job_from_another_task,
    hep_job_from_another_task, interference, is_interference_from_another_hep_job, another_hep_job]
  cases hsched : sched t with
  | none => simp [Prosa.Analysis.Definitions.Task_schedule.task_scheduled_at, hsched]
  | some s =>
    simp only [Prosa.Analysis.Definitions.Task_schedule.task_scheduled_at, hsched]
    cases hp : hep_job s j
    · -- Case: hep_job s j = false (priority inversion)
      simp only [hp, Bool.false_and, Bool.toNat_false, Nat.add_zero, Bool.not_true, Bool.toNat_true]
      -- RHS = 1. LHS: need to show task not scheduled or contradiction
      by_cases htsk : job_task (Task := Task) s = tsk
      · -- s is from same task as j: contradiction via sequential_tasks
        exfalso
        have h_sched_s : scheduled_at sched s t := by
          rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def]; simp [hsched]
        have h_arr_lt : job_arrival j < job_arrival s := by
          by_contra h_neg; push_neg at h_neg
          have := H_JLFP_respects_sequential_tasks s j (htsk.trans TSK.symm) h_neg
          simp [this] at hp
        have h_same : same_task (Task := Task) j s = true := by
          simp [same_task, TSK, htsk]
        have h_comp := H_sequential_tasks j s t h_same h_arr_lt h_sched_s
        exact NCOMPL (completion_monotonic sched j t t2 (Nat.le_of_lt ht.2) h_comp)
      · -- s is from different task: tsk not scheduled, any is true
        have hbeq : (job_task (Task := Task) s == tsk) = false := beq_eq_false_iff_ne.mpr htsk
        simp only [hbeq, Bool.not_false, Bool.true_and]
        -- Show j has interference at t
        have h_j_in : j ∈ Prosa.Model.Task.Arrivals.task_arrivals_before arr_seq tsk upp_t := by
          simp only [Prosa.Model.Task.Arrivals.task_arrivals_before,
            Prosa.Model.Task.Arrivals.task_arrivals_between]
          rw [List.mem_filter]
          exact ⟨ARR, by simp [TSK]⟩
        have h_any : (Prosa.Model.Task.Arrivals.task_arrivals_before arr_seq tsk upp_t).any
            (fun jj => (!hep_job s jj) || (hep_job s jj && (s != jj))) = true :=
          List.any_eq_true.mpr ⟨j, h_j_in, by simp [hp]⟩
        simp [h_any]
    · -- Case: hep_job s j = true
      simp only [hp, Bool.not_false, Bool.true_and, Bool.toNat_false, Nat.zero_add]
      by_cases htsk2 : job_task (Task := Task) s = job_task j
      · -- Same task: both sides 0
        have hbeq : (job_task (Task := Task) s == tsk) = true := by rw [beq_iff_eq, htsk2, TSK]
        have hne : (job_task (Task := Task) s != job_task j) = false := by
          simp [bne_iff_ne, htsk2]
        simp [hbeq, hne]
      · -- Different task
        have hne : (job_task (Task := Task) s != job_task j) = true := by
          simp [bne_iff_ne, htsk2]
        simp only [hne, Bool.toNat_true]
        have htsk3 : job_task (Task := Task) s ≠ tsk := by intro h; exact htsk2 (h.trans TSK.symm)
        have hbeq : (job_task (Task := Task) s == tsk) = false := beq_eq_false_iff_ne.mpr htsk3
        simp only [hbeq, Bool.not_false, Bool.true_and]
        have s_ne_j : s ≠ j := by intro h; subst h; exact htsk2 rfl
        have h_j_in : j ∈ Prosa.Model.Task.Arrivals.task_arrivals_before arr_seq tsk upp_t := by
          simp only [Prosa.Model.Task.Arrivals.task_arrivals_before,
            Prosa.Model.Task.Arrivals.task_arrivals_between]
          rw [List.mem_filter]
          exact ⟨ARR, by simp [TSK]⟩
        have h_any : (Prosa.Model.Task.Arrivals.task_arrivals_before arr_seq tsk upp_t).any
            (fun jj => (!hep_job s jj) || (hep_job s jj && (s != jj))) = true :=
          List.any_eq_true.mpr ⟨j, h_j_in, by simp [hp, s_ne_j]⟩
        simp [h_any]

include H_arrival_times_are_consistent H_arr_seq_is_a_set in
private theorem workload_equiv (t1 t2 : instant) :
    cumulative_interfering_workload_of_hep_jobs arr_seq j t1 t2 =
    workload_of_other_hep_jobs arr_seq j t1 t2 := by
  by_cases hle : t1 ≤ t2
  · obtain ⟨k, rfl⟩ : ∃ k, t2 = t1 + k := ⟨t2 - t1, (Nat.add_sub_cancel' hle).symm⟩
    clear hle
    induction k with
    | zero =>
      simp only [Nat.add_zero]
      unfold cumulative_interfering_workload_of_hep_jobs
      rw [Finset.Ico_self, Finset.sum_empty]
      unfold workload_of_other_hep_jobs workload_of_jobs arrivals_between
              arrivals_at Prosa.Util.Notation.bigCat
      simp
    | succ n ih =>
      have h1 : t1 + (n + 1) = (t1 + n) + 1 := by ring
      rw [h1]
      unfold cumulative_interfering_workload_of_hep_jobs at ih ⊢
      rw [Finset.sum_Ico_succ_top (Nat.le_add_right t1 n), ih]
      -- RHS: workload_of_other_hep_jobs arr_seq j t1 (t1 + n + 1)
      -- Split via workload_of_jobs_cat
      unfold workload_of_other_hep_jobs at *
      rw [Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_cat arr_seq (t1 + n) t1 (t1 + n + 1)
            (fun jhp => another_hep_job jhp j)
            ⟨Nat.le_add_right t1 n, Nat.le_succ (t1 + n)⟩]
      congr 1
      -- Show: interfering_workload_of_hep_jobs at (t1+n) = workload at arrivals_between (t1+n) (t1+n+1)
      unfold interfering_workload_of_hep_jobs workload_of_jobs arrivals_between
              arrivals_at Prosa.Util.Notation.bigCat
      conv_rhs => rw [show t1 + n + 1 - (t1 + n) = 1 from Nat.add_sub_cancel_left (t1 + n) 1]
      simp
  · push_neg at hle
    unfold cumulative_interfering_workload_of_hep_jobs
    rw [Finset.Ico_eq_empty (not_lt.mpr (Nat.le_of_lt hle)), Finset.sum_empty]
    unfold workload_of_other_hep_jobs workload_of_jobs arrivals_between
            arrivals_at Prosa.Util.Notation.bigCat
    rw [show t2 - t1 = 0 from Nat.sub_eq_zero_of_le (Nat.le_of_lt hle)]
    simp

include H_arrival_times_are_consistent H_arr_seq_is_a_set in
theorem instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs
    (t1 t2 : instant) :
    cumulative_interfering_workload_of_hep_jobs arr_seq j t1 t2 =
    workload_of_other_hep_jobs arr_seq j t1 t2 :=
  workload_equiv arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set j t1 t2

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute in
private theorem service_equiv (t1 t0 : instant)
    (H_qt : Prosa.Analysis.Definitions.Busy_interval.quiet_time arr_seq sched j t1) :
    cumulative_interference_from_other_hep_jobs sched j t1 t0 =
    service_of_other_hep_jobs arr_seq sched j t1 t0 := by
  simp only [service_of_other_hep_jobs, service_of_jobs, service_during,
             cumulative_interference_from_other_hep_jobs]
  -- Swap sum order: ∑_job ∑_time → ∑_time ∑_job
  have h_swap : ∀ (l : List Job),
      (l.map (fun jj => ∑ t' ∈ Finset.Ico t1 t0, service_at sched jj t')).sum =
      ∑ t' ∈ Finset.Ico t1 t0, (l.map (fun jj => service_at sched jj t')).sum := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [ih, ← Finset.sum_add_distrib]
  rw [h_swap]
  apply Finset.sum_congr rfl
  intro tt htt
  rw [Finset.mem_Ico] at htt
  simp only [is_interference_from_another_hep_job, another_hep_job]
  cases hsched : sched tt with
  | none =>
    simp only [Bool.toNat_false]
    symm; apply List.sum_eq_zero
    intro x hx; rw [List.mem_map] at hx
    obtain ⟨jhp, _, rfl⟩ := hx
    apply Prosa.Analysis.Facts.Behavior.Service.not_scheduled_implies_no_service
    rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def]; simp [hsched]
  | some jo =>
    simp only []
    cases hprio : (hep_job jo j && (jo != j))
    · -- jo does NOT satisfy the predicate: both sides are 0
      simp only [Bool.toNat_false]
      symm; apply List.sum_eq_zero
      intro x hx; rw [List.mem_map] at hx
      obtain ⟨jhp, hjhp_mem, rfl⟩ := hx
      rw [List.mem_filter] at hjhp_mem
      have h_eq_or_ne : jo = jhp ∨ jo ≠ jhp := eq_or_ne jo jhp
      cases h_eq_or_ne with
      | inl heq =>
        subst heq; rw [hjhp_mem.2] at hprio; simp at hprio
      | inr hne =>
        apply Prosa.Analysis.Facts.Behavior.Service.not_scheduled_implies_no_service
        rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def]; simp [hsched, hne]
    · -- jo satisfies predicate: both sides = 1
      simp only [Bool.toNat_true]
      have h_sched_jo : scheduled_at sched jo tt = true := by
        rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def]; simp [hsched]
      have hjo_arrives : arrives_in arr_seq jo :=
        H_jobs_come_from_arrival_sequence jo tt h_sched_jo
      have hjo_arr_le : job_arrival jo ≤ tt :=
        H_jobs_must_arrive_to_execute jo tt h_sched_jo
      have hjo_arr_lt : job_arrival jo < t0 := Nat.lt_of_le_of_lt hjo_arr_le htt.2
      have hjo_arr_ge : t1 ≤ job_arrival jo := by
        by_contra h_neg; push_neg at h_neg
        have hprio_hp : hep_job jo j = true := by
          simp only [Bool.and_eq_true] at hprio; exact hprio.1
        have hcompl : completed_by sched jo t1 := H_qt jo hjo_arrives hprio_hp h_neg
        have h_not_sched := completed_implies_not_scheduled sched jo
          H_completed_jobs_dont_execute tt (completion_monotonic sched jo t1 tt htt.1 hcompl)
        rw [h_not_sched] at h_sched_jo; exact absurd h_sched_jo (by simp)
      have hjo_in : jo ∈ arrivals_between arr_seq t1 t0 :=
        Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
          arr_seq H_arrival_times_are_consistent jo t1 t0
          hjo_arrives ⟨hjo_arr_ge, hjo_arr_lt⟩
      have hjo_in_filtered : jo ∈ (arrivals_between arr_seq t1 t0).filter
          (fun jhp => another_hep_job jhp j) :=
        List.mem_filter.mpr ⟨hjo_in, hprio⟩
      -- service_at for jo = 1, for others = 0
      have h_sa : ∀ jhp, service_at sched jhp tt = if jhp = jo then 1 else 0 := by
        intro jhp
        by_cases h : jhp = jo
        · subst h
          rw [Prosa.Analysis.Facts.Model.Ideal_schedule.service_at_is_scheduled_at,
              Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def, hsched]; simp
        · rw [if_neg h]
          apply Prosa.Analysis.Facts.Behavior.Service.not_scheduled_implies_no_service
          rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def, hsched]
          simp [Ne.symm h]
      simp_rw [h_sa]
      -- Sum of (if jj = jo then 1 else 0) for jj in nodup list containing jo = 1
      have h_nodup : (arrivals_between arr_seq t1 t0).Nodup :=
        Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_uniq
          arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set t1 t0
      have h_nodup_f := h_nodup.filter (fun jhp => another_hep_job jhp j)
      have h_sum_eq : ∀ (l : List Job), l.Nodup → jo ∈ l →
          (l.map (fun jj => if jj = jo then (1:ℕ) else 0)).sum = 1 := by
        intro l hl hm
        induction l with
        | nil => simp at hm
        | cons a l' ih =>
          rw [List.nodup_cons] at hl
          simp only [List.map_cons, List.sum_cons]
          rw [List.mem_cons] at hm
          cases hm with
          | inl ha =>
            subst ha; simp
            apply List.sum_eq_zero; intro x hx; rw [List.mem_map] at hx
            obtain ⟨b, hb, rfl⟩ := hx
            simp [show b ≠ jo from fun h => hl.1 (h ▸ hb)]
          | inr hm' =>
            simp [show a ≠ jo from fun h => hl.1 (h ▸ hm')]
            exact ih hl.2 hm'
      exact (h_sum_eq _ h_nodup_f hjo_in_filtered).symm

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_tasks
  H_priority_is_reflexive H_priority_is_transitive
  H_JLFP_respects_sequential_tasks in
theorem quiet_time_cl_implies_quiet_time_ab
    (H_j_arrives : arrives_in arr_seq j) (t : instant) :
    Prosa.Analysis.Definitions.Busy_interval.quiet_time arr_seq sched j t →
    Prosa.Analysis.Abstract.Definitions.quiet_time sched
      (interference sched) (interfering_workload arr_seq sched) j t := by
  intro QT
  have zero_qt : Prosa.Analysis.Definitions.Busy_interval.quiet_time arr_seq sched j 0 :=
    fun _ _ _ hab => absurd hab (Nat.not_lt_zero _)
  refine ⟨?_, fun ⟨arr_before, not_comp⟩ =>
    not_comp (QT j H_j_arrives (H_priority_is_reflexive 0 j) arr_before)⟩
  -- Part 1: cumul_interference = cumul_interfering_workload
  have h1 : cumul_interference (interference sched) j 0 t =
      cumulative_priority_inversion sched j 0 t +
      service_of_other_hep_jobs arr_seq sched j 0 t := by
    show cumulative_interference sched j 0 t = _
    rw [cumulative_interference_split]; congr 1
    exact service_equiv arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute j 0 t zero_qt
  have h2 : cumul_interfering_workload (interfering_workload arr_seq sched) j 0 t =
      cumulative_priority_inversion sched j 0 t +
      workload_of_other_hep_jobs arr_seq j 0 t := by
    show cumulative_interfering_workload arr_seq sched j 0 t = _
    unfold cumulative_interfering_workload; simp only [interfering_workload]
    rw [Finset.sum_add_distrib]; congr 1
    exact workload_equiv arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set j 0 t
  have h3 : service_of_other_hep_jobs arr_seq sched j 0 t =
      workload_of_other_hep_jobs arr_seq j 0 t := by
    simp only [service_of_other_hep_jobs, workload_of_other_hep_jobs]; symm
    exact (Prosa.Analysis.Facts.Model.Service_of_jobs.all_jobs_have_completed_equiv_workload_eq_service
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      (fun jhp => another_hep_job jhp j) 0 t t).mp
      (fun jh hjh hPjh => by
        simp only [another_hep_job, Bool.and_eq_true] at hPjh
        exact QT jh
          (Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived
            arr_seq H_arrival_times_are_consistent jh 0 t hjh)
          hPjh.1
          (Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived_between
            arr_seq H_arrival_times_are_consistent jh 0 t hjh).2)
  rw [h1, h2, h3]

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_tasks
  H_priority_is_reflexive H_priority_is_transitive
  H_JLFP_respects_sequential_tasks in
theorem quiet_time_ab_implies_quiet_time_cl (t : instant) :
    Prosa.Analysis.Abstract.Definitions.quiet_time sched
      (interference sched) (interfering_workload arr_seq sched) j t →
    Prosa.Analysis.Definitions.Busy_interval.quiet_time arr_seq sched j t := by
  intro ⟨hcumul, hnot_pending⟩
  intro jhp hjhp_arrives hjhp_prio hjhp_before
  have zero_qt : Prosa.Analysis.Definitions.Busy_interval.quiet_time arr_seq sched j 0 :=
    fun _ _ _ hab => absurd hab (Nat.not_lt_zero _)
  -- Derive: service(another_hep) = workload(another_hep)
  have h_se : cumul_interference (interference sched) j 0 t =
      cumulative_priority_inversion sched j 0 t +
      service_of_other_hep_jobs arr_seq sched j 0 t := by
    show cumulative_interference sched j 0 t = _
    rw [cumulative_interference_split]; congr 1
    exact service_equiv arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute j 0 t zero_qt
  have h_we : cumul_interfering_workload (interfering_workload arr_seq sched) j 0 t =
      cumulative_priority_inversion sched j 0 t +
      workload_of_other_hep_jobs arr_seq j 0 t := by
    show cumulative_interfering_workload arr_seq sched j 0 t = _
    unfold cumulative_interfering_workload; simp only [interfering_workload]
    rw [Finset.sum_add_distrib]; congr 1
    exact workload_equiv arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set j 0 t
  rw [h_se, h_we] at hcumul
  have hcumul' : service_of_other_hep_jobs arr_seq sched j 0 t =
      workload_of_other_hep_jobs arr_seq j 0 t := Nat.add_left_cancel hcumul
  by_cases hjhp_eq : jhp = j
  · subst hjhp_eq; by_contra hnc; exact hnot_pending ⟨hjhp_before, hnc⟩
  · have h_ahep : another_hep_job jhp j = true := by
      simp [another_hep_job, hjhp_prio, hjhp_eq]
    have hjhp_in := Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
      arr_seq H_arrival_times_are_consistent jhp 0 t hjhp_arrives ⟨Nat.zero_le _, hjhp_before⟩
    simp only [service_of_other_hep_jobs, workload_of_other_hep_jobs] at hcumul'
    exact (Prosa.Analysis.Facts.Model.Service_of_jobs.all_jobs_have_completed_equiv_workload_eq_service
      arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      (fun jhp => another_hep_job jhp j) 0 t t).mpr hcumul'.symm jhp hjhp_in h_ahep

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_tasks
  H_priority_is_reflexive H_priority_is_transitive
  H_JLFP_respects_sequential_tasks in
theorem instantiated_busy_interval_equivalent_edf_busy_interval
    (H_j_arrives : arrives_in arr_seq j) (t1 t2 : instant) :
    Prosa.Analysis.Definitions.Busy_interval.busy_interval arr_seq sched j t1 t2 ↔
    Prosa.Analysis.Abstract.Definitions.busy_interval sched
      (interference sched) (interfering_workload arr_seq sched) j t1 t2 := by
  have qt_fwd := quiet_time_cl_implies_quiet_time_ab arr_seq
    H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_tasks
    H_priority_is_reflexive H_priority_is_transitive
    H_JLFP_respects_sequential_tasks j H_j_arrives
  have qt_bwd := quiet_time_ab_implies_quiet_time_cl arr_seq
    H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_tasks
    H_priority_is_reflexive H_priority_is_transitive
    H_JLFP_respects_sequential_tasks j
  constructor
  · rintro ⟨⟨hlt, hqt1, hnqt, hle_arr, harr_lt⟩, hqt2⟩
    exact ⟨⟨⟨hle_arr, harr_lt⟩, qt_fwd _ hqt1,
            fun t ⟨ht1, ht2⟩ hqt => hnqt t ⟨ht1, ht2⟩ (qt_bwd t hqt)⟩,
           qt_fwd _ hqt2⟩
  · rintro ⟨⟨⟨hle_arr, harr_lt⟩, hqt1, hnqt⟩, hqt2⟩
    exact ⟨⟨Nat.lt_of_le_of_lt hle_arr harr_lt, qt_bwd _ hqt1,
            fun t ⟨ht1, ht2⟩ hqt => hnqt t ⟨ht1, ht2⟩ (qt_fwd _ hqt),
            hle_arr, harr_lt⟩,
           qt_bwd _ hqt2⟩

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute in
theorem instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs
    (t1 t0 : instant)
    (H_quiet_time : Prosa.Analysis.Definitions.Busy_interval.quiet_time arr_seq sched j t1) :
    cumulative_interference_from_other_hep_jobs sched j t1 t0 =
    service_of_other_hep_jobs arr_seq sched j t1 t0 :=
  service_equiv arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute j t1 t0 H_quiet_time

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute in
theorem instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks
    (t1 t0 : instant)
    (H_quiet_time : Prosa.Analysis.Definitions.Busy_interval.quiet_time arr_seq sched j t1) :
    cumulative_interference_from_hep_jobs_from_other_tasks (Task := Task) sched j t1 t0 =
    service_of_hep_jobs_from_other_tasks (Task := Task) arr_seq sched j t1 t0 := by
  simp only [service_of_hep_jobs_from_other_tasks, service_of_jobs, service_during,
             cumulative_interference_from_hep_jobs_from_other_tasks]
  have h_swap : ∀ (l : List Job),
      (l.map (fun jj => ∑ t' ∈ Finset.Ico t1 t0, service_at sched jj t')).sum =
      ∑ t' ∈ Finset.Ico t1 t0, (l.map (fun jj => service_at sched jj t')).sum := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [ih, ← Finset.sum_add_distrib]
  rw [h_swap]
  apply Finset.sum_congr rfl
  intro tt htt
  rw [Finset.mem_Ico] at htt
  simp only [is_interference_from_hep_job_from_another_task, hep_job_from_another_task]
  cases hsched : sched tt with
  | none =>
    simp only [Bool.toNat_false]
    symm; apply List.sum_eq_zero
    intro x hx; rw [List.mem_map] at hx
    obtain ⟨jhp, _, rfl⟩ := hx
    apply Prosa.Analysis.Facts.Behavior.Service.not_scheduled_implies_no_service
    rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def]; simp [hsched]
  | some jo =>
    simp only []
    cases hprio : (hep_job jo j && (job_task (Task := Task) jo != job_task j))
    · simp only [Bool.toNat_false]
      symm; apply List.sum_eq_zero
      intro x hx; rw [List.mem_map] at hx
      obtain ⟨jhp, hjhp_mem, rfl⟩ := hx
      rw [List.mem_filter] at hjhp_mem
      have h_eq_or_ne : jo = jhp ∨ jo ≠ jhp := eq_or_ne jo jhp
      cases h_eq_or_ne with
      | inl heq =>
        subst heq; rw [hjhp_mem.2] at hprio; simp at hprio
      | inr hne =>
        apply Prosa.Analysis.Facts.Behavior.Service.not_scheduled_implies_no_service
        rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def]; simp [hsched, hne]
    · simp only [Bool.toNat_true]
      have h_sched_jo : scheduled_at sched jo tt = true := by
        rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def]; simp [hsched]
      have hjo_arrives : arrives_in arr_seq jo :=
        H_jobs_come_from_arrival_sequence jo tt h_sched_jo
      have hjo_arr_le : job_arrival jo ≤ tt :=
        H_jobs_must_arrive_to_execute jo tt h_sched_jo
      have hjo_arr_lt : job_arrival jo < t0 := Nat.lt_of_le_of_lt hjo_arr_le htt.2
      have hjo_arr_ge : t1 ≤ job_arrival jo := by
        by_contra h_neg; push_neg at h_neg
        have hprio_hp : hep_job jo j = true := by
          simp only [Bool.and_eq_true] at hprio; exact hprio.1
        have hcompl : completed_by sched jo t1 := H_quiet_time jo hjo_arrives hprio_hp h_neg
        have h_not_sched := completed_implies_not_scheduled sched jo
          H_completed_jobs_dont_execute tt (completion_monotonic sched jo t1 tt htt.1 hcompl)
        rw [h_not_sched] at h_sched_jo; exact absurd h_sched_jo (by simp)
      have hjo_in : jo ∈ arrivals_between arr_seq t1 t0 :=
        Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
          arr_seq H_arrival_times_are_consistent jo t1 t0
          hjo_arrives ⟨hjo_arr_ge, hjo_arr_lt⟩
      have hjo_in_filtered : jo ∈ (arrivals_between arr_seq t1 t0).filter
          (fun jhp => hep_job_from_another_task (Task := Task) jhp j) :=
        List.mem_filter.mpr ⟨hjo_in, hprio⟩
      have h_sa : ∀ jhp, service_at sched jhp tt = if jhp = jo then 1 else 0 := by
        intro jhp
        by_cases h : jhp = jo
        · subst h
          rw [Prosa.Analysis.Facts.Model.Ideal_schedule.service_at_is_scheduled_at,
              Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def, hsched]; simp
        · rw [if_neg h]
          apply Prosa.Analysis.Facts.Behavior.Service.not_scheduled_implies_no_service
          rw [Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def, hsched]
          simp [Ne.symm h]
      simp_rw [h_sa]
      have h_nodup : (arrivals_between arr_seq t1 t0).Nodup :=
        Prosa.Analysis.Facts.Behavior.Arrivals.arrivals_uniq
          arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set t1 t0
      have h_nodup_f := h_nodup.filter (fun jhp => hep_job_from_another_task (Task := Task) jhp j)
      have h_sum_eq : ∀ (l : List Job), l.Nodup → jo ∈ l →
          (l.map (fun jj => if jj = jo then (1:ℕ) else 0)).sum = 1 := by
        intro l hl hm
        induction l with
        | nil => simp at hm
        | cons a l' ih =>
          rw [List.nodup_cons] at hl
          simp only [List.map_cons, List.sum_cons]
          rw [List.mem_cons] at hm
          cases hm with
          | inl ha =>
            subst ha; simp
            apply List.sum_eq_zero; intro x hx; rw [List.mem_map] at hx
            obtain ⟨b, hb, rfl⟩ := hx
            simp [show b ≠ jo from fun h => hl.1 (h ▸ hb)]
          | inr hm' =>
            simp [show a ≠ jo from fun h => hl.1 (h ▸ hm')]
            exact ih hl.2 hm'
      exact (h_sum_eq _ h_nodup_f hjo_in_filtered).symm

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_tasks
  H_priority_is_reflexive H_priority_is_transitive
  H_JLFP_respects_sequential_tasks in
theorem instantiated_quiet_time_equivalent_quiet_time
    (H_j_arrives : arrives_in arr_seq j) (t : instant) :
    Prosa.Analysis.Definitions.Busy_interval.quiet_time arr_seq sched j t ↔
    Prosa.Analysis.Abstract.Definitions.quiet_time sched
      (interference sched) (interfering_workload arr_seq sched) j t :=
  ⟨quiet_time_cl_implies_quiet_time_ab arr_seq
    H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_tasks
    H_priority_is_reflexive H_priority_is_transitive
    H_JLFP_respects_sequential_tasks j H_j_arrives t,
   quiet_time_ab_implies_quiet_time_cl arr_seq
    H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_sequential_tasks
    H_priority_is_reflexive H_priority_is_transitive
    H_JLFP_respects_sequential_tasks j t⟩

end JLFPInstantiation

end Prosa.Analysis.Abstract.Ideal_jlfp_rta
