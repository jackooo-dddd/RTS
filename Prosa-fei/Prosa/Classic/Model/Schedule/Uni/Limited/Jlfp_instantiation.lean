-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/jlfp_instantiation.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Schedule_of_task
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Workload
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Schedule.Uni.Schedule_of_task
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP
open Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions

namespace JLFPInstantiation

section Instantiation

variable {Task : Type _} [DecidableEq Task]
variable (task_cost : Task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)

variable (sched : schedule Job)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_sequential_jobs :
  sequential_jobs job_arrival job_cost sched job_task)

variable (higher_eq_priority : JLFP_policy Job)
variable (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
variable (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority)

variable (H_JLFP_respects_sequential_jobs :
  JLFP_respects_sequential_jobs job_task job_arrival higher_eq_priority)

variable (tsk : Task)

def is_interference_from_another_job_with_higher_eq_priority
    (higher_eq_priority : JLFP_policy Job) (sched : schedule Job)
    (j : Job) (t : Time) : Bool :=
  match sched t with
  | some jhp => higher_eq_priority jhp j && decide (jhp ≠ j)
  | none => false

def is_interference_from_another_task_with_higher_eq_priority
    (higher_eq_priority : JLFP_policy Job) (job_task : Job → Task) (sched : schedule Job)
    (j : Job) (t : Time) : Bool :=
  match sched t with
  | some jhp => higher_eq_priority jhp j && decide (job_task jhp ≠ job_task j)
  | none => false

def interfering_workload_of_jobs_with_hep_priority
    (higher_eq_priority : JLFP_policy Job) (job_cost : Job → Time) (arr_seq : arrival_sequence Job)
    (j : Job) (t : Time) : Nat :=
  ((jobs_arriving_at arr_seq t).filter
    (fun jhp => higher_eq_priority jhp j && decide (jhp ≠ j))).map job_cost |>.sum

def interference
    (higher_eq_priority : JLFP_policy Job) (sched : schedule Job)
    (j : Job) (t : Time) : Bool :=
  is_priority_inversion sched higher_eq_priority j t != 0 ||
  is_interference_from_another_job_with_higher_eq_priority higher_eq_priority sched j t

def interfering_workload
    (higher_eq_priority : JLFP_policy Job) (job_cost : Job → Time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (j : Job) (t : Time) : Nat :=
  is_priority_inversion sched higher_eq_priority j t +
  interfering_workload_of_jobs_with_hep_priority higher_eq_priority job_cost arr_seq j t

section Equivalences

theorem cumulative_interference_split :
    ∀ j t1 t2,
      ∑ t ∈ Finset.Ico t1 t2,
        (interference higher_eq_priority sched j t).toNat =
      ∑ t ∈ Finset.Ico t1 t2,
        is_priority_inversion sched higher_eq_priority j t +
      ∑ t ∈ Finset.Ico t1 t2,
        (is_interference_from_another_job_with_higher_eq_priority
          higher_eq_priority sched j t).toNat := by
  intro j t1 t2
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [interference, is_interference_from_another_job_with_higher_eq_priority,
             is_priority_inversion]
  cases h : sched t with
  | none => simp
  | some s =>
    simp only []
    cases hp : higher_eq_priority s j <;> simp

include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_priority_is_reflexive H_priority_is_transitive H_JLFP_respects_sequential_jobs in
theorem cumulative_task_interference_split :
    ∀ j t1 t2 upp_t,
      job_task j = tsk →
      j ∈ jobs_arrived_before arr_seq upp_t →
      ¬ completed_by job_cost sched j t2 →
      ∑ t ∈ Finset.Ico t1 t2,
        ((!(task_scheduled_at job_task sched tsk t)) &&
          (arrivals_of_task_before job_task arr_seq tsk upp_t).any
            (fun jj => JLFPInstantiation.interference higher_eq_priority sched jj t)).toNat =
      ∑ t ∈ Finset.Ico t1 t2,
        is_priority_inversion sched higher_eq_priority j t +
      ∑ t ∈ Finset.Ico t1 t2,
        (is_interference_from_another_task_with_higher_eq_priority
          higher_eq_priority job_task sched j t).toNat := by
  intro j t1 t2 upp_t TSK ARR NCOMPL
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have ht_lt : t < t2 := (Finset.mem_Ico.mp ht).2
  simp only [task_scheduled_at,
             is_interference_from_another_task_with_higher_eq_priority,
             interference, is_interference_from_another_job_with_higher_eq_priority,
             is_priority_inversion,
             Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.is_priority_inversion]
  cases hsched : sched t with
  | none => simp
  | some s =>
    cases hp : higher_eq_priority s j
    · -- hp = false: priority inversion
      simp only [hp, ite_false, Bool.false_and, Bool.toNat_false, Nat.add_zero]
      by_cases htsk : job_task s = tsk
      · exfalso
        rw [← TSK] at htsk
        have s_sched : scheduled_at sched s t = true := by simp [scheduled_at, hsched]
        by_cases harr : job_arrival s ≤ job_arrival j
        · have := H_JLFP_respects_sequential_jobs s j htsk harr; simp [this] at hp
        · push_neg at harr
          exact NCOMPL (completion_monotonic job_cost sched j t t2 (Nat.le_of_lt ht_lt) (H_sequential_jobs j s t (TSK ▸ htsk.symm) harr s_sched))
      · have hbeq : (job_task s == tsk) = false := by rw [beq_eq_false_iff_ne]; exact htsk
        simp only [hbeq, Bool.not_false, Bool.true_and]
        have hj_in : j ∈ arrivals_of_task_before job_task arr_seq tsk upp_t := by
          simp only [arrivals_of_task_before, arrivals_of_task_between, List.mem_filter, is_job_of_task]
          exact ⟨jobs_arrived_between_sub arr_seq j 0 0 upp_t upp_t (le_refl _) (le_refl _) ARR, by simp [TSK]⟩
        have hany : (arrivals_of_task_before job_task arr_seq tsk upp_t).any (fun jj => ((if higher_eq_priority s jj = true then 0 else 1) != 0 || (higher_eq_priority s jj && decide (s ≠ jj)))) = true := by
          rw [List.any_eq_true]
          exact ⟨j, hj_in, by simp [hp]⟩
        rw [hany]; simp
    · -- hp = true
      simp only [hp, ite_true, Bool.true_and, Nat.zero_add]
      by_cases htsk : job_task s = job_task j
      · have hdec : decide (job_task s ≠ job_task j) = false := by simp [htsk]
        simp only [hdec, Bool.toNat_false]
        have hbeq : (job_task s == tsk) = true := by rw [beq_iff_eq]; rw [htsk, TSK]
        simp only [hbeq, Bool.not_true, Bool.false_and, Bool.toNat_false]
      · have hdec : decide (job_task s ≠ job_task j) = true := by simp [htsk]
        simp only [hdec, Bool.toNat_true]
        have htsk2 : job_task s ≠ tsk := by intro h; apply htsk; rw [h, TSK]
        have hbeq : (job_task s == tsk) = false := by rw [beq_eq_false_iff_ne]; exact htsk2
        simp only [hbeq, Bool.not_false, Bool.true_and]
        have hj_in : j ∈ arrivals_of_task_before job_task arr_seq tsk upp_t := by
          simp only [arrivals_of_task_before, arrivals_of_task_between, List.mem_filter, is_job_of_task]
          exact ⟨jobs_arrived_between_sub arr_seq j 0 0 upp_t upp_t (le_refl _) (le_refl _) ARR, by simp [TSK]⟩
        have s_ne_j : s ≠ j := by intro h; subst h; exact htsk rfl
        have hany : (arrivals_of_task_before job_task arr_seq tsk upp_t).any (fun jj => ((if higher_eq_priority s jj = true then 0 else 1) != 0 || (higher_eq_priority s jj && decide (s ≠ jj)))) = true := by
          rw [List.any_eq_true]
          exact ⟨j, hj_in, by simp [hp, s_ne_j]⟩
        rw [hany]; simp

section InstantiatedWorkloadEquivalence

variable (t1 t2 : Time)

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

theorem instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs :
    ∑ t ∈ Finset.Ico t1 t2,
      interfering_workload_of_jobs_with_hep_priority
        higher_eq_priority job_cost arr_seq j t =
    workload_of_jobs job_cost (jobs_arrived_between arr_seq t1 t2)
      (fun jhp => higher_eq_priority jhp j && decide (jhp ≠ j)) := by
  -- LHS sums per-timestep interfering workload; RHS sums over concatenated arrivals.
  -- They are equal because jobs_arrived_between is the concat of per-step arrivals.
  -- Proof by induction on the interval length.
  by_cases hle : t1 ≤ t2
  · obtain ⟨k, rfl⟩ : ∃ k, t2 = t1 + k := ⟨t2 - t1, (Nat.add_sub_cancel' hle).symm⟩
    clear hle
    induction k with
    | zero =>
      simp only [Nat.add_zero, Finset.Ico_self, Finset.sum_empty]
      unfold workload_of_jobs jobs_arrived_between Prosa.Util.Bigcat.bigcat_nat
      simp
    | succ n ih =>
      -- Split the Finset.Ico sum
      have h1 : t1 + (n + 1) = (t1 + n) + 1 := by ring
      rw [h1, Finset.sum_Ico_succ_top (Nat.le_add_right t1 n)]
      rw [ih]
      -- Split jobs_arrived_between using cat lemma
      rw [workload_of_jobs_cat job_cost arr_seq (t1 + n) t1 (t1 + n + 1)
            (fun jhp => higher_eq_priority jhp j && decide (jhp ≠ j))
            ⟨Nat.le_add_right t1 n, Nat.le_succ (t1 + n)⟩]
      -- Now: LHS + interfering_workload = workload(t1,t1+n) + workload(t1+n,t1+n+1)
      -- Need to show interfering_workload = workload(t1+n,t1+n+1)
      congr 1
      -- Show: workload over arrived_between (t1+n) (t1+n+1) = interfering_workload at t1+n
      unfold interfering_workload_of_jobs_with_hep_priority workload_of_jobs
      unfold jobs_arrived_between Prosa.Util.Bigcat.bigcat_nat jobs_arriving_at
      -- The subtraction t1+n+1 - (t1+n) simplifies to 1
      -- range' (t1+n) 1 = [t1+n], so map f it = [f(t1+n)], flatten = f(t1+n)
      conv_rhs => rw [show t1 + n + 1 - (t1 + n) = 1 from Nat.add_sub_cancel_left (t1 + n) 1]
      simp
  · push_neg at hle
    rw [Finset.Ico_eq_empty (not_lt.mpr (Nat.le_of_lt hle)), Finset.sum_empty]
    unfold workload_of_jobs jobs_arrived_between Prosa.Util.Bigcat.bigcat_nat
    rw [show t2 - t1 = 0 from Nat.sub_eq_zero_of_le (Nat.le_of_lt hle)]
    simp

end InstantiatedWorkloadEquivalence

section InstantiatedServiceEquivalences

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

variable (t1 t : Time)
variable (H_quiet_time :
  Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.quiet_time
    job_arrival job_cost arr_seq sched higher_eq_priority j t1)

include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_priority_is_reflexive H_priority_is_transitive H_JLFP_respects_sequential_jobs H_j_arrives H_job_of_tsk H_quiet_time in
theorem instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs :
    ∑ tt ∈ Finset.Ico t1 t,
      (is_interference_from_another_job_with_higher_eq_priority
        higher_eq_priority sched j tt).toNat =
    service_of_jobs sched (jobs_arrived_between arr_seq t1 t)
      (fun jhp => higher_eq_priority jhp j && decide (jhp ≠ j)) t1 t := by
  -- Unfold RHS into a double sum and swap order
  unfold service_of_jobs service_during
  -- Swap sum order: ∑_job ∑_time service_at → ∑_time ∑_job service_at
  have h_swap : ∀ (l : List Job),
      (l.map (fun jj => ∑ t' ∈ Finset.Ico t1 t, service_at sched jj t')).sum =
      ∑ t' ∈ Finset.Ico t1 t, (l.map (fun jj => service_at sched jj t')).sum := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [ih, ← Finset.sum_add_distrib]
  rw [h_swap]
  -- Now both sides are ∑ tt ∈ Finset.Ico t1 t, f(tt). Show pointwise equality
  apply Finset.sum_congr rfl
  intro tt htt
  rw [Finset.mem_Ico] at htt
  simp only [is_interference_from_another_job_with_higher_eq_priority, service_at, scheduled_at]
  cases hsched : sched tt with
  | none => simp [Bool.toNat]
  | some jo =>
    -- Simplify the match on some jo
    simp only []
    cases hprio : (higher_eq_priority jo j && decide (jo ≠ j))
    · -- jo does NOT satisfy the predicate: both sides are 0
      simp only [Bool.toNat_false]
      symm; apply List.sum_eq_zero
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨jhp, hjhp_mem, rfl⟩ := hx
      rw [List.mem_filter] at hjhp_mem
      by_cases heq : (some jo == some jhp : Bool) = true
      · rw [beq_iff_eq] at heq
        have : jo = jhp := Option.some_injective _ heq
        subst this
        rw [hjhp_mem.2] at hprio; simp at hprio
      · simp only [Bool.not_eq_true] at heq; simp [heq, Bool.toNat]
    · -- jo satisfies predicate: LHS = 1, RHS = sum of service_at
      simp only [Bool.toNat_true]
      have hjo_arrives : arrives_in arr_seq jo :=
        H_jobs_come_from_arrival_sequence jo tt (by simp [scheduled_at, hsched])
      have hjo_arr_le : job_arrival jo ≤ tt :=
        H_jobs_must_arrive_to_execute jo tt (by simp [scheduled_at, hsched])
      have hjo_arr_lt_t : job_arrival jo < t := Nat.lt_of_le_of_lt hjo_arr_le htt.2
      have hjo_arr_ge_t1 : t1 ≤ job_arrival jo := by
        by_contra h_neg
        push_neg at h_neg
        have hprio_hp : higher_eq_priority jo j = true := by
          have h := hprio
          simp only [Bool.and_eq_true] at h
          exact h.1
        have hcompl : completed_by job_cost sched jo t1 := by
          apply H_quiet_time
          · exact hjo_arrives
          · exact hprio_hp
          · exact h_neg
        have h_compl_tt := completion_monotonic job_cost sched jo t1 tt htt.1 hcompl
        exact (completed_implies_not_scheduled job_cost sched jo H_completed_jobs_dont_execute tt h_compl_tt)
          (by simp [scheduled_at, hsched])
      have hjo_in : jo ∈ jobs_arrived_between arr_seq t1 t :=
        arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent jo t1 t
          hjo_arrives ⟨hjo_arr_ge_t1, hjo_arr_lt_t⟩
      have hjo_in_filtered : jo ∈ (jobs_arrived_between arr_seq t1 t).filter
          (fun jhp => higher_eq_priority jhp j && decide (jhp ≠ j)) :=
        List.mem_filter.mpr ⟨hjo_in, hprio⟩
      -- Sum is exactly 1: ≥ 1 from jo, ≤ 1 from service_of_jobs_le_1
      -- First rewrite to use service_at
      have h_eq_sa : ∀ jhp, (some jo == some jhp : Bool).toNat = service_at sched jhp tt := by
        intro jhp; simp [service_at, scheduled_at, hsched]
      simp_rw [h_eq_sa]
      have h_sum_le_1 := service_of_jobs_le_1 job_arrival arr_seq H_arrival_times_are_consistent
        H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence t1 t tt
        (fun jhp => higher_eq_priority jhp j && decide (jhp ≠ j))
      have h_sum_ge_1 : 1 ≤ ((jobs_arrived_between arr_seq t1 t).filter
          (fun jhp => higher_eq_priority jhp j && decide (jhp ≠ j)) |>.map
          (fun jhp => service_at sched jhp tt)).sum := by
        have hsa_jo : service_at sched jo tt = 1 := by simp [service_at, scheduled_at, hsched, Bool.toNat]
        calc 1 = service_at sched jo tt := hsa_jo.symm
          _ ≤ _ := List.le_sum_of_mem (List.mem_map.mpr ⟨jo, hjo_in_filtered, rfl⟩)
      omega

include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_priority_is_reflexive H_priority_is_transitive H_JLFP_respects_sequential_jobs H_j_arrives H_job_of_tsk H_quiet_time in
theorem instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks :
    ∑ tt ∈ Finset.Ico t1 t,
      (is_interference_from_another_task_with_higher_eq_priority
        higher_eq_priority job_task sched j tt).toNat =
    service_of_jobs sched (jobs_arrived_between arr_seq t1 t)
      (fun jhp => higher_eq_priority jhp j && decide (job_task jhp ≠ job_task j)) t1 t := by
  -- Unfold RHS into a double sum and swap order
  unfold service_of_jobs service_during
  have h_swap : ∀ (l : List Job),
      (l.map (fun jj => ∑ t' ∈ Finset.Ico t1 t, service_at sched jj t')).sum =
      ∑ t' ∈ Finset.Ico t1 t, (l.map (fun jj => service_at sched jj t')).sum := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [ih, ← Finset.sum_add_distrib]
  rw [h_swap]
  apply Finset.sum_congr rfl
  intro tt htt
  rw [Finset.mem_Ico] at htt
  simp only [is_interference_from_another_task_with_higher_eq_priority, service_at, scheduled_at]
  cases hsched : sched tt with
  | none => simp [Bool.toNat]
  | some jo =>
    simp only []
    cases hprio : (higher_eq_priority jo j && decide (job_task jo ≠ job_task j))
    · -- jo does NOT satisfy the predicate: both sides are 0
      simp only [Bool.toNat_false]
      symm; apply List.sum_eq_zero
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨jhp, hjhp_mem, rfl⟩ := hx
      rw [List.mem_filter] at hjhp_mem
      by_cases heq : (some jo == some jhp : Bool) = true
      · rw [beq_iff_eq] at heq
        have : jo = jhp := Option.some_injective _ heq
        subst this
        rw [hjhp_mem.2] at hprio; simp at hprio
      · simp only [Bool.not_eq_true] at heq; simp [heq, Bool.toNat]
    · -- jo satisfies predicate: LHS = 1, RHS = sum of service_at
      simp only [Bool.toNat_true]
      have hjo_arrives : arrives_in arr_seq jo :=
        H_jobs_come_from_arrival_sequence jo tt (by simp [scheduled_at, hsched])
      have hjo_arr_le : job_arrival jo ≤ tt :=
        H_jobs_must_arrive_to_execute jo tt (by simp [scheduled_at, hsched])
      have hjo_arr_lt_t : job_arrival jo < t := Nat.lt_of_le_of_lt hjo_arr_le htt.2
      have hjo_arr_ge_t1 : t1 ≤ job_arrival jo := by
        by_contra h_neg
        push_neg at h_neg
        have hprio_hp : higher_eq_priority jo j = true := by
          have h := hprio
          simp only [Bool.and_eq_true] at h
          exact h.1
        have hcompl : completed_by job_cost sched jo t1 := by
          apply H_quiet_time
          · exact hjo_arrives
          · exact hprio_hp
          · exact h_neg
        have h_compl_tt := completion_monotonic job_cost sched jo t1 tt htt.1 hcompl
        exact (completed_implies_not_scheduled job_cost sched jo H_completed_jobs_dont_execute tt h_compl_tt)
          (by simp [scheduled_at, hsched])
      have hjo_in : jo ∈ jobs_arrived_between arr_seq t1 t :=
        arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent jo t1 t
          hjo_arrives ⟨hjo_arr_ge_t1, hjo_arr_lt_t⟩
      have hjo_in_filtered : jo ∈ (jobs_arrived_between arr_seq t1 t).filter
          (fun jhp => higher_eq_priority jhp j && decide (job_task jhp ≠ job_task j)) :=
        List.mem_filter.mpr ⟨hjo_in, hprio⟩
      -- Sum is exactly 1
      have h_eq_sa : ∀ jhp, (some jo == some jhp : Bool).toNat = service_at sched jhp tt := by
        intro jhp; simp [service_at, scheduled_at, hsched]
      simp_rw [h_eq_sa]
      have h_sum_le_1 := service_of_jobs_le_1 job_arrival arr_seq H_arrival_times_are_consistent
        H_arr_seq_is_a_set sched H_jobs_come_from_arrival_sequence t1 t tt
        (fun jhp => higher_eq_priority jhp j && decide (job_task jhp ≠ job_task j))
      have h_sum_ge_1 : 1 ≤ ((jobs_arrived_between arr_seq t1 t).filter
          (fun jhp => higher_eq_priority jhp j && decide (job_task jhp ≠ job_task j)) |>.map
          (fun jhp => service_at sched jhp tt)).sum := by
        have hsa_jo : service_at sched jo tt = 1 := by simp [service_at, scheduled_at, hsched, Bool.toNat]
        calc 1 = service_at sched jo tt := hsa_jo.symm
          _ ≤ _ := List.le_sum_of_mem (List.mem_map.mpr ⟨jo, hjo_in_filtered, rfl⟩)
      omega

end InstantiatedServiceEquivalences

section BusyIntervalEquivalence

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)
variable (H_job_cost_positive : job_cost j > 0)

include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_priority_is_reflexive H_priority_is_transitive H_JLFP_respects_sequential_jobs H_j_arrives H_job_of_tsk H_job_cost_positive in
theorem instantiated_quiet_time_equivalent_edf_quiet_time :
    ∀ t,
      Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.quiet_time
        job_arrival job_cost arr_seq sched higher_eq_priority j t ↔
      Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.quiet_time
        job_arrival job_cost sched
        (fun jj tt => interference higher_eq_priority sched jj tt)
        (fun jj tt => interfering_workload higher_eq_priority job_cost arr_seq sched jj tt)
        j t := by
  -- Abbreviations
  have zero_is_quiet_time : ∀ j', Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.quiet_time
      job_arrival job_cost arr_seq sched higher_eq_priority j' 0 := by
    intro j' jhp _ _ hab
    exfalso; exact Nat.not_lt_zero _ hab
  have CIS := cumulative_interference_split (higher_eq_priority := higher_eq_priority) (sched := sched)
  -- IC1: cumulative interference from hep jobs = service of hep jobs (specialized to j)
  have IC1 : ∀ (t1' t' : Time),
    Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.quiet_time
      job_arrival job_cost arr_seq sched higher_eq_priority j t1' →
    ∑ tt ∈ Finset.Ico t1' t',
      (is_interference_from_another_job_with_higher_eq_priority higher_eq_priority sched j tt).toNat =
    service_of_jobs sched (jobs_arrived_between arr_seq t1' t')
      (fun jhp => higher_eq_priority jhp j && decide (jhp ≠ j)) t1' t' := by
    intro t1' t' hqt
    exact @instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs
      Task _ Job _ job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
      sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_sequential_jobs higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
      H_JLFP_respects_sequential_jobs tsk j H_j_arrives H_job_of_tsk t1' t' hqt
  -- WK: cumulative workload = workload_of_jobs
  have WK : ∀ (t1' t2' : Time) (j' : Job),
    ∑ t ∈ Finset.Ico t1' t2',
      interfering_workload_of_jobs_with_hep_priority higher_eq_priority job_cost arr_seq j' t =
    workload_of_jobs job_cost (jobs_arrived_between arr_seq t1' t2')
      (fun jhp => higher_eq_priority jhp j' && decide (jhp ≠ j')) :=
    fun t1' t2' j' => instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs
      (job_cost := job_cost) (arr_seq := arr_seq) (higher_eq_priority := higher_eq_priority)
      (t1 := t1') (t2 := t2') (j := j')
  -- AC: all completed ↔ workload = service
  have AC : ∀ (t1' t2' t_compl : Time) (P' : Job → Bool),
    (∀ jj, jj ∈ jobs_arrived_between arr_seq t1' t2' → P' jj = true →
      completed_by job_cost sched jj t_compl) ↔
    workload_of_jobs job_cost (jobs_arrived_between arr_seq t1' t2') P' =
    service_of_jobs sched (jobs_arrived_between arr_seq t1' t2') P' t1' t_compl :=
    fun t1' t2' t_compl P' => all_jobs_have_completed_equiv_workload_eq_service
      (job_arrival := job_arrival) (job_cost := job_cost) (arr_seq := arr_seq)
      (H_arrival_times_are_consistent := H_arrival_times_are_consistent)
      (sched := sched)
      (H_jobs_must_arrive_to_execute := H_jobs_must_arrive_to_execute)
      (H_completed_jobs_dont_execute := H_completed_jobs_dont_execute)
      (P := P') (t1 := t1') (t2 := t2') t_compl
  intro t
  constructor
  · -- Forward: BusyInterval.quiet_time → AbstractRTA.quiet_time
    intro hQT
    constructor
    · -- cumul_interference = cumul_interfering_workload
      -- Goal: cumul_interference (...) j 0 t = cumul_interfering_workload (...) j 0 t
      -- Unfold cumul_interference/workload to sums, then use CIS, IC1, WK, AC
      unfold Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.cumul_interference
      unfold Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.cumul_interfering_workload
      -- Now goal: ∑ (interference ...).toNat = ∑ (interfering_workload ...)
      -- Use CIS to split LHS
      rw [CIS j 0 t]
      -- Now LHS = ∑ pi + ∑ hep_interf
      -- Unfold interfering_workload on RHS
      simp only [interfering_workload]
      rw [Finset.sum_add_distrib]
      -- Cancel the priority_inversion parts
      congr 1
      -- Need: ∑ is_interference_from_another_job_hep = ∑ interfering_workload_of_jobs_with_hep_priority
      rw [IC1 0 t (zero_is_quiet_time j)]
      rw [WK 0 t j]
      -- Need: service_of_jobs = workload_of_jobs for hep&≠j jobs in [0,t)
      symm
      exact (AC 0 t t (fun jhp => higher_eq_priority jhp j && decide (jhp ≠ j))).mp
        (fun jh hjh hPjh => by
          simp only [Bool.and_eq_true] at hPjh
          apply hQT jh
          · exact in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent jh 0 t hjh
          · exact hPjh.1
          · exact (in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent jh 0 t hjh).2)
    · -- ¬ pending_earlier_and_at
      intro ⟨harr_before, hnot_compl⟩
      exact hnot_compl (hQT j H_j_arrives (H_priority_is_reflexive j) harr_before)
  · -- Backward: AbstractRTA.quiet_time → BusyInterval.quiet_time
    intro ⟨hcumul, hnot_pending⟩
    intro jhp hjhp_arrives hjhp_prio hjhp_before
    -- From hcumul, extract that service = workload for hep&≠j jobs
    have hcumul' : ∑ tt ∈ Finset.Ico 0 t,
        (is_interference_from_another_job_with_higher_eq_priority higher_eq_priority sched j tt).toNat =
        ∑ tt ∈ Finset.Ico 0 t,
        interfering_workload_of_jobs_with_hep_priority higher_eq_priority job_cost arr_seq j tt := by
      unfold Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.cumul_interference at hcumul
      unfold Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.cumul_interfering_workload at hcumul
      rw [CIS j 0 t] at hcumul
      simp only [interfering_workload] at hcumul
      rw [Finset.sum_add_distrib] at hcumul
      omega
    rw [IC1 0 t (zero_is_quiet_time j), WK 0 t j] at hcumul'
    -- So service_of_jobs = workload_of_jobs for hep&≠j jobs
    -- Use all_jobs_have_completed_equiv_workload_eq_service to get individual completion
    have h_all_compl := (AC 0 t t (fun jhp' => higher_eq_priority jhp' j && decide (jhp' ≠ j))).mpr hcumul'.symm
    -- Now show jhp is completed
    -- Case: jhp = j or jhp ≠ j
    by_cases hjhp_eq : jhp = j
    · -- jhp = j: need ¬pending_earlier_and_at → j is completed
      subst hjhp_eq
      by_contra hnc
      exact hnot_pending ⟨hjhp_before, hnc⟩
    · -- jhp ≠ j: apply h_all_compl
      have hjhp_in := arrived_between_implies_in_arrivals job_arrival arr_seq
        H_arrival_times_are_consistent jhp 0 t hjhp_arrives ⟨Nat.zero_le _, hjhp_before⟩
      exact h_all_compl jhp hjhp_in (by simp [hjhp_prio, hjhp_eq])

include H_arrival_times_are_consistent H_arr_seq_is_a_set H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_priority_is_reflexive H_priority_is_transitive H_JLFP_respects_sequential_jobs H_j_arrives H_job_of_tsk H_job_cost_positive in
theorem instantiated_busy_interval_equivalent_edf_busy_interval :
    ∀ t1 t2,
      Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.busy_interval
        job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2 ↔
      Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.busy_interval
        job_arrival job_cost sched
        (fun jj tt => interference higher_eq_priority sched jj tt)
        (fun jj tt => interfering_workload higher_eq_priority job_cost arr_seq sched jj tt)
        j t1 t2 := by
  have QT_equiv := instantiated_quiet_time_equivalent_edf_quiet_time
    (job_arrival := job_arrival) (job_cost := job_cost) (job_task := job_task) (arr_seq := arr_seq)
    (H_arrival_times_are_consistent := H_arrival_times_are_consistent)
    (H_arr_seq_is_a_set := H_arr_seq_is_a_set)
    (sched := sched)
    (H_jobs_come_from_arrival_sequence := H_jobs_come_from_arrival_sequence)
    (H_jobs_must_arrive_to_execute := H_jobs_must_arrive_to_execute)
    (H_completed_jobs_dont_execute := H_completed_jobs_dont_execute)
    (H_sequential_jobs := H_sequential_jobs)
    (higher_eq_priority := higher_eq_priority)
    (H_priority_is_reflexive := H_priority_is_reflexive)
    (H_priority_is_transitive := H_priority_is_transitive)
    (H_JLFP_respects_sequential_jobs := H_JLFP_respects_sequential_jobs)
    (tsk := tsk) (j := j)
    (H_j_arrives := H_j_arrives) (H_job_of_tsk := H_job_of_tsk)
    (H_job_cost_positive := H_job_cost_positive)
  intro t1' t2'
  simp only [Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.busy_interval,
             Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP.busy_interval_prefix,
             Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.busy_interval,
             Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Definitions.busy_interval_prefix]
  constructor
  · rintro ⟨⟨hlt, hqt1, hnqt, hle_arr, harr_lt⟩, hqt2⟩
    exact ⟨⟨hle_arr, harr_lt, (QT_equiv t1').mp hqt1,
            fun t ht1 ht2 hqt => hnqt t ⟨ht1, ht2⟩ ((QT_equiv t).mpr hqt)⟩,
           (QT_equiv t2').mp hqt2⟩
  · rintro ⟨⟨hle_arr, harr_lt, hqt1, hnqt⟩, hqt2⟩
    exact ⟨⟨Nat.lt_of_le_of_lt hle_arr harr_lt, (QT_equiv t1').mpr hqt1,
            fun t ⟨ht1, ht2⟩ hqt => hnqt t ht1 ht2 ((QT_equiv t).mp hqt),
            hle_arr, harr_lt⟩,
           (QT_equiv t2').mpr hqt2⟩

end BusyIntervalEquivalence

end Equivalences

end Instantiation

end JLFPInstantiation

end Prosa.Classic.Model.Schedule.Uni.Limited.Jlfp_instantiation
