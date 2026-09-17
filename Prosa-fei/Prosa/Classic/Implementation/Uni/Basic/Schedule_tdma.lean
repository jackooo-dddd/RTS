-- Translated from: ../rt-proofs/classic/implementation/uni/basic/schedule_tdma.v
import Prosa.Classic.Util.All
import Prosa.Classic.Util.Find_seq
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform_tdma
import Prosa.Classic.Model.Policy_tdma
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction
import Prosa.Classic.Implementation.Job
import Prosa.Util.Seqset
import Mathlib.Tactic

namespace Prosa.Classic.Implementation.Uni.Basic.Schedule_tdma

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Basic.Platform_tdma
open Prosa.Classic.Model.Policy_tdma
open Prosa.Classic.Model.Schedule.Uni.Transformation.Construction.ScheduleConstruction
open Prosa.Classic.Util.Find_seq
open Prosa.Util.Seqset

namespace ConcreteSchedulerTDMA

section ImplementationTDMA

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)

variable (ts : SeqSet Task)

variable (time_slot : TDMA_slot Task)

variable (slot_order : TDMA_slot_order Task)

variable (H_arrival_times_are_consistent :
    arrival_times_are_consistent job_arrival arr_seq)

section JobSchedule

variable (sched : schedule Job)
variable (t : Time)

def pending_jobs : List Job :=
  (jobs_arrived_up_to arr_seq t).filter
    (fun j => decide (job_arrival j ≤ t) && !decide (job_cost j ≤ service sched j t))

def job_to_schedule : Option Job :=
  findP (fun job =>
    decide (((t + TDMA_cycle ts time_slot -
      Task_slot_offset ts slot_order (job_task job) time_slot %
        TDMA_cycle ts time_slot) %
      TDMA_cycle ts time_slot) <
      time_slot (job_task job)))
    (pending_jobs job_arrival job_cost arr_seq sched t)

section Lemmas

variable (arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)

include H_arrival_times_are_consistent arr_seq_is_a_set

theorem pending_jobs_uniq :
    (pending_jobs job_arrival job_cost arr_seq sched t).Nodup := by
  unfold pending_jobs
  apply List.Nodup.filter
  unfold jobs_arrived_up_to
  exact arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent arr_seq_is_a_set 0 (t + 1)

theorem respects_FIFO :
    ∀ j j',
    j ∈ pending_jobs job_arrival job_cost arr_seq sched t →
    j' ∈ pending_jobs job_arrival job_cost arr_seq sched t →
    (pending_jobs job_arrival job_cost arr_seq sched t).idxOf j' <
      (pending_jobs job_arrival job_cost arr_seq sched t).idxOf j →
    job_arrival j' ≤ job_arrival j := by
  intro j j' hj hj' hidx
  by_contra hlt
  push_neg at hlt
  -- hlt : job_arrival j < job_arrival j'
  -- We derive a contradiction by showing idxOf j < idxOf j' in pending_jobs,
  -- which contradicts hidx (idxOf j' < idxOf j)
  -- Step 1: j and j' are in jobs_arrived_up_to
  have hj_pend := hj
  have hj'_pend := hj'
  unfold pending_jobs at hj hj'
  rw [List.mem_filter] at hj hj'
  have ⟨hj_arr, hj_pred⟩ := hj
  have ⟨hj'_arr, hj'_pred⟩ := hj'
  -- Step 2: Get arrival time indices
  unfold jobs_arrived_up_to at hj_arr hj'_arr
  have ⟨i_j, hi_j_mem, hi_j_ge, hi_j_lt⟩ := Prosa.Util.Bigcat.mem_bigcat_nat_exists j 0 (t + 1) _ hj_arr
  have ⟨i_j', hi_j'_mem, hi_j'_ge, hi_j'_lt⟩ := Prosa.Util.Bigcat.mem_bigcat_nat_exists j' 0 (t + 1) _ hj'_arr
  have h_arrj := H_arrival_times_are_consistent j i_j hi_j_mem
  have h_arrj' := H_arrival_times_are_consistent j' i_j' hi_j'_mem
  -- So i_j = job_arrival j, i_j' = job_arrival j'
  -- hlt says job_arrival j < job_arrival j', hence i_j < i_j'
  have hij_lt : i_j < i_j' := by simp only [Time] at *; omega
  -- Step 3: Split the list at i_j + 1
  -- jobs_arrived_between 0 (t+1) = jobs_arrived_between 0 (i_j+1) ++ jobs_arrived_between (i_j+1) (t+1)
  have hle1 : 0 ≤ i_j + 1 := Nat.zero_le _
  have hle2 : i_j + 1 ≤ t + 1 := by simp only [Time] at *; omega
  -- j ∈ first part
  have hj_in_first : j ∈ jobs_arrived_between arr_seq 0 (i_j + 1) := by
    unfold jobs_arrived_between
    exact Prosa.Util.Bigcat.mem_bigcat_nat j 0 (i_j + 1) i_j (jobs_arriving_at arr_seq) ⟨Nat.zero_le _, Nat.lt_succ_of_le (le_refl _)⟩ hi_j_mem
  -- j' ∈ second part
  have hj'_in_second : j' ∈ jobs_arrived_between arr_seq (i_j + 1) (t + 1) := by
    unfold jobs_arrived_between
    exact Prosa.Util.Bigcat.mem_bigcat_nat j' (i_j + 1) (t + 1) i_j' (jobs_arriving_at arr_seq) ⟨hij_lt, hi_j'_lt⟩ hi_j'_mem
  -- The full list is nodup
  have hnodup_full : (jobs_arrived_between arr_seq 0 (t + 1)).Nodup :=
    arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent arr_seq_is_a_set 0 (t + 1)
  -- j' is NOT in the first part (because the full list is Nodup and j' is in the second part)
  have hj'_not_first : j' ∉ jobs_arrived_between arr_seq 0 (i_j + 1) := by
    intro h_in
    -- j' ∈ first and j' ∈ second, but the concatenation is Nodup
    rw [job_arrived_between_cat arr_seq 0 (i_j + 1) (t + 1) hle1 hle2] at hnodup_full
    exact List.disjoint_of_nodup_append hnodup_full h_in hj'_in_second
  -- Step 4: In the concatenation, j comes before j'
  -- list = first ++ second, j ∈ first, j' ∈ second ∧ j' ∉ first
  -- So idxOf j list < first.length ≤ idxOf j' list
  -- Therefore, in the filtered list (pending_jobs), idxOf j < idxOf j'
  -- This requires showing filter preserves relative order
  -- For the filter, pending_jobs = (first ++ second).filter p
  -- = first.filter p ++ second.filter p (by List.filter_append)
  -- j ∈ first.filter p and j' ∈ second.filter p (they satisfy p)
  -- So in pending_jobs, j appears before j'
  -- Hence idxOf j pending_jobs < idxOf j' pending_jobs
  set pred := (fun j => decide (job_arrival j ≤ t) && !decide (job_cost j ≤ service sched j t))
  -- Rewrite the list split
  have hsplit : jobs_arrived_up_to arr_seq t =
    jobs_arrived_between arr_seq 0 (i_j + 1) ++ jobs_arrived_between arr_seq (i_j + 1) (t + 1) := by
    unfold jobs_arrived_up_to
    exact job_arrived_between_cat arr_seq 0 (i_j + 1) (t + 1) hle1 hle2
  -- pending_jobs = (jobs_arrived_up_to arr_seq t).filter pred
  -- = (first ++ second).filter pred = first.filter pred ++ second.filter pred
  have hpj_split : pending_jobs job_arrival job_cost arr_seq sched t =
    (jobs_arrived_between arr_seq 0 (i_j + 1)).filter pred ++ (jobs_arrived_between arr_seq (i_j + 1) (t + 1)).filter pred := by
    unfold pending_jobs
    rw [hsplit, List.filter_append]
  -- j ∈ first.filter pred
  have hj_in_f1 : j ∈ (jobs_arrived_between arr_seq 0 (i_j + 1)).filter pred := by
    rw [List.mem_filter]; exact ⟨hj_in_first, hj_pred⟩
  -- j' ∈ second.filter pred
  have hj'_in_f2 : j' ∈ (jobs_arrived_between arr_seq (i_j + 1) (t + 1)).filter pred := by
    rw [List.mem_filter]; exact ⟨hj'_in_second, hj'_pred⟩
  -- j' ∉ first.filter pred (because j' ∉ first)
  have hj'_not_f1 : j' ∉ (jobs_arrived_between arr_seq 0 (i_j + 1)).filter pred := by
    intro h_in; rw [List.mem_filter] at h_in; exact hj'_not_first h_in.1
  -- Now, in pending_jobs = f1 ++ f2, j ∈ f1 and j' ∈ f2, j' ∉ f1
  -- idxOf j (f1 ++ f2) < f1.length ≤ idxOf j' (f1 ++ f2)
  -- hence idxOf j < idxOf j'
  rw [hpj_split] at hidx
  have hidx_j' : ((jobs_arrived_between arr_seq 0 (i_j + 1)).filter pred).length ≤
    List.idxOf j' ((jobs_arrived_between arr_seq 0 (i_j + 1)).filter pred ++
    (jobs_arrived_between arr_seq (i_j + 1) (t + 1)).filter pred) := by
    rw [List.idxOf_append_of_notMem hj'_not_f1]
    omega
  have hidx_j : List.idxOf j ((jobs_arrived_between arr_seq 0 (i_j + 1)).filter pred ++
    (jobs_arrived_between arr_seq (i_j + 1) (t + 1)).filter pred) <
    ((jobs_arrived_between arr_seq 0 (i_j + 1)).filter pred).length := by
    rw [List.idxOf_append_of_mem hj_in_f1]
    exact List.idxOf_lt_length_of_mem hj_in_f1
  omega

omit arr_seq_is_a_set in
theorem pending_job_in_penging_list :
    ∀ j, arrives_in arr_seq j →
    pending job_arrival job_cost sched j t →
    j ∈ pending_jobs job_arrival job_cost arr_seq sched t := by
  intro j ARRJ PEN
  unfold pending_jobs
  rw [List.mem_filter]
  constructor
  · -- j ∈ jobs_arrived_up_to arr_seq t
    unfold jobs_arrived_up_to
    apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent
    · exact ARRJ
    · constructor
      · exact Nat.zero_le _
      · have ⟨harr, _⟩ := PEN
        unfold has_arrived at harr
        simp only [Time] at *
        omega
  · -- the filter predicate holds
    have ⟨harr, hnotcomp⟩ := PEN
    unfold has_arrived at harr
    unfold completed_by at hnotcomp
    simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨harr, hnotcomp⟩

omit arr_seq_is_a_set in
theorem pendinglist_jobs_in_arr_seq :
    ∀ j, j ∈ pending_jobs job_arrival job_cost arr_seq sched t →
    arrives_in arr_seq j := by
  intro j JIN
  unfold pending_jobs at JIN
  rw [List.mem_filter] at JIN
  have ⟨harr, _⟩ := JIN
  unfold jobs_arrived_up_to at harr
  exact in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j 0 (t + 1) harr

end Lemmas

end JobSchedule

section SchedulerTDMA

private def empty_schedule : schedule Job := fun _ => none

def scheduler_tdma : schedule Job :=
  build_schedule_from_prefixes
    (job_to_schedule job_arrival job_cost job_task arr_seq ts time_slot slot_order)
    empty_schedule

include H_arrival_times_are_consistent in
theorem scheduler_depends_only_on_prefix :
    ∀ (sched1 sched2 : schedule Job) (t : Time),
    (∀ t0, t0 < t → sched1 t0 = sched2 t0) →
    job_to_schedule job_arrival job_cost job_task arr_seq ts time_slot slot_order sched1 t =
    job_to_schedule job_arrival job_cost job_task arr_seq ts time_slot slot_order sched2 t := by
  intro sched1 sched2 t ALL
  unfold job_to_schedule
  congr 1
  unfold pending_jobs
  apply List.filter_congr
  intro j _
  have h_service_eq : service sched1 j t = service sched2 j t := by
    unfold service service_during
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    unfold service_at scheduled_at
    rw [ALL i hi.2]
  simp [h_service_eq]

include H_arrival_times_are_consistent in
theorem scheduler_uses_construction_function :
    ∀ t, scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order t =
    job_to_schedule job_arrival job_cost job_task arr_seq ts time_slot slot_order
      (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) t := by
  intro t
  apply prefix_dependent_schedule_construction
  exact scheduler_depends_only_on_prefix job_arrival job_cost job_task arr_seq ts time_slot slot_order H_arrival_times_are_consistent

end SchedulerTDMA

include H_arrival_times_are_consistent in
theorem scheduler_jobs_must_arrive_to_execute :
    jobs_must_arrive_to_execute job_arrival
      (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) := by
  intro j t SCHED
  simp only [scheduled_at, beq_iff_eq] at SCHED
  rw [scheduler_uses_construction_function job_arrival job_cost job_task arr_seq ts time_slot slot_order H_arrival_times_are_consistent t] at SCHED
  unfold job_to_schedule at SCHED
  have ⟨_, hIN⟩ := findP_in_seq _ _ _ SCHED
  unfold pending_jobs at hIN
  rw [List.mem_filter] at hIN
  have ⟨_, hpred⟩ := hIN
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hpred
  unfold has_arrived
  exact hpred.1

include H_arrival_times_are_consistent in
theorem scheduler_completed_jobs_dont_execute :
    completed_jobs_dont_execute job_cost
      (scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order) := by
  intro j t
  induction t with
  | zero =>
    simp [service, service_during]
  | succ n ih =>
    set sched_tdma := scheduler_tdma job_arrival job_cost job_task arr_seq ts time_slot slot_order with hsched_def
    show ∑ i ∈ Finset.Ico 0 (n + 1), service_at sched_tdma j i ≤ job_cost j
    rw [Finset.sum_Ico_succ_top (Nat.zero_le n)]
    have ih' : ∑ i ∈ Finset.Ico 0 n, service_at sched_tdma j i ≤ job_cost j := ih
    have hsa_le := service_at_most_one sched_tdma j n
    by_cases heq : ∑ i ∈ Finset.Ico 0 n, service_at sched_tdma j i = job_cost j
    · -- service at n = job_cost j, so j is completed at n; service_at n must be 0
      suffices h : service_at sched_tdma j n = 0 by omega
      simp only [service_at, scheduled_at]
      rw [hsched_def, scheduler_uses_construction_function job_arrival job_cost job_task arr_seq ts time_slot slot_order H_arrival_times_are_consistent n]
      unfold job_to_schedule
      -- Need to show findP doesn't return some j
      set P := (fun job =>
          decide
            (((n + TDMA_cycle ts time_slot -
                    Task_slot_offset ts slot_order (job_task job) time_slot %
                      TDMA_cycle ts time_slot) %
                  TDMA_cycle ts time_slot) <
                time_slot (job_task job)))
      set plist := pending_jobs job_arrival job_cost arr_seq sched_tdma n
      cases hfp : findP P plist with
      | none => rfl
      | some val =>
        by_cases hval : val = j
        · exfalso
          -- val = j, so val ∈ pending_jobs, but val is completed at n
          have ⟨_, hIN⟩ := findP_in_seq _ _ _ hfp
          rw [hval] at hIN
          change j ∈ pending_jobs job_arrival job_cost arr_seq sched_tdma n at hIN
          unfold pending_jobs at hIN
          rw [List.mem_filter] at hIN
          have ⟨_, hpred⟩ := hIN
          simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hpred
          apply hpred.2
          show job_cost j ≤ service sched_tdma j n
          unfold service service_during
          exact le_of_eq heq.symm
        · -- val ≠ j, so (some val == some j) = false
          simp [hval]
    · -- service at n < job_cost j
      omega

end ImplementationTDMA

end ConcreteSchedulerTDMA

end Prosa.Classic.Implementation.Uni.Basic.Schedule_tdma
