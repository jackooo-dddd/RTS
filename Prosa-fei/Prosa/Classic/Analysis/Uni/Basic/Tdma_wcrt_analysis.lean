-- Translated from: ../rt-proofs/classic/analysis/uni/basic/tdma_wcrt_analysis.v
import Prosa.Classic.Util.Div_mod
import Prosa.Classic.Util.Nat
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Schedule_of_task
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform_tdma
import Mathlib.Tactic

namespace Prosa.Classic.Analysis.Uni.Basic.Tdma_wcrt_analysis

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Job (valid_realtime_job job_cost_le_task_cost valid_sporadic_job)
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Basic.Platform_tdma
open Prosa.Classic.Model.Policy_tdma
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Util.Div_mod
open Prosa.Util.Div_mod
open Prosa.Util.Seqset

section EndTimeDefs

variable {Job : Type _} [DecidableEq Job]

inductive end_time_predicate_local (sched : schedule Job) (job : Job) :
    Instant → Duration → Instant → Prop where
  | C0_ : ∀ t, end_time_predicate_local sched job t 0 t
  | S_C_not_sched : ∀ t c e,
      ¬(scheduled_at sched job t = true) →
      end_time_predicate_local sched job (t + 1) (c + 1) e →
      end_time_predicate_local sched job t (c + 1) e
  | S_C_sched : ∀ t c e,
      scheduled_at sched job t = true →
      end_time_predicate_local sched job (t + 1) c e →
      end_time_predicate_local sched job t (c + 1) e

def completes_at_local (sched : schedule Job) (job : Job)
    (job_arrival_fn : Job → Time) (job_cost_fn : Job → Time) (t : Instant) :
    Prop :=
  end_time_predicate_local sched job (job_arrival_fn job) (job_cost_fn job) t

theorem completed_by_end_time_aux (sched : schedule Job) (job : Job)
    (job_arrival_fn : Job → Time) (job_cost_fn : Job → Time)
    (H_jobs_must_arrive : jobs_must_arrive_to_execute job_arrival_fn sched)
    (job_end : Instant)
    (hcmpl : completes_at_local sched job job_arrival_fn job_cost_fn job_end) :
    completed_by job_cost_fn sched job job_end := by
  unfold completes_at_local at hcmpl
  unfold completed_by service service_during
  have arrival_le : ∀ t c e, end_time_predicate_local sched job t c e → t ≤ e := by
    intro t c e h
    induction h with
    | C0_ => exact Nat.le_refl _
    | S_C_not_sched _ _ _ _ _ ih => exact Nat.le_of_succ_le ih
    | S_C_sched _ _ _ _ _ ih => exact Nat.le_of_succ_le ih
  have svc_eq : ∀ t c e, end_time_predicate_local sched job t c e →
      ∑ i ∈ Finset.Ico t e, service_at sched job i = c := by
    intro t c e h
    induction h with
    | C0_ t => simp
    | S_C_not_sched t c e hcase hpre ih =>
      have hle : t < e := Nat.lt_of_succ_le (arrival_le _ _ _ hpre)
      rw [Finset.sum_eq_sum_Ico_succ_bot hle, ih]
      unfold service_at; simp [show ¬(scheduled_at sched job t = true) from hcase]
    | S_C_sched t c e hcase hpre ih =>
      have hle : t < e := Nat.lt_of_succ_le (arrival_le _ _ _ hpre)
      rw [Finset.sum_eq_sum_Ico_succ_bot hle, ih]
      unfold service_at; simp [hcase]; ring
  have hle := arrival_le _ _ _ hcmpl
  have hsvc := svc_eq _ _ _ hcmpl
  rw [ignore_service_before_arrival job_arrival_fn sched H_jobs_must_arrive job 0
      job_end (Nat.zero_le _) hle, hsvc]

end EndTimeDefs

section HelperDefs

variable {sporadic_task : Type _} [DecidableEq sporadic_task]

noncomputable def from_start_of_slot_fn
    (ts : SeqSet sporadic_task) (slot_order : TDMA_slot_order sporadic_task)
    (tsk : sporadic_task) (task_time_slot : TDMA_slot sporadic_task)
    (t : Time) : ℕ :=
  (t + TDMA_cycle ts task_time_slot -
    Task_slot_offset ts slot_order tsk task_time_slot % TDMA_cycle ts task_time_slot) %
    TDMA_cycle ts task_time_slot

noncomputable def to_next_slot_fn
    (ts : SeqSet sporadic_task) (slot_order : TDMA_slot_order sporadic_task)
    (tsk : sporadic_task) (task_time_slot : TDMA_slot sporadic_task)
    (t : Time) : ℕ :=
  TDMA_cycle ts task_time_slot -
    from_start_of_slot_fn ts slot_order tsk task_time_slot t

noncomputable def duration_to_finish_from_start_of_slot_with_fn
    (ts : SeqSet sporadic_task)
    (tsk : sporadic_task) (task_time_slot : TDMA_slot sporadic_task)
    (c : Duration) : Duration :=
  (div_ceil c (task_time_slot tsk) - 1) *
    (TDMA_cycle ts task_time_slot - task_time_slot tsk) + c

noncomputable def to_end_of_slot_fn
    (ts : SeqSet sporadic_task) (slot_order : TDMA_slot_order sporadic_task)
    (tsk : sporadic_task) (task_time_slot : TDMA_slot sporadic_task)
    (t : Time) : ℕ :=
  task_time_slot tsk - from_start_of_slot_fn ts slot_order tsk task_time_slot t

instance instDecidableTaskInTimeSlot
    (ts : SeqSet sporadic_task) (slot_order : TDMA_slot_order sporadic_task)
    (tsk : sporadic_task) (task_time_slot : TDMA_slot sporadic_task)
    (t : Time) : Decidable (Task_in_time_slot ts slot_order tsk task_time_slot t) :=
  inferInstanceAs (Decidable (_ < _))

noncomputable def formula_rt_fn
    (ts : SeqSet sporadic_task) (slot_order : TDMA_slot_order sporadic_task)
    (tsk : sporadic_task) (task_time_slot : TDMA_slot sporadic_task)
    (arr : Instant) (c : Duration) : Duration :=
  if c = 0 then 0
  else if Task_in_time_slot ts slot_order tsk task_time_slot arr then
    if c ≤ to_end_of_slot_fn ts slot_order tsk task_time_slot arr then
      c
    else
      to_next_slot_fn ts slot_order tsk task_time_slot arr +
        duration_to_finish_from_start_of_slot_with_fn ts tsk task_time_slot
          (c - to_end_of_slot_fn ts slot_order tsk task_time_slot arr)
  else
    to_next_slot_fn ts slot_order tsk task_time_slot arr +
      duration_to_finish_from_start_of_slot_with_fn ts tsk task_time_slot c

variable {Job : Type _} [DecidableEq Job]

noncomputable def job_response_time_tdma_in_at_most_one_job_is_pending_fn
    (ts : SeqSet sporadic_task) (slot_order : TDMA_slot_order sporadic_task)
    (tsk : sporadic_task) (task_time_slot : TDMA_slot sporadic_task)
    (job_arrival : Job → Time) (job_cost : Job → Time) (j : Job) :
    Duration :=
  formula_rt_fn ts slot_order tsk task_time_slot (job_arrival j) (job_cost j)

noncomputable def WCRT_formula_fn (cycle s wcet : ℕ) : ℕ :=
  div_ceil wcet s * (cycle - s) + wcet

noncomputable def WCRT_fn
    (ts : SeqSet sporadic_task) (task_cost : sporadic_task → Time)
    (tsk : sporadic_task) (task_time_slot : TDMA_slot sporadic_task) : ℕ :=
  WCRT_formula_fn (TDMA_cycle ts task_time_slot) (task_time_slot tsk)
    (task_cost tsk)

end HelperDefs

namespace WCRT_OneJobTDMA

section WCRT_analysis

  variable {sporadic_task : Type _} [DecidableEq sporadic_task]
  variable (task_cost : sporadic_task → Time)
  variable (task_period : sporadic_task → Time)
  variable (task_deadline : sporadic_task → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_deadline : Job → Time)
  variable (job_task : Job → sporadic_task)

  variable (arr_seq : arrival_sequence Job)
  variable (H_sporadic_tasks :
    sporadic_task_model task_period job_arrival job_task arr_seq)

  variable (sched : schedule Job)
  variable (H_jobs_must_arrive_to_execute :
    jobs_must_arrive_to_execute job_arrival sched)
  variable (H_completed_jobs_dont_execute :
    completed_jobs_dont_execute job_cost sched)

  variable (task_time_slot : TDMA_slot sporadic_task)
  variable (slot_order : TDMA_slot_order sporadic_task)

  variable (ts : SeqSet sporadic_task)
  variable (H_valid_task_parameters :
    valid_sporadic_taskset task_cost task_period task_deadline ts._set_seq)

  variable (tsk : sporadic_task)
  variable (H_task_in_task_set : tsk ∈ ts)

  variable (j : Job)
  variable (H_job_task : job_task j = tsk)
  variable (job_in_arr_seq : arrives_in arr_seq j)
  variable (H_valid_job :
    valid_realtime_job job_cost job_deadline j ∧
    job_cost j ≤ task_cost (job_task j) ∧
    job_deadline j = task_deadline (job_task j))

  variable (H_valid_time_slot : is_valid_time_slot tsk task_time_slot)

  variable (TDMA_policy_hyp :
    Respects_TDMA_policy job_arrival job_cost job_task arr_seq sched
      ts task_time_slot slot_order)

  variable (all_previous_jobs_of_same_task_completed :
    ∀ j_other,
      arrives_in arr_seq j_other →
      job_task j = job_task j_other →
      job_arrival j_other < job_arrival j →
      completed_by job_cost sched j_other (job_arrival j))

  section BasicLemmas

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task H_valid_job H_valid_time_slot all_previous_jobs_of_same_task_completed in
    theorem at_most_one_job_is_pending :
        ∀ (j_other : Job) (t : Time),
          arrives_in arr_seq j_other →
          job_arrival j_other < job_arrival j →
          pending job_arrival job_cost sched j t →
          pending job_arrival job_cost sched j_other t →
          job_task j = job_task j_other → j = j_other := by
      intro j_other t ARRJO ARRBF ⟨ARREDJ, NCOMJ⟩ ⟨ARREDJO, NCOMJO⟩ EQTSK
      -- j_other completed by job_arrival j (by hypothesis)
      have hcomp_arr := all_previous_jobs_of_same_task_completed j_other ARRJO EQTSK ARRBF
      -- j is pending at t, so has_arrived j t, i.e., job_arrival j ≤ t
      have harr_le : job_arrival j ≤ t := ARREDJ
      -- By completion_monotonic, j_other is completed at t
      have hcomp_t := completion_monotonic job_cost sched j_other (job_arrival j) t harr_le hcomp_arr
      -- But j_other is pending at t, so NOT completed at t
      exact absurd hcomp_t NCOMJO

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem TDMA_policy_case_RT_le_Period :
        ∀ (t : Time),
          pending job_arrival job_cost sched j t →
          (Task_in_time_slot ts slot_order tsk task_time_slot t ↔
           scheduled_at sched j t = true) := by
      intro t PEN
      have hslot_equiv : ∀ t', Task_in_time_slot ts slot_order (job_task j) task_time_slot t' ↔
          Task_in_time_slot ts slot_order tsk task_time_slot t' := by
        intro t'; rw [H_job_task]
      constructor
      · -- in_slot → scheduled
        intro HSLOT
        by_contra NSCHED
        push_neg at NSCHED
        -- j is backlogged
        have BACKLOG : backlogged job_arrival job_cost sched j t :=
          ⟨PEN, NSCHED⟩
        -- Apply TDMA policy to get the disjunction
        have ⟨_, HBACK⟩ := TDMA_policy_hyp j t job_in_arr_seq
        have HCASES := HBACK BACKLOG
        rcases HCASES with NINSLOT | ⟨j_other, ARRJO, ARRBF, SAME, SCHEDJO⟩
        · -- Case: j not in its time slot
          exact NINSLOT ((hslot_equiv t).mpr HSLOT)
        · -- Case: ∃ j_other earlier with same task, scheduled
          have PEND_OTHER : pending job_arrival job_cost sched j_other t :=
            scheduled_implies_pending job_arrival job_cost sched
              H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute j_other t SCHEDJO
          exfalso
          -- Inline at_most_one_job_is_pending logic
          have hcomp_arr := all_previous_jobs_of_same_task_completed j_other ARRJO SAME ARRBF
          have harr_le : job_arrival j ≤ t := PEN.1
          have hcomp_t := completion_monotonic job_cost sched j_other (job_arrival j) t harr_le hcomp_arr
          exact PEND_OTHER.2 hcomp_t
      · -- scheduled → in_slot
        intro HSCHED
        have ⟨HIMPL, _⟩ := TDMA_policy_hyp j t job_in_arr_seq
        exact (hslot_equiv t).mp (HIMPL HSCHED)

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task H_valid_job H_valid_time_slot all_previous_jobs_of_same_task_completed in
    theorem pendingArrival :
        pending job_arrival job_cost sched j (job_arrival j) := by
      unfold pending
      refine ⟨le_refl _, ?_⟩
      intro hcomp
      unfold completed_by service service_during at hcomp
      rw [ignore_service_before_arrival job_arrival sched H_jobs_must_arrive_to_execute j 0 (job_arrival j) (Nat.zero_le _) (le_refl _)] at hcomp
      rw [Finset.Ico_self] at hcomp
      simp at hcomp
      have hpos : job_cost j > 0 := H_valid_job.1.1
      simp only [Time] at *; omega

    theorem pendingSt :
        ∀ (t : Time),
          pending job_arrival job_cost sched j t →
          scheduled_at sched j t = false →
          pending job_arrival job_cost sched j (t + 1) := by
      intro t ⟨HARR, NCOMP⟩ NSCHED
      unfold pending has_arrived
      refine ⟨by unfold has_arrived at HARR; simp only [Time] at *; omega, ?_⟩
      intro hcomp
      apply NCOMP
      unfold completed_by service service_during at hcomp ⊢
      have hsa : service_at sched j t = 0 := by
        unfold service_at; simp [NSCHED]
      have hsplit : ∑ i ∈ Finset.Ico 0 (t + 1), service_at sched j i =
          ∑ i ∈ Finset.Ico 0 t, service_at sched j i +
          ∑ i ∈ Finset.Ico t (t + 1), service_at sched j i := by
        rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le t) (by simp only [Time] at *; omega)]
      rw [hsplit] at hcomp
      have hone : ∑ i ∈ Finset.Ico t (t + 1), service_at sched j i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi; rw [Finset.mem_Ico] at hi
        have : i = t := by simp only [Time] at *; omega
        rw [this]; exact hsa
      simp only [hone, Nat.add_zero] at hcomp
      convert hcomp using 1

    theorem pendingSt_Sched :
        ∀ (t : Time) (c : ℕ),
          pending job_arrival job_cost sched j t →
          service sched j t + (c + 2) = job_cost j →
          scheduled_at sched j t = true →
          pending job_arrival job_cost sched j (t + 1) := by
      intro t c ⟨HARR, NCOMP⟩ COST SCHED
      unfold pending has_arrived
      refine ⟨by unfold has_arrived at HARR; simp only [Time] at *; omega, ?_⟩
      intro hcomp
      unfold completed_by service service_during at hcomp
      have hsa : service_at sched j t = 1 := by
        unfold service_at; simp [SCHED]
      have hsplit : ∑ i ∈ Finset.Ico 0 (t + 1), service_at sched j i =
          ∑ i ∈ Finset.Ico 0 t, service_at sched j i +
          ∑ i ∈ Finset.Ico t (t + 1), service_at sched j i := by
        rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le t) (by simp only [Time] at *; omega)]
      rw [hsplit] at hcomp
      have hone : ∑ i ∈ Finset.Ico t (t + 1), service_at sched j i = service_at sched j t := by
        have hsing : Finset.Ico t (t + 1) = {t} := by
          ext x; simp only [Finset.mem_Ico, Finset.mem_singleton, Time] at *; omega
        rw [hsing, Finset.sum_singleton]
      rw [hone, hsa] at hcomp
      unfold service service_during at COST
      simp only [Time] at *
      omega

  end BasicLemmas

  section formula_predicate_eq

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task H_valid_job H_valid_time_slot all_previous_jobs_of_same_task_completed in
    theorem to_next_slot_pos :
        ∀ (t : Time),
          to_next_slot_fn ts slot_order tsk task_time_slot t > 0 := by
      intro t
      unfold to_next_slot_fn from_start_of_slot_fn
      have hcycle_pos : TDMA_cycle ts task_time_slot > 0 :=
        TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
      have hmod_lt := Nat.mod_lt
        (t + TDMA_cycle ts task_time_slot - Task_slot_offset ts slot_order tsk task_time_slot % TDMA_cycle ts task_time_slot)
        hcycle_pos
      omega

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task H_valid_job H_valid_time_slot all_previous_jobs_of_same_task_completed in
    theorem lt_to_next_slot_1LR :
        ∀ (a : ℕ) (t : Time),
          a + 1 < to_next_slot_fn ts slot_order tsk task_time_slot t →
          a < to_next_slot_fn ts slot_order tsk task_time_slot (t + 1) := by
      intro a t h
      unfold to_next_slot_fn from_start_of_slot_fn at h ⊢
      set cycle := TDMA_cycle ts task_time_slot
      set offset := Task_slot_offset ts slot_order tsk task_time_slot
      have hcycle_pos : cycle > 0 :=
        TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
      have hmod_lt : offset % cycle < cycle := Nat.mod_lt offset hcycle_pos
      have hle : offset % cycle ≤ cycle := Nat.le_of_lt hmod_lt
      have hcsub : cycle - offset % cycle ≤ cycle := Nat.sub_le cycle (offset % cycle)
      -- Rewrite subtractions using Nat.add_sub_assoc
      rw [Nat.add_sub_assoc hle t] at h
      rw [Nat.add_sub_assoc hle (t + 1)]
      -- Note: t + 1 + (cycle - offset % cycle) = (t + (cycle - offset % cycle)) + 1
      have hkey : t + 1 + (cycle - offset % cycle) = (t + (cycle - offset % cycle)) + 1 := by
        rw [Nat.add_right_comm]
      rw [hkey]
      set x := t + (cycle - offset % cycle)
      rcases modnSor' x cycle with h1 | h1
      · -- Case 1: (x + 1) % cycle = x % cycle + 1
        rw [h1]
        have := Nat.mod_lt x hcycle_pos
        omega
      · -- Case 2: (x + 1) % cycle = 0
        rw [h1]
        have := Nat.mod_lt x hcycle_pos
        omega

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task H_valid_job H_valid_time_slot all_previous_jobs_of_same_task_completed in
    theorem lt_to_next_slot_LR :
        ∀ (b a : ℕ) (t : Time),
          a + b < to_next_slot_fn ts slot_order tsk task_time_slot t →
          a < to_next_slot_fn ts slot_order tsk task_time_slot (t + b) := by
      intro b
      induction b with
      | zero => intro a t h; simp only [Nat.add_zero] at h ⊢; exact h
      | succ b' ih =>
        intro a t h
        have h1 : (a + 1) + b' < to_next_slot_fn ts slot_order tsk task_time_slot t := by
          simp only [Time] at *; omega
        have h2 := ih (a + 1) t h1
        have heq : t + (b' + 1) = (t + b') + 1 := by simp only [Time] at *; omega
        rw [heq]
        exact @lt_to_next_slot_1LR sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task H_valid_job H_valid_time_slot all_previous_jobs_of_same_task_completed a (t + b') h2

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem S_t_not_sched :
        ∀ (t : Time),
          pending job_arrival job_cost sched j t →
          scheduled_at sched j t = false →
          1 < to_next_slot_fn ts slot_order tsk task_time_slot t →
          scheduled_at sched j (t + 1) = false := by
      intro t PEN NSCHED HLT
      -- Use TDMA_policy to get slot ↔ scheduled for pending jobs
      have SLOT_IFF := TDMA_policy_case_RT_le_Period task_cost task_period task_deadline
        job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot
        slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task
        job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed
        t PEN
      -- At t: not scheduled → not in slot
      have NSLOT : ¬Task_in_time_slot ts slot_order tsk task_time_slot t := by
        intro hslot; exact absurd (SLOT_IFF.mp hslot) (by simp [NSCHED])
      -- Pending at t+1
      have PEN1 := pendingSt job_arrival job_cost sched j t PEN NSCHED
      have SLOT_IFF1 := TDMA_policy_case_RT_le_Period task_cost task_period task_deadline
        job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot
        slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task
        job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed
        (t + 1) PEN1
      -- Suffices to show not in time slot at t+1
      by_contra HSCHED
      push_neg at HSCHED
      simp only [Bool.not_eq_false] at HSCHED
      have HSLOT1 := SLOT_IFF1.mpr HSCHED
      -- Now derive contradiction from modular arithmetic
      unfold Task_in_time_slot at NSLOT HSLOT1
      unfold to_next_slot_fn from_start_of_slot_fn at HLT
      set cycle := TDMA_cycle ts task_time_slot
      set offset := Task_slot_offset ts slot_order tsk task_time_slot
      have hcycle_pos : cycle > 0 :=
        TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
      have hmod_bound := Nat.mod_lt
        (t + cycle - offset % cycle) hcycle_pos
      rw [Nat.not_lt] at NSLOT
      -- from_start_of_slot t ≥ time_slot (NSLOT), and 1 < cycle - from_start_of_slot t (HLT)
      -- So from_start_of_slot t < cycle - 1, meaning from_start_of_slot (t+1) = from_start_of_slot t + 1
      -- which is still ≥ time_slot
      have hle : offset % cycle ≤ cycle := Nat.le_of_lt (Nat.mod_lt offset hcycle_pos)
      have hle2 : offset % cycle ≤ t + cycle := Nat.le_trans hle (Nat.le_add_left cycle t)
      have hle3 : offset % cycle ≤ t + 1 + cycle := Nat.le_trans hle (Nat.le_add_left cycle (t + 1))
      have hkey : t + 1 + cycle - offset % cycle = (t + cycle - offset % cycle) + 1 := by
        rw [show t + 1 + cycle = (t + cycle) + 1 from by ring]
        exact Nat.succ_sub hle2
      rw [hkey] at HSLOT1
      set m := (t + cycle - offset % cycle) % cycle with hm_def
      -- Since 1 < cycle - m (HLT), m + 1 < cycle, so no modular wrap-around
      have hm_le_cycle : m ≤ cycle := Nat.le_of_lt hmod_bound
      have hm1_lt : m + 1 < cycle := by zify [hm_le_cycle] at HLT ⊢; omega
      have hmod_succ : ((t + cycle - offset % cycle) + 1) % cycle = m + 1 := by
        rw [(Nat.div_add_mod (t + cycle - offset % cycle) cycle).symm,
            Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt hm1_lt]
      rw [hmod_succ] at HSLOT1
      -- HSLOT1 : m + 1 < task_time_slot tsk, NSLOT : task_time_slot tsk ≤ m
      exact absurd (lt_of_lt_of_le HSLOT1 NSLOT) (not_lt.mpr (Nat.le_add_right m 1))

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem duration_not_sched :
        ∀ (t : Time),
          pending job_arrival job_cost sched j t →
          scheduled_at sched j t = false →
          ∀ (d : ℕ),
            d < to_next_slot_fn ts slot_order tsk task_time_slot t →
            scheduled_at sched j (t + d) = false ∧
            pending job_arrival job_cost sched j (t + d) := by
      intro t PEN NSCHED d
      induction d with
      | zero => intro _; simp only [Nat.add_zero]; exact ⟨NSCHED, PEN⟩
      | succ d' ih =>
        intro hlt
        have hd'lt : d' < to_next_slot_fn ts slot_order tsk task_time_slot t :=
          Nat.lt_of_succ_lt hlt
        have ⟨hnsched_d', hpend_d'⟩ := ih hd'lt
        have heq : t + (d' + 1) = (t + d') + 1 := by simp only [Time] at *; omega
        rw [heq]
        have hpend1 := pendingSt job_arrival job_cost sched j (t + d') hpend_d' hnsched_d'
        have h1lt : 1 < to_next_slot_fn ts slot_order tsk task_time_slot (t + d') := by
          have := @lt_to_next_slot_LR sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task H_valid_job H_valid_time_slot all_previous_jobs_of_same_task_completed d' 1 t (by simp only [Time] at *; omega)
          exact this
        have hnsched1 := @S_t_not_sched sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed (t + d') hpend_d' hnsched_d' h1lt
        exact ⟨hnsched1, hpend1⟩

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem pending_Nsched_sched :
        ∀ (t : Time),
          pending job_arrival job_cost sched j t →
          scheduled_at sched j t = false →
          pending job_arrival job_cost sched j
            (t + to_next_slot_fn ts slot_order tsk task_time_slot t) := by
      intro t PEN NSCHED
      have NEXT : to_next_slot_fn ts slot_order tsk task_time_slot t > 0 := by
        unfold to_next_slot_fn from_start_of_slot_fn
        have hcycle_pos : TDMA_cycle ts task_time_slot > 0 :=
          TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
        have := Nat.mod_lt (t + TDMA_cycle ts task_time_slot - Task_slot_offset ts slot_order tsk task_time_slot % TDMA_cycle ts task_time_slot) hcycle_pos
        omega
      set nxt := to_next_slot_fn ts slot_order tsk task_time_slot t
      have hd : nxt - 1 < nxt := Nat.sub_lt (by omega) (by omega)
      have hdur := @duration_not_sched sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN NSCHED (nxt - 1) hd
      have heq : t + nxt = (t + (nxt - 1)) + 1 := by simp only [nxt, Time] at *; omega
      rw [heq]
      exact pendingSt job_arrival job_cost sched j _ hdur.2 hdur.1

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem at_next_start_of_slot_schedulabe :
        ∀ (t : Time),
          pending job_arrival job_cost sched j t →
          scheduled_at sched j t = false →
          scheduled_at sched j
            (t + to_next_slot_fn ts slot_order tsk task_time_slot t) = true := by
      intro t PEN NSCHED
      have hcycle_pos : TDMA_cycle ts task_time_slot > 0 :=
        TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
      have hslot_pos : task_time_slot tsk > 0 := H_valid_time_slot
      -- pending at t + to_next_slot t
      have PENS := pending_Nsched_sched task_cost task_period task_deadline
        job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot
        slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task
        job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed
        t PEN NSCHED
      have SLOT_IFF := TDMA_policy_case_RT_le_Period task_cost task_period task_deadline
        job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot
        slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task
        job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed
        (t + to_next_slot_fn ts slot_order tsk task_time_slot t) PENS
      apply SLOT_IFF.mp
      -- Show Task_in_time_slot at t + to_next_slot t
      unfold Task_in_time_slot to_next_slot_fn from_start_of_slot_fn
      set cycle := TDMA_cycle ts task_time_slot
      set offset := Task_slot_offset ts slot_order tsk task_time_slot
      have hmod_lt : offset % cycle < cycle := Nat.mod_lt offset hcycle_pos
      have hle : offset % cycle ≤ cycle := Nat.le_of_lt hmod_lt
      -- t + (cycle - from_start) + cycle - offset % cycle
      -- = t + cycle - offset % cycle + (cycle - (t + cycle - offset % cycle) % cycle)
      -- The key is that from_start_of_slot + to_next_slot = cycle
      -- So (t + to_next_slot + cycle - offset % cycle) % cycle = 0
      have hkey : (t + (cycle - (t + cycle - offset % cycle) % cycle) + cycle - offset % cycle) % cycle = 0 := by
        set n := t + cycle - offset % cycle
        have hx_lt : n % cycle < cycle := Nat.mod_lt n hcycle_pos
        have hx_le_n : n % cycle ≤ n := Nat.mod_le n cycle
        have ho_le : offset % cycle ≤ t + cycle := Nat.le_trans hle (Nat.le_add_left cycle t)
        have h_xle : n % cycle ≤ cycle := Nat.le_of_lt hx_lt
        -- Key: t + (cycle - n%cycle) + cycle - offset%cycle = n - n%cycle + cycle
        -- n = t + cycle - o, so n - n%c = n/c * c
        -- t + (cycle - n%c) + cycle - o = t + cycle - n%c + cycle - o = (n + cycle) - n%c - o + o - o
        -- Actually: t + (cycle - n%c) = t + cycle - n%c (since n%c ≤ cycle)
        -- And t + cycle - n%c + cycle - o = t + 2*cycle - n%c - o = (n + o) + cycle - n%c - o = n + cycle - n%c = n - n%c + cycle
        have heq : t + (cycle - n % cycle) + cycle - offset % cycle = n - n % cycle + cycle := by
          have h_n_def : n = t + cycle - offset % cycle := rfl
          have hr_le_n : n % cycle ≤ n := Nat.mod_le n cycle
          have h_o_le_lhs : offset % cycle ≤ t + (cycle - n % cycle) + cycle := by
            calc offset % cycle ≤ cycle := Nat.le_of_lt hmod_lt
                 _ ≤ t + (cycle - n % cycle) + cycle := Nat.le_add_left _ _
          zify [h_xle, hr_le_n, h_o_le_lhs, ho_le]
          omega
        rw [heq]
        have hdiv : n - n % cycle = n / cycle * cycle := by
          have h := Nat.div_add_mod n cycle
          zify [Nat.mod_le n cycle] at h ⊢; linarith
        rw [hdiv]
        rw [Nat.mul_comm, ← Nat.mul_succ]
        exact Nat.mul_mod_right cycle _
      rw [hkey]
      exact hslot_pos

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem formula_not_sched_St :
        ∀ (t : Time) (c : ℕ),
          pending job_arrival job_cost sched j t →
          scheduled_at sched j t = false →
          t + formula_rt_fn ts slot_order tsk task_time_slot t (c + 1) =
            (t + 1) + formula_rt_fn ts slot_order tsk task_time_slot (t + 1) (c + 1) := by
      intro t c PEN NSCHED
      have hcycle_pos : TDMA_cycle ts task_time_slot > 0 :=
        TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
      have hslot_pos : task_time_slot tsk > 0 := H_valid_time_slot
      have hcycle_ge_slot : TDMA_cycle ts task_time_slot ≥ task_time_slot tsk :=
        TDMA_cycle_ge_each_time_slot ts tsk H_task_in_task_set task_time_slot
      set cycle := TDMA_cycle ts task_time_slot with hcycle_def
      set offset := Task_slot_offset ts slot_order tsk task_time_slot with hoffset_def
      have hoffset_lt : offset % cycle < cycle := Nat.mod_lt offset hcycle_pos
      have hoffset_le : offset % cycle ≤ cycle := Nat.le_of_lt hoffset_lt
      -- ¬in_slot(t) from TDMA policy
      have SLOT_IFF := @TDMA_policy_case_RT_le_Period sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN
      have NSLOT : ¬Task_in_time_slot ts slot_order tsk task_time_slot t := by
        intro hslot; exact absurd (SLOT_IFF.mp hslot) (by simp [NSCHED])
      -- Compute LHS: formula_rt(t, c+1) = ns(t) + dur(c+1) since ¬in_slot(t)
      have hrt_t : formula_rt_fn ts slot_order tsk task_time_slot t (c + 1) =
          to_next_slot_fn ts slot_order tsk task_time_slot t +
          duration_to_finish_from_start_of_slot_with_fn ts tsk task_time_slot (c + 1) := by
        unfold formula_rt_fn
        rw [if_neg (show ¬(c + 1 = 0) from by omega), if_neg NSLOT]
      -- from_start analysis via modnSor'
      set x := t + cycle - offset % cycle
      have hxle : offset % cycle ≤ t + cycle := Nat.le_trans hoffset_le (Nat.le_add_left cycle t)
      have hx1 : t + 1 + cycle - offset % cycle = x + 1 := by
        rw [show t + 1 + cycle = (t + cycle) + 1 from by ring]
        exact Nat.succ_sub hxle
      -- Pre-compute from_start equalities for reuse
      have h_fs_t : from_start_of_slot_fn ts slot_order tsk task_time_slot t = x % cycle := rfl
      have h_fs_t1 : from_start_of_slot_fn ts slot_order tsk task_time_slot (t + 1) =
          (x + 1) % cycle := by
        show (t + 1 + cycle - offset % cycle) % cycle = (x + 1) % cycle; rw [hx1]
      rcases modnSor' x cycle with h_inc | h_wrap
      · -- Case A: from_start(t+1) = from_start(t) + 1 (no wrap) → ¬in_slot(t+1)
        have NSLOT1 : ¬Task_in_time_slot ts slot_order tsk task_time_slot (t + 1) := by
          show ¬((t + 1 + cycle - offset % cycle) % cycle < task_time_slot tsk)
          rw [hx1, h_inc]
          exact fun h => NSLOT (Nat.lt_of_succ_lt h)
        have hrt_t1 : formula_rt_fn ts slot_order tsk task_time_slot (t + 1) (c + 1) =
            to_next_slot_fn ts slot_order tsk task_time_slot (t + 1) +
            duration_to_finish_from_start_of_slot_with_fn ts tsk task_time_slot (c + 1) := by
          unfold formula_rt_fn
          rw [if_neg (show ¬(c + 1 = 0) from by omega), if_neg NSLOT1]
        rw [hrt_t, hrt_t1]
        -- Goal: t + (ns(t) + dur) = (t+1) + (ns(t+1) + dur), i.e., t + ns(t) = t+1 + ns(t+1)
        have hns_eq : to_next_slot_fn ts slot_order tsk task_time_slot t =
            to_next_slot_fn ts slot_order tsk task_time_slot (t + 1) + 1 := by
          simp only [to_next_slot_fn, h_fs_t, h_fs_t1, h_inc, ← hcycle_def]
          have h_bound : x % cycle + 1 < cycle := by rw [← h_inc]; exact Nat.mod_lt _ hcycle_pos
          zify [le_of_lt (Nat.mod_lt x hcycle_pos), le_of_lt h_bound]; omega
        rw [hns_eq]; ring
      · -- Case B: from_start(t+1) = 0 (mod wrap) → in_slot(t+1)
        have HSLOT1 : Task_in_time_slot ts slot_order tsk task_time_slot (t + 1) := by
          show (t + 1 + cycle - offset % cycle) % cycle < task_time_slot tsk
          rw [hx1, h_wrap]; exact hslot_pos
        have hfs_max : x % cycle = cycle - 1 := by
          have h := modnS_eq x (cycle - 1)
          rw [Nat.sub_add_cancel hcycle_pos] at h
          exact h.mp h_wrap
        have hns_t : to_next_slot_fn ts slot_order tsk task_time_slot t = 1 := by
          simp only [to_next_slot_fn, h_fs_t, hfs_max, ← hcycle_def]
          exact Nat.sub_sub_self (Nat.succ_le_of_lt hcycle_pos)
        have hte1 : to_end_of_slot_fn ts slot_order tsk task_time_slot (t + 1) =
            task_time_slot tsk := by
          simp only [to_end_of_slot_fn, h_fs_t1, h_wrap]; simp
        by_cases hc_le : c + 1 ≤ to_end_of_slot_fn ts slot_order tsk task_time_slot (t + 1)
        · -- Sub-case B1: c+1 ≤ ts_val → formula_rt(t+1,c+1) = c+1
          have hrt_t1 : formula_rt_fn ts slot_order tsk task_time_slot (t + 1) (c + 1) =
              c + 1 := by
            unfold formula_rt_fn
            rw [if_neg (show ¬(c + 1 = 0) from by omega), if_pos HSLOT1, if_pos hc_le]
          rw [hrt_t, hrt_t1, hns_t]
          rw [hte1] at hc_le
          simp only [duration_to_finish_from_start_of_slot_with_fn, ← hcycle_def]
          have hceil1 : div_ceil (c + 1) (task_time_slot tsk) = 1 :=
            ceil_eq1 (c + 1) (task_time_slot tsk) (by omega) hc_le
          rw [hceil1]; simp only [Time] at *; omega
        · -- Sub-case B2: c+1 > ts_val
          rw [hte1] at hc_le; push_neg at hc_le
          have hrt_t1 : formula_rt_fn ts slot_order tsk task_time_slot (t + 1) (c + 1) =
              to_next_slot_fn ts slot_order tsk task_time_slot (t + 1) +
              duration_to_finish_from_start_of_slot_with_fn ts tsk task_time_slot
                (c + 1 - task_time_slot tsk) := by
            unfold formula_rt_fn
            rw [if_neg (show ¬(c + 1 = 0) from by omega), if_pos HSLOT1,
                if_neg (show ¬(c + 1 ≤ to_end_of_slot_fn ts slot_order tsk task_time_slot (t + 1))
                  from by rw [hte1]; omega), hte1]
          rw [hrt_t, hrt_t1, hns_t]
          have hns1 : to_next_slot_fn ts slot_order tsk task_time_slot (t + 1) = cycle := by
            simp only [to_next_slot_fn, h_fs_t1, h_wrap, ← hcycle_def]
            exact Nat.sub_zero cycle
          rw [hns1]
          simp only [duration_to_finish_from_start_of_slot_with_fn, ← hcycle_def]
          have hceila : div_ceil (c + 1) (task_time_slot tsk) =
              div_ceil (c + 1 - task_time_slot tsk) (task_time_slot tsk) + 1 :=
            ceil_suba (c + 1) (task_time_slot tsk) hslot_pos hc_le
          rw [hceila]
          have hceil_pos : div_ceil (c + 1 - task_time_slot tsk) (task_time_slot tsk) ≥ 1 := by
            unfold div_ceil
            split_ifs with hdvd
            · exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hslot_pos
            · exact Nat.le_add_left 1 _
          simp only [Time] at *
          clear_value cycle x offset
          have hne1 : div_ceil (c + 1 - task_time_slot tsk) (task_time_slot tsk) + 1 - 1 =
              div_ceil (c + 1 - task_time_slot tsk) (task_time_slot tsk) := by
            simp [Nat.add_sub_cancel]
          rw [hne1]
          zify [hceil_pos, hcycle_ge_slot, hc_le.le]; nlinarith

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem formula_sched_St :
        ∀ (t : Time) (c : ℕ),
          scheduled_at sched j t = true →
          t + formula_rt_fn ts slot_order tsk task_time_slot t (c + 1) =
            (t + 1) + formula_rt_fn ts slot_order tsk task_time_slot (t + 1) c := by
      intro t c SCHED
      have hcycle_pos : TDMA_cycle ts task_time_slot > 0 :=
        TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
      have hslot_pos : task_time_slot tsk > 0 := H_valid_time_slot
      have hcycle_ge_slot : TDMA_cycle ts task_time_slot ≥ task_time_slot tsk :=
        TDMA_cycle_ge_each_time_slot ts tsk H_task_in_task_set task_time_slot
      set cycle := TDMA_cycle ts task_time_slot with hcycle_def
      set offset := Task_slot_offset ts slot_order tsk task_time_slot with hoffset_def
      have hoffset_lt : offset % cycle < cycle := Nat.mod_lt offset hcycle_pos
      have hoffset_le : offset % cycle ≤ cycle := Nat.le_of_lt hoffset_lt
      -- Derive pending and in_slot from scheduled
      have PEN : pending job_arrival job_cost sched j t :=
        scheduled_implies_pending job_arrival job_cost sched
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute j t SCHED
      have SLOT_IFF := @TDMA_policy_case_RT_le_Period sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN
      have HSLOT : Task_in_time_slot ts slot_order tsk task_time_slot t :=
        SLOT_IFF.mpr (by simp [SCHED])
      -- Modular arithmetic setup
      set x := t + cycle - offset % cycle
      have hxle : offset % cycle ≤ t + cycle := Nat.le_trans hoffset_le (Nat.le_add_left cycle t)
      have hx1 : t + 1 + cycle - offset % cycle = x + 1 := by
        rw [show t + 1 + cycle = (t + cycle) + 1 from by ring]
        exact Nat.succ_sub hxle
      have h_fs_t : from_start_of_slot_fn ts slot_order tsk task_time_slot t = x % cycle := rfl
      have h_fs_t1 : from_start_of_slot_fn ts slot_order tsk task_time_slot (t + 1) =
          (x + 1) % cycle := by
        show (t + 1 + cycle - offset % cycle) % cycle = (x + 1) % cycle; rw [hx1]
      -- in_slot(t) means from_start(t) < task_time_slot
      have h_in_t : x % cycle < task_time_slot tsk := HSLOT
      -- Pre-compute to_end_of_slot
      have h_te_t : to_end_of_slot_fn ts slot_order tsk task_time_slot t =
          task_time_slot tsk - x % cycle := by
        simp only [to_end_of_slot_fn, h_fs_t]
      have hte_pos : to_end_of_slot_fn ts slot_order tsk task_time_slot t ≥ 1 := by
        show task_time_slot tsk - from_start_of_slot_fn ts slot_order tsk task_time_slot t ≥ 1
        exact Nat.sub_pos_of_lt HSLOT
      -- LHS: formula_rt(t, c+1) with in_slot(t)
      have hrt_lhs_ite : formula_rt_fn ts slot_order tsk task_time_slot t (c + 1) =
          if c + 1 ≤ to_end_of_slot_fn ts slot_order tsk task_time_slot t then c + 1
          else to_next_slot_fn ts slot_order tsk task_time_slot t +
            duration_to_finish_from_start_of_slot_with_fn ts tsk task_time_slot
              (c + 1 - to_end_of_slot_fn ts slot_order tsk task_time_slot t) := by
        unfold formula_rt_fn
        rw [if_neg (show ¬(c + 1 = 0) from by omega), if_pos HSLOT]
      -- Case c = 0
      by_cases hc : c = 0
      · -- c = 0: formula_rt(t, 1) = 1, formula_rt(t+1, 0) = 0
        subst hc; rw [hrt_lhs_ite, if_pos hte_pos]
        simp only [formula_rt_fn, ite_true, Nat.zero_add, Nat.add_zero]
      · -- c ≥ 1
        rcases modnSor' x cycle with h_inc | h_wrap
        · -- Case A: no wrap, from_start(t+1) = from_start(t) + 1
          have h_te_t1 : to_end_of_slot_fn ts slot_order tsk task_time_slot (t + 1) =
              task_time_slot tsk - (x + 1) % cycle := by
            simp only [to_end_of_slot_fn, h_fs_t1]
          have hns_rel : to_next_slot_fn ts slot_order tsk task_time_slot t =
              to_next_slot_fn ts slot_order tsk task_time_slot (t + 1) + 1 := by
            simp only [to_next_slot_fn, h_fs_t, h_fs_t1, h_inc, ← hcycle_def]
            have h_bound : x % cycle + 1 < cycle := by rw [← h_inc]; exact Nat.mod_lt _ hcycle_pos
            zify [le_of_lt (Nat.mod_lt x hcycle_pos), le_of_lt h_bound]; omega
          by_cases h_in_t1 : (x + 1) % cycle < task_time_slot tsk
          · -- Case A1: in_slot(t+1)
            have HSLOT1 : Task_in_time_slot ts slot_order tsk task_time_slot (t + 1) := by
              show (t + 1 + cycle - offset % cycle) % cycle < task_time_slot tsk
              rw [hx1]; exact h_in_t1
            have hte_rel : to_end_of_slot_fn ts slot_order tsk task_time_slot t =
                to_end_of_slot_fn ts slot_order tsk task_time_slot (t + 1) + 1 := by
              rw [h_te_t, h_te_t1, h_inc]
              have : x % cycle + 1 < task_time_slot tsk := by rw [h_inc] at h_in_t1; exact h_in_t1
              omega
            by_cases hle : c + 1 ≤ to_end_of_slot_fn ts slot_order tsk task_time_slot t
            · -- c+1 ≤ te(t) → c ≤ te(t+1)
              have hle1 : c ≤ to_end_of_slot_fn ts slot_order tsk task_time_slot (t + 1) := by omega
              rw [hrt_lhs_ite, if_pos hle]
              unfold formula_rt_fn
              rw [if_neg hc, if_pos HSLOT1, if_pos hle1]; ring
            · -- c+1 > te(t) → c > te(t+1)
              push_neg at hle
              have hgt1 : ¬(c ≤ to_end_of_slot_fn ts slot_order tsk task_time_slot (t + 1)) := by omega
              rw [hrt_lhs_ite, if_neg (by omega)]
              unfold formula_rt_fn
              rw [if_neg hc, if_pos HSLOT1, if_neg hgt1]
              have harg_eq : c + 1 - to_end_of_slot_fn ts slot_order tsk task_time_slot t =
                  c - to_end_of_slot_fn ts slot_order tsk task_time_slot (t + 1) := by omega
              rw [harg_eq, hns_rel]; ring
          · -- Case A2: ¬in_slot(t+1)
            push_neg at h_in_t1
            rw [h_inc] at h_in_t1
            -- h_in_t1 : task_time_slot tsk ≤ x % cycle + 1
            have NSLOT1 : ¬Task_in_time_slot ts slot_order tsk task_time_slot (t + 1) := by
              show ¬((t + 1 + cycle - offset % cycle) % cycle < task_time_slot tsk)
              rw [hx1, h_inc]; exact not_lt.mpr h_in_t1
            -- from_start(t)+1 = ts ⟹ from_start(t) = ts - 1
            have heq : x % cycle + 1 = task_time_slot tsk :=
              le_antisymm (Nat.succ_le_of_lt h_in_t) h_in_t1
            have h_fs_eq : x % cycle = task_time_slot tsk - 1 := by
              rw [← heq, Nat.add_sub_cancel]
            have hte_t_eq1 : to_end_of_slot_fn ts slot_order tsk task_time_slot t = 1 := by
              rw [h_te_t, h_fs_eq]
              exact Nat.sub_sub_self (Nat.succ_le_of_lt hslot_pos)
            -- c+1 > te(t)=1 since c ≥ 1
            have hgt : ¬(c + 1 ≤ to_end_of_slot_fn ts slot_order tsk task_time_slot t) := by
              rw [hte_t_eq1]; omega
            rw [hrt_lhs_ite, if_neg hgt, hte_t_eq1, show c + 1 - 1 = c from by omega]
            unfold formula_rt_fn; rw [if_neg hc, if_neg NSLOT1, hns_rel]; ring
        · -- Case B: wrap, (x+1)%cycle = 0
          have hfs_max : x % cycle = cycle - 1 := by
            have h := modnS_eq x (cycle - 1)
            rw [Nat.sub_add_cancel hcycle_pos] at h
            exact h.mp h_wrap
          -- cycle = task_time_slot tsk
          have hcycle_eq_slot : cycle = task_time_slot tsk := by
            rw [hfs_max] at h_in_t
            exact le_antisymm (Nat.le_of_pred_lt h_in_t) hcycle_ge_slot
          -- in_slot(t+1)
          have HSLOT1 : Task_in_time_slot ts slot_order tsk task_time_slot (t + 1) := by
            show (t + 1 + cycle - offset % cycle) % cycle < task_time_slot tsk
            rw [hx1, h_wrap, ← hcycle_eq_slot]; exact hcycle_pos
          -- te(t) = 1
          have hte_t_eq1 : to_end_of_slot_fn ts slot_order tsk task_time_slot t = 1 := by
            rw [h_te_t, hfs_max, hcycle_eq_slot]
            exact Nat.sub_sub_self (Nat.succ_le_of_lt hslot_pos)
          -- c+1 > te(t)=1
          have hgt : ¬(c + 1 ≤ to_end_of_slot_fn ts slot_order tsk task_time_slot t) := by
            rw [hte_t_eq1]; omega
          -- ns(t) = 1
          have hns_t : to_next_slot_fn ts slot_order tsk task_time_slot t = 1 := by
            simp only [to_next_slot_fn, h_fs_t, hfs_max, ← hcycle_def]
            exact Nat.sub_sub_self (Nat.succ_le_of_lt hcycle_pos)
          -- formula_rt(t, c+1) = 1 + dur(c)
          rw [hrt_lhs_ite, if_neg hgt, hte_t_eq1, show c + 1 - 1 = c from by omega, hns_t]
          -- dur(c) = c since cycle = task_time_slot tsk means (cycle - task_time_slot tsk) = 0
          have hdur_id : ∀ n, duration_to_finish_from_start_of_slot_with_fn ts tsk task_time_slot n = n := by
            intro n
            simp only [duration_to_finish_from_start_of_slot_with_fn, ← hcycle_def,
                        hcycle_eq_slot, Nat.sub_self, Nat.mul_zero, Nat.zero_add]
          -- te(t+1) = task_time_slot tsk
          have hte_t1_eq : to_end_of_slot_fn ts slot_order tsk task_time_slot (t + 1) =
              task_time_slot tsk := by
            simp only [to_end_of_slot_fn, h_fs_t1, h_wrap, Nat.sub_zero]
          by_cases hle1 : c ≤ to_end_of_slot_fn ts slot_order tsk task_time_slot (t + 1)
          · -- c ≤ te(t+1)
            unfold formula_rt_fn; rw [if_neg hc, if_pos HSLOT1, if_pos hle1]
            rw [hdur_id]; ring
          · -- c > te(t+1)
            unfold formula_rt_fn; rw [if_neg hc, if_pos HSLOT1, if_neg hle1]
            rw [hdur_id, hdur_id]
            have hns_t1 : to_next_slot_fn ts slot_order tsk task_time_slot (t + 1) = cycle := by
              simp only [to_next_slot_fn, h_fs_t1, h_wrap, ← hcycle_def, Nat.sub_zero]
            rw [hns_t1, hte_t1_eq, hcycle_eq_slot]
            push_neg at hle1; rw [hte_t1_eq] at hle1
            have : task_time_slot tsk + (c - task_time_slot tsk) = c :=
              Nat.add_sub_cancel' (le_of_lt hle1)
            simp only [Time] at *; omega

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem formula_not_sched_interval :
        ∀ (t : Time) (c : ℕ),
          pending job_arrival job_cost sched j t →
          scheduled_at sched j t = false →
          ∀ (d : ℕ),
            d < to_next_slot_fn ts slot_order tsk task_time_slot t →
            t + formula_rt_fn ts slot_order tsk task_time_slot t (c + 1) =
              t + d + formula_rt_fn ts slot_order tsk task_time_slot (t + d) (c + 1) := by
      intro t c hpend hnsched
      intro d
      induction d with
      | zero => intro _; simp
      | succ d' ih =>
        intro hlt
        have hd'lt : d' < to_next_slot_fn ts slot_order tsk task_time_slot t := by omega
        have ⟨hnsched_d', hpend_d'⟩ := @duration_not_sched sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t hpend hnsched d' hd'lt
        have ih_eq := ih hd'lt
        rw [ih_eq]
        have hstep := @formula_not_sched_St sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed (t + d') c hpend_d' hnsched_d'
        simp only [Time] at *; omega

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem formula_not_sched_to_next_slot :
        ∀ (t : Time) (c : ℕ),
          pending job_arrival job_cost sched j t →
          scheduled_at sched j t = false →
          t + formula_rt_fn ts slot_order tsk task_time_slot t (c + 1) =
            t + to_next_slot_fn ts slot_order tsk task_time_slot t +
              formula_rt_fn ts slot_order tsk task_time_slot
                (t + to_next_slot_fn ts slot_order tsk task_time_slot t) (c + 1) := by
      intro t c PEN NSCHED
      set nxt := to_next_slot_fn ts slot_order tsk task_time_slot t
      have Hnxt_pos : nxt > 0 := @to_next_slot_pos sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task H_valid_job H_valid_time_slot all_previous_jobs_of_same_task_completed t
      have Hfact : nxt - 1 < nxt := Nat.sub_lt Hnxt_pos (by omega)
      have h1 := @formula_not_sched_interval sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t c PEN NSCHED (nxt - 1) Hfact
      have ⟨hns_pred, hpen_pred⟩ := @duration_not_sched sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN NSCHED (nxt - 1) Hfact
      have hstep := @formula_not_sched_St sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed (t + (nxt - 1)) c hpen_pred hns_pred
      rw [h1, hstep]
      have hkey : t + (nxt - 1) + 1 = t + nxt := by
        simp only [nxt, Time] at *; omega
      rw [hkey]

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem job_not_sched_to_cunsume_1unit :
        ∀ (t : Time) (c : ℕ),
          pending job_arrival job_cost sched j t →
          scheduled_at sched j t = false →
          t + formula_rt_fn ts slot_order tsk task_time_slot t (c + 1) =
            (t + to_next_slot_fn ts slot_order tsk task_time_slot t) + 1 +
              formula_rt_fn ts slot_order tsk task_time_slot
                ((t + to_next_slot_fn ts slot_order tsk task_time_slot t) + 1) c := by
      intro t c PEN NSCHED
      have hsched := @at_next_start_of_slot_schedulabe sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN NSCHED
      have h2 := @formula_sched_St sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed (t + to_next_slot_fn ts slot_order tsk task_time_slot t) c hsched
      have h1 := @formula_not_sched_to_next_slot sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t c PEN NSCHED
      rw [h1, h2]

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem end_time_predicate_not_sched_eq :
        ∀ (d c : ℕ) (t : Time) (e : Instant),
          pending job_arrival job_cost sched j t →
          scheduled_at sched j t = false →
          end_time_predicate_local sched j t (c + 1) e →
          d < to_next_slot_fn ts slot_order tsk task_time_slot t →
          end_time_predicate_local sched j (t + d) (c + 1) e := by
      intro d
      induction d with
      | zero => intro c t e _ _ h _; rwa [Nat.add_zero]
      | succ d' ih =>
        intro c t e PEN NSCHED hpred hlt
        have hd'lt : d' < to_next_slot_fn ts slot_order tsk task_time_slot t := Nat.lt_of_succ_lt hlt
        have hpred_d' := ih c t e PEN NSCHED hpred hd'lt
        rw [show t + (d' + 1) = (t + d') + 1 from by simp only [Time] at *; omega]
        have ⟨hns_d', _⟩ := @duration_not_sched sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN NSCHED d' hd'lt
        cases hpred_d' with
        | S_C_not_sched _ _ _ _ hnext => exact hnext
        | S_C_sched _ _ _ hsched _ => simp [hns_d'] at hsched

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem end_time_predicate_not_sched_eq_rev :
        ∀ (d c : ℕ) (t : Time) (e : Instant),
          pending job_arrival job_cost sched j t →
          scheduled_at sched j t = false →
          end_time_predicate_local sched j (t + d) (c + 1) e →
          d < to_next_slot_fn ts slot_order tsk task_time_slot t →
          end_time_predicate_local sched j t (c + 1) e := by
      intro d
      induction d with
      | zero => intro c t e _ _ h _; rwa [Nat.add_zero] at h
      | succ d' ih =>
        intro c t e PEN NSCHED h2 hlt
        have hd'lt : d' < to_next_slot_fn ts slot_order tsk task_time_slot t := Nat.lt_of_succ_lt hlt
        rw [show t + (d' + 1) = (t + d') + 1 from by simp only [Time] at *; omega] at h2
        have ⟨hns_d', _⟩ := @duration_not_sched sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN NSCHED d' hd'lt
        -- Apply S_C_not_sched constructor backwards: pred((t+d')+1, c+1, e) → pred(t+d', c+1, e)
        have h2' : end_time_predicate_local sched j (t + d') (c + 1) e :=
          .S_C_not_sched (t + d') c e (by simp [hns_d']) h2
        exact ih c t e PEN NSCHED h2' hd'lt

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem end_time_predicate_eq_iff :
        ∀ (t : Time) (c : ℕ) (e : Instant),
          pending job_arrival job_cost sched j t →
          scheduled_at sched j t = false →
          (end_time_predicate_local sched j t (c + 1) e ↔
           end_time_predicate_local sched j
             ((t + to_next_slot_fn ts slot_order tsk task_time_slot t) + 1)
             c e) := by
      intro t c e PEN NSCHED
      set nxt := to_next_slot_fn ts slot_order tsk task_time_slot t
      have Hnxt_pos : nxt > 0 := @to_next_slot_pos sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task H_valid_job H_valid_time_slot all_previous_jobs_of_same_task_completed t
      have Hfact : nxt - 1 < nxt := Nat.sub_lt Hnxt_pos (by omega)
      constructor
      · -- Forward: pred(t, c+1, e) → pred((t+nxt)+1, c, e)
        intro h2
        -- Step 1: pred(t, c+1, e) → pred(t+(nxt-1), c+1, e)
        have h_fwd := @end_time_predicate_not_sched_eq sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed (nxt - 1) c t e PEN NSCHED h2 Hfact
        -- Step 2: sched(t+(nxt-1)) = false
        have ⟨hns_pred, _⟩ := @duration_not_sched sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN NSCHED (nxt - 1) Hfact
        -- Step 3: extract forward from pred at t+(nxt-1) to pred at t+nxt
        have h_at_nxt : end_time_predicate_local sched j (t + nxt) (c + 1) e := by
          rw [show t + nxt = (t + (nxt - 1)) + 1 from by simp only [nxt, Time] at *; omega]
          cases h_fwd with
          | S_C_not_sched _ _ _ _ hnext => exact hnext
          | S_C_sched _ _ _ hsched _ => simp [hns_pred] at hsched
        -- Step 4: sched(t+nxt) = true, extract forward from pred(t+nxt, c+1, e) to pred(t+nxt+1, c, e)
        have hsched_nxt := @at_next_start_of_slot_schedulabe sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN NSCHED
        cases h_at_nxt with
        | S_C_sched _ _ _ _ hnext => exact hnext
        | S_C_not_sched _ _ _ hns _ => exact absurd hsched_nxt hns
      · -- Backward: pred((t+nxt)+1, c, e) → pred(t, c+1, e)
        intro h2
        -- Step 1: sched(t+nxt) = true → apply S_C_sched backward to get pred(t+nxt, c+1, e)
        have hsched_nxt := @at_next_start_of_slot_schedulabe sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN NSCHED
        have h_at_nxt : end_time_predicate_local sched j (t + nxt) (c + 1) e :=
          .S_C_sched (t + nxt) c e hsched_nxt h2
        -- Step 2: sched(t+(nxt-1)) = false → apply S_C_not_sched backward
        have ⟨hns_pred, _⟩ := @duration_not_sched sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN NSCHED (nxt - 1) Hfact
        have h_prev : end_time_predicate_local sched j (t + (nxt - 1)) (c + 1) e := by
          rw [show t + nxt = (t + (nxt - 1)) + 1 from by simp only [nxt, Time] at *; omega] at h_at_nxt
          exact .S_C_not_sched (t + (nxt - 1)) c e (by simp [hns_pred]) h_at_nxt
        -- Step 3: unwind back through the not-sched duration
        exact @end_time_predicate_not_sched_eq_rev sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed (nxt - 1) c t e PEN NSCHED h_prev Hfact

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem service_is_zero_in_Nsched_duration :
        ∀ (d : ℕ) (t : Time),
          pending job_arrival job_cost sched j t →
          scheduled_at sched j t = false →
          d ≤ to_next_slot_fn ts slot_order tsk task_time_slot t →
          service sched j (t + d) = service sched j t := by
      intro d
      induction d with
      | zero => intro t _ _ _; rw [Nat.add_zero]
      | succ d' ih =>
        intro t PEN NSCHED hle
        have hd'le : d' ≤ to_next_slot_fn ts slot_order tsk task_time_slot t := by omega
        have hd'lt : d' < to_next_slot_fn ts slot_order tsk task_time_slot t := by omega
        have ih_eq := ih t PEN NSCHED hd'le
        have ⟨hns_d', _⟩ := @duration_not_sched sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN NSCHED d' hd'lt
        rw [show t + (d' + 1) = t + d' + 1 from by simp only [Time] at *; omega]
        have hstep : service sched j (t + d' + 1) = service sched j (t + d') := by
          unfold service service_during
          rw [Finset.sum_Ico_succ_top (Nat.zero_le (t + d'))]
          unfold service_at
          simp [hns_d']
        rw [hstep, ih_eq]

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
    theorem completes_at_end_time_pre :
        ∀ (c : ℕ) (t : Time),
          pending job_arrival job_cost sched j t →
          service sched j t + c = job_cost j →
          end_time_predicate_local sched j t c
            (t + formula_rt_fn ts slot_order tsk task_time_slot t c) := by
      intro c
      induction c with
      | zero =>
        intro t PEN SC
        simp only [formula_rt_fn, ite_true, Nat.add_zero]
        exact .C0_ t
      | succ c' ih =>
        intro t PEN SC
        cases hsched : scheduled_at sched j t
        case true =>
          -- Scheduled at t
          cases c' with
          | zero =>
            -- c = 1
            have hstep := @formula_sched_St sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t 0 hsched
            refine .S_C_sched t 0 _ hsched ?_
            rw [hstep]
            have h0 : formula_rt_fn ts slot_order tsk task_time_slot (t + 1) 0 = 0 := by
              simp [formula_rt_fn]
            rw [h0, Nat.add_zero]
            exact .C0_ (t + 1)
          | succ c'' =>
            -- c = c'' + 2
            have hstep := @formula_sched_St sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t (c'' + 1) hsched
            have PEN' := pendingSt_Sched job_arrival job_cost sched j t c'' PEN SC hsched
            have SC' : service sched j (t + 1) + (c'' + 1) = job_cost j := by
              have hsvc : service sched j (t + 1) = service sched j t + 1 := by
                unfold service service_during
                rw [Finset.sum_Ico_succ_top (Nat.zero_le t)]
                unfold service_at; simp [hsched]
              rw [hsvc]; omega
            refine .S_C_sched t (c'' + 1) _ hsched ?_
            rw [hstep]
            exact ih (t + 1) PEN' SC'
        case false =>
          -- Not scheduled at t
          cases c' with
          | zero =>
            -- c = 1, not scheduled
            have hiff := @end_time_predicate_eq_iff sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t 0 (t + formula_rt_fn ts slot_order tsk task_time_slot t 1) PEN hsched
            apply hiff.mpr
            have hjnstc := @job_not_sched_to_cunsume_1unit sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t 0 PEN hsched
            rw [hjnstc]
            have h0 : formula_rt_fn ts slot_order tsk task_time_slot
                ((t + to_next_slot_fn ts slot_order tsk task_time_slot t) + 1) 0 = 0 := by
              simp [formula_rt_fn]
            rw [h0, Nat.add_zero]
            exact .C0_ _
          | succ c'' =>
            -- c = c'' + 2, not scheduled
            have hiff := @end_time_predicate_eq_iff sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t (c'' + 1) (t + formula_rt_fn ts slot_order tsk task_time_slot t (c'' + 2)) PEN hsched
            apply hiff.mpr
            have hjnstc := @job_not_sched_to_cunsume_1unit sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t (c'' + 1) PEN hsched
            rw [hjnstc]
            -- Derive pending and service at (t + nxt) + 1
            have PENX := @pending_Nsched_sched sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN hsched
            have SCHED_nxt := @at_next_start_of_slot_schedulabe sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed t PEN hsched
            have hserv_eq := @service_is_zero_in_Nsched_duration sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed (to_next_slot_fn ts slot_order tsk task_time_slot t) t PEN hsched (le_refl _)
            have SC_nxt : service sched j (t + to_next_slot_fn ts slot_order tsk task_time_slot t) + (c'' + 2) = job_cost j := by
              rw [hserv_eq]; exact SC
            have PEN' := pendingSt_Sched job_arrival job_cost sched j (t + to_next_slot_fn ts slot_order tsk task_time_slot t) c'' PENX SC_nxt SCHED_nxt
            have SC' : service sched j ((t + to_next_slot_fn ts slot_order tsk task_time_slot t) + 1) + (c'' + 1) = job_cost j := by
              have hsvc : service sched j ((t + to_next_slot_fn ts slot_order tsk task_time_slot t) + 1) =
                  service sched j (t + to_next_slot_fn ts slot_order tsk task_time_slot t) + 1 := by
                unfold service service_during
                rw [Finset.sum_Ico_succ_top (Nat.zero_le (t + to_next_slot_fn ts slot_order tsk task_time_slot t))]
                unfold service_at; simp [SCHED_nxt]
              rw [hsvc, hserv_eq]; omega
            exact ih ((t + to_next_slot_fn ts slot_order tsk task_time_slot t) + 1) PEN' SC'

  end formula_predicate_eq

  include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed in
  theorem completes_at_end_time :
      completes_at_local sched j job_arrival job_cost
        (job_arrival j +
          job_response_time_tdma_in_at_most_one_job_is_pending_fn
            ts slot_order tsk task_time_slot job_arrival job_cost j) := by
    unfold completes_at_local job_response_time_tdma_in_at_most_one_job_is_pending_fn
    refine @completes_at_end_time_pre sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed (job_cost j) (job_arrival j) ?_ ?_
    · exact @pendingArrival sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task H_valid_job H_valid_time_slot all_previous_jobs_of_same_task_completed
    · have h0 := cumulative_service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive_to_execute j 0 (job_arrival j) (le_refl _)
      unfold service service_during; rw [h0]; omega

  section ValidWCRT

    variable (H_job_cost_le_task_cost_hyp :
      job_cost j ≤ task_cost (job_task j))

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed H_job_cost_le_task_cost_hyp in
    theorem response_time_le_WCRT :
        job_response_time_tdma_in_at_most_one_job_is_pending_fn
          ts slot_order tsk task_time_slot job_arrival job_cost j ≤
          WCRT_fn ts task_cost tsk task_time_slot := by
      unfold job_response_time_tdma_in_at_most_one_job_is_pending_fn WCRT_fn WCRT_formula_fn
      have cost_pos : job_cost j > 0 := H_valid_job.1.1
      have cost_le : job_cost j ≤ task_cost tsk := by
        rw [← H_job_task]; exact H_job_cost_le_task_cost_hyp
      have slot_pos : task_time_slot tsk > 0 := H_valid_time_slot
      have cycle_pos : TDMA_cycle ts task_time_slot > 0 :=
        TDMA_cycle_positive ts tsk H_task_in_task_set task_time_slot H_valid_time_slot
      have cycle_ge_slot : TDMA_cycle ts task_time_slot ≥ task_time_slot tsk :=
        TDMA_cycle_ge_each_time_slot ts tsk H_task_in_task_set task_time_slot
      -- Helper: a + k*D ≤ WCRT when a ≤ WCET and k ≤ div_ceil(WCET,s)
      have wcrt_bound : ∀ a k, a ≤ task_cost tsk →
          k ≤ div_ceil (task_cost tsk) (task_time_slot tsk) →
          a + k * (TDMA_cycle ts task_time_slot - task_time_slot tsk) ≤
          div_ceil (task_cost tsk) (task_time_slot tsk) *
            (TDMA_cycle ts task_time_slot - task_time_slot tsk) + task_cost tsk := by
        intro a k ha hk
        calc a + k * (TDMA_cycle ts task_time_slot - task_time_slot tsk)
            ≤ task_cost tsk + div_ceil (task_cost tsk) (task_time_slot tsk) *
                (TDMA_cycle ts task_time_slot - task_time_slot tsk) :=
              Nat.add_le_add ha (Nat.mul_le_mul_right _ hk)
          _ = div_ceil (task_cost tsk) (task_time_slot tsk) *
                (TDMA_cycle ts task_time_slot - task_time_slot tsk) + task_cost tsk :=
              Nat.add_comm _ _
      -- Helper: D + (k-1)*D = k*D when k ≥ 1
      have factor_lemma : ∀ k D', k ≥ 1 → D' + (k - 1) * D' = k * D' := by
        intro k D' hk
        cases k with
        | zero => omega
        | succ n => simp [Nat.succ_sub_one, Nat.succ_mul]; ring
      show formula_rt_fn ts slot_order tsk task_time_slot (job_arrival j) (job_cost j) ≤
        div_ceil (task_cost tsk) (task_time_slot tsk) *
          (TDMA_cycle ts task_time_slot - task_time_slot tsk) + task_cost tsk
      unfold formula_rt_fn
      split_ifs with hc_eq h_slot h_cost
      · -- c = 0: contradiction with cost_pos
        exact Nat.zero_le _
      · -- in_slot, c ≤ to_end: formula_rt = c
        calc job_cost j ≤ task_cost tsk := cost_le
          _ ≤ _ := Nat.le_add_left _ _
      · -- in_slot, c > to_end
        simp only [duration_to_finish_from_start_of_slot_with_fn, to_next_slot_fn, to_end_of_slot_fn]
        set f := from_start_of_slot_fn ts slot_order tsk task_time_slot (job_arrival j)
        set D := TDMA_cycle ts task_time_slot - task_time_slot tsk
        set c' := job_cost j - (task_time_slot tsk - f)
        have hf_lt_s : f < task_time_slot tsk := h_slot
        have hc_gt : job_cost j > task_time_slot tsk - f := by
          unfold to_end_of_slot_fn at h_cost; exact not_le.mp h_cost
        have hc'_pos : c' > 0 := Nat.sub_pos_of_lt hc_gt
        have hc'_le : c' ≤ task_cost tsk := le_trans (Nat.sub_le _ _) cost_le
        set k := div_ceil c' (task_time_slot tsk)
        have hk_pos : k ≥ 1 := ceil_neq0 c' (task_time_slot tsk) hc'_pos slot_pos
        have hk_le : k ≤ div_ceil (task_cost tsk) (task_time_slot tsk) :=
          leq_divceil2r _ _ _ slot_pos hc'_le
        suffices h : job_cost j + k * D ≤
            div_ceil (task_cost tsk) (task_time_slot tsk) * D + task_cost tsk by
          have h_sum : (TDMA_cycle ts task_time_slot - f) + c' = job_cost j + D := by
            have h1 : c' + (task_time_slot tsk - f) = job_cost j :=
              Nat.sub_add_cancel (le_of_lt hc_gt)
            have h2 : TDMA_cycle ts task_time_slot - f =
                D + (task_time_slot tsk - f) := by
              have hfles := le_of_lt hf_lt_s
              have h_lhs := Nat.sub_add_cancel (le_trans hfles cycle_ge_slot)
              have h_rhs : D + (task_time_slot tsk - f) + f =
                  TDMA_cycle ts task_time_slot := by
                rw [Nat.add_assoc, Nat.sub_add_cancel hfles]
                exact Nat.sub_add_cancel cycle_ge_slot
              exact Nat.add_right_cancel (h_lhs.trans h_rhs.symm)
            rw [h2, Nat.add_assoc, Nat.add_comm (task_time_slot tsk - f) c', h1, Nat.add_comm]
          have h_factor := factor_lemma k D hk_pos
          calc (TDMA_cycle ts task_time_slot - f) + ((k - 1) * D + c')
              = ((TDMA_cycle ts task_time_slot - f) + c') + (k - 1) * D := by
                rw [Nat.add_comm ((k - 1) * D) c', Nat.add_assoc]
            _ = (job_cost j + D) + (k - 1) * D := by rw [h_sum]
            _ = job_cost j + (D + (k - 1) * D) := (Nat.add_assoc _ _ _)
            _ = job_cost j + k * D := by rw [h_factor]
            _ ≤ div_ceil (task_cost tsk) (task_time_slot tsk) * D + task_cost tsk := h
        exact wcrt_bound (job_cost j) k cost_le hk_le
      · -- not in slot
        simp only [duration_to_finish_from_start_of_slot_with_fn, to_next_slot_fn]
        set f := from_start_of_slot_fn ts slot_order tsk task_time_slot (job_arrival j)
        set D := TDMA_cycle ts task_time_slot - task_time_slot tsk
        have hf_ge_s : f ≥ task_time_slot tsk := not_lt.mp h_slot
        have hf_lt_cycle : f < TDMA_cycle ts task_time_slot := by
          simp only [f, from_start_of_slot_fn]; exact Nat.mod_lt _ cycle_pos
        have h_to_next_le : TDMA_cycle ts task_time_slot - f ≤ D := by
          simp only [D]; omega
        set k := div_ceil (job_cost j) (task_time_slot tsk)
        have hk_pos : k ≥ 1 := ceil_neq0 _ _ cost_pos slot_pos
        have hk_le : k ≤ div_ceil (task_cost tsk) (task_time_slot tsk) :=
          leq_divceil2r _ _ _ slot_pos cost_le
        suffices h : job_cost j + k * D ≤
            div_ceil (task_cost tsk) (task_time_slot tsk) * D + task_cost tsk by
          have h_factor := factor_lemma k D hk_pos
          calc (TDMA_cycle ts task_time_slot - f) + ((k - 1) * D + job_cost j)
              ≤ D + ((k - 1) * D + job_cost j) :=
                Nat.add_le_add_right h_to_next_le _
            _ = (D + (k - 1) * D) + job_cost j := by rw [← Nat.add_assoc]
            _ = k * D + job_cost j := by rw [h_factor]
            _ = job_cost j + k * D := Nat.add_comm _ _
            _ ≤ div_ceil (task_cost tsk) (task_time_slot tsk) * D + task_cost tsk := h
        exact wcrt_bound (job_cost j) k cost_le hk_le

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed H_job_cost_le_task_cost_hyp in
    theorem exists_WCRT :
        job_cost j = task_cost tsk ∧
          from_start_of_slot_fn ts slot_order tsk task_time_slot (job_arrival j) =
            task_time_slot tsk →
        job_response_time_tdma_in_at_most_one_job_is_pending_fn
          ts slot_order tsk task_time_slot job_arrival job_cost j =
          WCRT_fn ts task_cost tsk task_time_slot := by
      intro ⟨hcost, hfs⟩
      unfold job_response_time_tdma_in_at_most_one_job_is_pending_fn WCRT_fn WCRT_formula_fn
      have cost_pos : job_cost j > 0 := H_valid_job.1.1
      have slot_pos : task_time_slot tsk > 0 := H_valid_time_slot
      show formula_rt_fn ts slot_order tsk task_time_slot (job_arrival j) (job_cost j) =
        div_ceil (task_cost tsk) (task_time_slot tsk) *
          (TDMA_cycle ts task_time_slot - task_time_slot tsk) + task_cost tsk
      unfold formula_rt_fn
      have h_not_in_slot : ¬ Task_in_time_slot ts slot_order tsk task_time_slot (job_arrival j) :=
        not_lt.mpr (le_of_eq hfs.symm)
      rw [if_neg (ne_of_gt cost_pos), if_neg h_not_in_slot]
      simp only [duration_to_finish_from_start_of_slot_with_fn, to_next_slot_fn]
      rw [hcost, hfs]
      set D := TDMA_cycle ts task_time_slot - task_time_slot tsk
      set k := div_ceil (task_cost tsk) (task_time_slot tsk)
      have hk_pos : k ≥ 1 := ceil_neq0 _ _ (by rw [← hcost]; exact cost_pos) slot_pos
      have h_factor : D + (k - 1) * D = k * D := by
        have : k = (k - 1) + 1 := (Nat.sub_add_cancel hk_pos).symm
        conv_rhs => rw [this]
        ring
      calc D + ((k - 1) * D + task_cost tsk)
          = (D + (k - 1) * D) + task_cost tsk := by rw [← Nat.add_assoc]
        _ = k * D + task_cost tsk := by rw [h_factor]

    include H_sporadic_tasks H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_task_parameters H_task_in_task_set H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed H_job_cost_le_task_cost_hyp in
    theorem job_completed_by_WCRT :
        completed_by job_cost sched j
          (job_arrival j + WCRT_fn ts task_cost tsk task_time_slot) := by
      have h_le := @response_time_le_WCRT sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed H_job_cost_le_task_cost_hyp
      have h_compl := @completes_at_end_time sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute task_time_slot slot_order ts H_valid_task_parameters tsk H_task_in_task_set j H_job_task job_in_arr_seq H_valid_job H_valid_time_slot TDMA_policy_hyp all_previous_jobs_of_same_task_completed
      have h_done := completed_by_end_time_aux sched j job_arrival job_cost H_jobs_must_arrive_to_execute _ h_compl
      exact completion_monotonic job_cost sched j _ _ (Nat.add_le_add_left h_le _) h_done

  end ValidWCRT

end WCRT_analysis

end WCRT_OneJobTDMA

end Prosa.Classic.Analysis.Uni.Basic.Tdma_wcrt_analysis
