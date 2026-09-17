-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/platform/limited.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
import Prosa.Util.Nondecreasing
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Util.Nondecreasing
open Prosa.Util.List
open Prosa.Util.Epsilon

namespace ModelWithLimitedPreemptions

section ModelsWithLimitedPreemptions

  variable {Task : Type _} [DecidableEq Task]
  variable (task_cost : Task → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → Task)

  variable (arr_seq : arrival_sequence Job)

  variable (job_preemption_points : Job → List Time)

  section Definitions

    section ModelWithLimitedPreemptions

      def lengths_of_segments (j : Job) : List ℕ :=
        distances (job_preemption_points j)

      def job_max_nps (j : Job) : ℕ :=
        max0 (lengths_of_segments job_preemption_points j)

      def job_last_nps (j : Job) : ℕ :=
        last0 (lengths_of_segments job_preemption_points j)

      def job_with_zero_cost_consists_of_one_empty_segment : Prop :=
        ∀ j, arrives_in arr_seq j → job_cost j = 0 → job_preemption_points j = [0, 0]

      def last_segment_is_positive : Prop :=
        ∀ j, arrives_in arr_seq j → job_cost j > 0 → job_last_nps job_preemption_points j > 0

      def beginning_of_execution_in_preemption_points : Prop :=
        ∀ j, arrives_in arr_seq j → first0 (job_preemption_points j) = 0

      def end_of_execution_in_preemption_points : Prop :=
        ∀ j, arrives_in arr_seq j → last0 (job_preemption_points j) = job_cost j

      def preemption_points_is_nondecreasing_sequence : Prop :=
        ∀ (j : Job),
          arrives_in arr_seq j →
          nondecreasing_sequence (job_preemption_points j)

      def limited_preemptions_job_model : Prop :=
        job_with_zero_cost_consists_of_one_empty_segment job_cost arr_seq job_preemption_points ∧
        last_segment_is_positive job_cost arr_seq job_preemption_points ∧
        beginning_of_execution_in_preemption_points arr_seq job_preemption_points ∧
        end_of_execution_in_preemption_points job_cost arr_seq job_preemption_points ∧
        preemption_points_is_nondecreasing_sequence arr_seq job_preemption_points

    end ModelWithLimitedPreemptions

    section ModelWithFixedPreemptionPoints

      variable (task_preemption_points : Task → List Time)

      def task_last_nps (tsk : Task) : ℕ :=
        last0 (distances (task_preemption_points tsk))

      def task_max_nps (tsk : Task) : ℕ :=
        max0 (distances (task_preemption_points tsk))

      variable (ts : List Task)

      def task_beginning_of_execution_in_preemption_points : Prop :=
        ∀ tsk, tsk ∈ ts → first0 (task_preemption_points tsk) = 0

      def task_end_of_execution_in_preemption_points : Prop :=
        ∀ tsk, tsk ∈ ts → last0 (task_preemption_points tsk) = task_cost tsk

      def task_preemption_points_is_nondecreasing_sequence : Prop :=
        ∀ tsk, tsk ∈ ts → nondecreasing_sequence (task_preemption_points tsk)

      def job_consists_of_the_same_number_of_segments_as_task : Prop :=
        ∀ j,
          arrives_in arr_seq j →
          (job_preemption_points j).length = (task_preemption_points (job_task j)).length

      def lengths_of_task_segments_bound_length_of_job_segments : Prop :=
        ∀ j n,
          arrives_in arr_seq j →
          nthD (distances (job_preemption_points j)) n
            ≤ nthD (distances (task_preemption_points (job_task j))) n

      def task_segments_are_nonempty : Prop :=
        ∀ tsk n,
          tsk ∈ ts →
          n < (distances (task_preemption_points tsk)).length →
          ε ≤ nthD (distances (task_preemption_points tsk)) n

      def fixed_preemption_points_task_model : Prop :=
        task_beginning_of_execution_in_preemption_points task_preemption_points ts ∧
        task_end_of_execution_in_preemption_points task_cost task_preemption_points ts ∧
        task_preemption_points_is_nondecreasing_sequence task_preemption_points ts ∧
        job_consists_of_the_same_number_of_segments_as_task job_task arr_seq job_preemption_points task_preemption_points ∧
        lengths_of_task_segments_bound_length_of_job_segments job_task arr_seq job_preemption_points task_preemption_points ∧
        task_segments_are_nonempty task_preemption_points ts

      def fixed_preemption_points_model : Prop :=
        limited_preemptions_job_model job_cost arr_seq job_preemption_points ∧
        fixed_preemption_points_task_model task_cost job_task arr_seq job_preemption_points task_preemption_points ts

    end ModelWithFixedPreemptionPoints

    section ModelWithFloatingNonpreemptiveRegions

      variable (task_max_nps_v : Task → Time)

      def job_max_np_segment_le_task_max_np_segment : Prop :=
        ∀ (j : Job),
          arrives_in arr_seq j →
          job_max_nps job_preemption_points j ≤ task_max_nps_v (job_task j)

      def model_with_floating_nonpreemptive_regions : Prop :=
        limited_preemptions_job_model job_cost arr_seq job_preemption_points ∧
        job_max_np_segment_le_task_max_np_segment job_task arr_seq job_preemption_points task_max_nps_v

    end ModelWithFloatingNonpreemptiveRegions

    def can_be_preempted_for_model_with_limited_preemptions (j : Job) (progr : Time) : Bool :=
      decide (progr ∈ job_preemption_points j)

    def is_schedule_with_limited_preemptions (sched : schedule Job) : Prop :=
      ∀ j t,
        arrives_in arr_seq j →
        can_be_preempted_for_model_with_limited_preemptions job_preemption_points j (service sched j t) = false →
        scheduled_at sched j t = true

  end Definitions

  section Lemmas

    variable (sched : schedule Job)
    variable (H_is_schedule_with_limited_preemptions :
      is_schedule_with_limited_preemptions arr_seq job_preemption_points sched)

    variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

    variable (task_max_nps_v : Task → Time)
    variable (H_limited_preemptions_job_model :
      limited_preemptions_job_model job_cost arr_seq job_preemption_points)
    variable (H_job_max_np_segment_le_task_max_np_segment :
      job_max_np_segment_le_task_max_np_segment job_task arr_seq job_preemption_points task_max_nps_v)

    section AuxiliaryLemmas

      variable (j : Job)
      variable (H_j_arrives : arrives_in arr_seq j)
      include H_limited_preemptions_job_model H_j_arrives

      theorem list_of_preemption_point_is_not_empty :
          0 < (job_preemption_points j).length := by
        have EMPT := H_limited_preemptions_job_model.1
        have END := H_limited_preemptions_job_model.2.2.2.1
        by_cases h : job_cost j = 0
        · rw [EMPT j H_j_arrives h]; simp
        · by_contra h_len; push_neg at h_len; apply h
          rw [← END j H_j_arrives]
          have h_empty : job_preemption_points j = [] := by
            cases h_eq : job_preemption_points j with
            | nil => rfl
            | cons _ _ => simp [h_eq] at h_len
          simp [last0, h_empty]

      theorem zero_in_preemption_points :
          (0 : ℕ) ∈ job_preemption_points j := by
        have BEG := H_limited_preemptions_job_model.2.2.1
        rw [← BEG j H_j_arrives]; unfold first0
        have h_pos : 0 < (job_preemption_points j).length :=
          list_of_preemption_point_is_not_empty job_cost arr_seq
            job_preemption_points H_limited_preemptions_job_model j H_j_arrives
        cases h : job_preemption_points j with
        | nil => simp [h] at h_pos
        | cons a _ => simp

      theorem job_cost_in_nonpreemptive_points :
          job_cost j ∈ job_preemption_points j := by
        have END := H_limited_preemptions_job_model.2.2.2.1
        rw [← END j H_j_arrives]; unfold last0
        have h_pos : 0 < (job_preemption_points j).length :=
          list_of_preemption_point_is_not_empty job_cost arr_seq
            job_preemption_points H_limited_preemptions_job_model j H_j_arrives
        have h_ne : job_preemption_points j ≠ [] := List.ne_nil_of_length_pos h_pos
        cases h_eq : job_preemption_points j with
        | nil => exact absurd h_eq h_ne
        | cons a as => simp [List.getLastD]

      theorem number_of_preemption_points_at_least_two :
          2 ≤ (job_preemption_points j).length := by
        have EMPT := H_limited_preemptions_job_model.1
        by_cases h : job_cost j = 0
        · rw [EMPT j H_j_arrives h]; simp
        · calc 2 = [0, job_cost j].length := by simp
            _ ≤ (job_preemption_points j).length :=
              subseq_leq_size [0, job_cost j] (job_preemption_points j)
                (by simp [List.nodup_cons]; exact Ne.symm h) (by
                intro x hx; simp at hx
                rcases hx with rfl | rfl
                · exact zero_in_preemption_points job_cost arr_seq
                    job_preemption_points H_limited_preemptions_job_model j H_j_arrives
                · exact job_cost_in_nonpreemptive_points job_cost arr_seq
                    job_preemption_points H_limited_preemptions_job_model j H_j_arrives)

    end AuxiliaryLemmas

    include H_is_schedule_with_limited_preemptions in
    theorem model_with_fixed_preemption_points_is_correct :
        correct_preemption_model arr_seq sched
          (can_be_preempted_for_model_with_limited_preemptions job_preemption_points) := by
      unfold correct_preemption_model
      intro j h_arr
      refine ⟨?_, ?_⟩
      · -- not_preemptive_implies_scheduled
        unfold not_preemptive_implies_scheduled
        exact fun t h_npp => H_is_schedule_with_limited_preemptions j t h_arr h_npp
      · -- execution_starts_with_preemption_point
        unfold execution_starts_with_preemption_point
        intro prt h_not_sched h_sched
        by_contra h_contr
        apply h_not_sched
        -- service(prt+1) = service(prt) + service_at(prt) = service(prt) + 0
        have h_sa_false : scheduled_at sched j prt = false := by
          cases h_sa : scheduled_at sched j prt
          · rfl
          · exact absurd h_sa h_not_sched
        have h_serv : service sched j (prt + 1) = service sched j prt := by
          simp only [service, service_during, ← Finset.range_eq_Ico, Finset.sum_range_succ]
          simp [service_at, h_sa_false]
        have h_false : can_be_preempted_for_model_with_limited_preemptions
            job_preemption_points j (service sched j (prt + 1)) = false := by
          cases h_cp : can_be_preempted_for_model_with_limited_preemptions
              job_preemption_points j (service sched j (prt + 1))
          · rfl
          · exact absurd h_cp h_contr
        exact H_is_schedule_with_limited_preemptions j prt h_arr (h_serv ▸ h_false)

    include H_limited_preemptions_job_model H_job_max_np_segment_le_task_max_np_segment in
    theorem model_with_fixed_preemption_points_is_model_with_bounded_nonpreemptive_regions :
        model_with_bounded_nonpreemptive_segments job_cost job_task arr_seq
          (can_be_preempted_for_model_with_limited_preemptions job_preemption_points)
          (job_max_nps job_preemption_points) task_max_nps_v := by
      intro j ARR
      have EMPT := H_limited_preemptions_job_model.1
      have BEG := H_limited_preemptions_job_model.2.2.1
      have END := H_limited_preemptions_job_model.2.2.2.1
      have NDEC := H_limited_preemptions_job_model.2.2.2.2
      by_cases hzero : job_cost j = 0
      · -- Zero cost case
        have hjpp := EMPT j ARR hzero
        refine ⟨?_, ?_, ?_, ?_⟩
        · show can_be_preempted_for_model_with_limited_preemptions job_preemption_points j 0 = true
          unfold can_be_preempted_for_model_with_limited_preemptions; rw [hjpp]; decide
        · show can_be_preempted_for_model_with_limited_preemptions job_preemption_points j (job_cost j) = true
          unfold can_be_preempted_for_model_with_limited_preemptions; rw [hjpp, hzero]; decide
        · intro _; exact H_job_max_np_segment_le_task_max_np_segment j ARR
        · intro progr ⟨_, hle⟩
          rw [hzero] at hle
          have hzp : progr = 0 := Nat.le_zero.mp hle
          subst hzp
          refine ⟨0, le_refl _, Nat.zero_le _, ?_⟩
          show can_be_preempted_for_model_with_limited_preemptions job_preemption_points j 0 = true
          unfold can_be_preempted_for_model_with_limited_preemptions; rw [hjpp]; decide
      · -- Positive cost case
        have hpos : 0 < job_cost j := Nat.pos_of_ne_zero hzero
        refine ⟨?_, ?_, ?_, ?_⟩
        · show can_be_preempted_for_model_with_limited_preemptions job_preemption_points j 0 = true
          unfold can_be_preempted_for_model_with_limited_preemptions
          exact decide_eq_true_eq.mpr (zero_in_preemption_points job_cost arr_seq
            job_preemption_points H_limited_preemptions_job_model j ARR)
        · show can_be_preempted_for_model_with_limited_preemptions job_preemption_points j (job_cost j) = true
          unfold can_be_preempted_for_model_with_limited_preemptions
          exact decide_eq_true_eq.mpr (job_cost_in_nonpreemptive_points job_cost arr_seq
            job_preemption_points H_limited_preemptions_job_model j ARR)
        · intro _; exact H_job_max_np_segment_le_task_max_np_segment j ARR
        · -- nonpreemptive_regions_have_bounded_length
          intro progr ⟨_, hle⟩
          set pp := job_preemption_points j with hpp_def
          by_cases hmem : progr ∈ pp
          · -- progr is already a preemption point
            refine ⟨progr, le_refl _, Nat.le_add_right _ _, ?_⟩
            show can_be_preempted_for_model_with_limited_preemptions job_preemption_points j progr = true
            unfold can_be_preempted_for_model_with_limited_preemptions
            exact decide_eq_true_eq.mpr (hpp_def ▸ hmem)
          · -- progr is NOT a preemption point; find the segment it falls in
            have h_nd := NDEC j ARR
            have h_len2 := number_of_preemption_points_at_least_two job_cost arr_seq
              job_preemption_points H_limited_preemptions_job_model j ARR
            have h_beg := BEG j ARR
            have h_end := END j ARR
            have h_first_le : first0 pp ≤ progr := by rw [h_beg]; exact Nat.zero_le _
            have h_lt_last : progr < last0 pp := by
              rw [h_end]; rcases Nat.lt_or_eq_of_le hle with h | h
              · exact h
              · exfalso; apply hmem; rw [h, hpp_def]
                exact job_cost_in_nonpreemptive_points job_cost arr_seq
                  job_preemption_points H_limited_preemptions_job_model j ARR
            obtain ⟨n, hn_lt, hn_le, hn_lt2⟩ :=
              belonging_to_segment_of_seq_is_total pp progr h_len2 ⟨h_first_le, h_lt_last⟩
            -- ptr = nthD pp (n+1) is the next preemption point after progr
            set ptr := nthD pp (n + 1) with hptr_def
            -- ptr is a member of pp
            have h_ptr_mem : ptr ∈ pp := by
              have hlt : n + 1 < pp.length := hn_lt
              show nthD pp (n + 1) ∈ pp
              simp only [nthD, List.getD, List.getElem?_eq_getElem hlt, Option.getD]
              exact List.getElem_mem ..
            -- nthD pp n is a member of pp
            have h_n_mem : nthD pp n ∈ pp := by
              have hlt : n < pp.length := by omega
              simp only [nthD, List.getD, List.getElem?_eq_getElem hlt, Option.getD]
              exact List.getElem_mem ..
            -- nthD pp n ≠ progr (since progr ∉ pp but nthD pp n ∈ pp)
            have h_n_strict : nthD pp n + 1 ≤ progr := by
              have : nthD pp n ≠ progr := fun heq => hmem (heq ▸ h_n_mem)
              omega
            refine ⟨ptr, Nat.le_of_lt hn_lt2, ?_, ?_⟩
            · -- ptr ≤ progr + (job_max_nps j - ε)
              have h_dist := distance_between_neighboring_elements_le_max_distance_in_seq pp n
              -- h_dist : ptr - nthD pp n ≤ max0 (distances pp)
              -- h_n_strict : nthD pp n + 1 ≤ progr
              -- So ptr ≤ nthD pp n + max0(distances pp) ≤ (progr - 1) + max0(distances pp)
              --        = progr + max0(distances pp) - 1  (when max0 ≥ 1)
              have h_max_pos : 0 < max0 (distances pp) :=
                max_distance_in_nontrivial_seq_is_positive pp h_nd
                  ⟨0, job_cost j,
                    hpp_def ▸ zero_in_preemption_points job_cost arr_seq
                      job_preemption_points H_limited_preemptions_job_model j ARR,
                    hpp_def ▸ job_cost_in_nonpreemptive_points job_cost arr_seq
                      job_preemption_points H_limited_preemptions_job_model j ARR,
                    (ne_of_gt hpos).symm⟩
              show ptr ≤ progr + (job_max_nps job_preemption_points j - ε)
              unfold job_max_nps lengths_of_segments ε; rw [← hpp_def]
              omega
            · -- can_be_preempted j ptr = true
              show can_be_preempted_for_model_with_limited_preemptions job_preemption_points j ptr = true
              unfold can_be_preempted_for_model_with_limited_preemptions
              exact decide_eq_true_eq.mpr (hpp_def ▸ h_ptr_mem)

  end Lemmas

end ModelsWithLimitedPreemptions

end ModelWithLimitedPreemptions

end Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Limited
