-- Translated from: ../rt-proofs/classic/analysis/apa/bertogna_fp_comp.v
import Prosa.Classic.Util.All
import Prosa.Classic.Analysis.Apa.Bertogna_fp_theory
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Apa.Bertogna_fp_comp

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Workload
open Prosa.Classic.Model.Schedule.Apa.Platform
open Prosa.Classic.Model.Schedule.Apa.Interference
open Prosa.Classic.Model.Schedule.Apa.Affinity
open Prosa.Classic.Model.Schedule.Apa.Constrained_deadlines hiding apa_work_conserving respects_FP_policy_under_weak_APA
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Apa.Workload_bound.WorkloadBound
open Prosa.Classic.Analysis.Apa.Interference_bound.InterferenceBoundGeneric
open Prosa.Classic.Analysis.Apa.Interference_bound_fp.InterferenceBoundFP
open Prosa.Classic.Analysis.Apa.Bertogna_fp_theory.ResponseTimeAnalysisFP
open Prosa.Classic.Util.Fixedpoint
open Prosa.Classic.Util.Sorting
open Prosa.Util.Div_mod

attribute [local instance] Classical.propDecidable

namespace ResponseTimeIterationFP

section Analysis

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)

variable {num_cpus : ℕ}

variable (higher_priority : FP_policy sporadic_task)

variable (alpha : task_affinity sporadic_task num_cpus)
variable (alpha' : task_affinity sporadic_task num_cpus)

noncomputable def per_task_rta (tsk : sporadic_task)
    (R_prev : List (sporadic_task × Time)) (step : ℕ) : ℕ :=
  (fun t => task_cost tsk +
    div_floor
      (total_interference_bound_fp task_cost task_period alpha tsk
        (alpha' tsk) R_prev t higher_priority)
      (alpha' tsk).card)^[step] (task_cost tsk)

def max_steps (tsk : sporadic_task) : ℕ :=
  task_deadline tsk - task_cost tsk + 1

noncomputable def fp_bound_of_task
    (hp_pairs : Option (List (sporadic_task × Time)))
    (tsk : sporadic_task) : Option (List (sporadic_task × Time)) :=
  match hp_pairs with
  | some rt_bounds =>
    let R := per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds
               (max_steps task_deadline task_cost tsk)
    if R ≤ task_deadline tsk then
      some (rt_bounds ++ [(tsk, R)])
    else none
  | none => none

noncomputable def fp_claimed_bounds
    (ts : List sporadic_task) : Option (List (sporadic_task × Time)) :=
  ts.foldl (fp_bound_of_task task_cost task_period task_deadline higher_priority alpha alpha') (some [])

noncomputable def fp_schedulable (ts : List sporadic_task) : Prop :=
  fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha' ts ≠ none

section SimpleLemmas

theorem fp_claimed_bounds_unzip :
    ∀ (ts : List sporadic_task) (hp_bounds : List (sporadic_task × Time)),
      fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha' ts = some hp_bounds →
      hp_bounds.map Prod.fst = ts := by
  intro ts hp_bounds h
  -- We prove a more general statement about foldl with any accumulator
  suffices gen : ∀ (acc : List (sporadic_task × Time)) (ts_arg : List sporadic_task) (result : List (sporadic_task × Time)),
    List.foldl (fp_bound_of_task task_cost task_period task_deadline higher_priority alpha alpha') (some acc) ts_arg = some result →
    result.map Prod.fst = acc.map Prod.fst ++ ts_arg by
    unfold fp_claimed_bounds at h
    exact gen [] ts hp_bounds h
  intro acc ts_arg
  induction ts_arg generalizing acc with
  | nil =>
    intro result h
    simp [List.foldl] at h
    subst h; simp
  | cons t ts_rest ih =>
    intro result h
    rw [List.foldl_cons] at h
    simp only [fp_bound_of_task] at h
    split_ifs at h with hle
    · specialize ih (acc ++ [(t, per_task_rta task_cost task_period higher_priority alpha alpha' t acc (max_steps task_deadline task_cost t))]) result h
      rw [List.map_append] at ih
      simp at ih
      rw [ih]
    · -- h : foldl fp_bound_of_task none ts_rest = some result
      -- foldl starting from none always gives none
      have : ∀ (xs : List sporadic_task), List.foldl (fp_bound_of_task task_cost task_period task_deadline higher_priority alpha alpha') none xs = none := by
        intro xs; induction xs with
        | nil => simp [List.foldl]
        | cons x xs ih => simp [List.foldl, fp_bound_of_task, ih]
      rw [this] at h; contradiction

theorem fp_claimed_bounds_rcons :
    ∀ (ts' : List sporadic_task) (hp_bounds : List (sporadic_task × Time))
      (tsk1 tsk2 : sporadic_task) (R : Time),
      fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha'
        (ts' ++ [tsk1]) = some (hp_bounds ++ [(tsk2, R)]) →
      fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha'
        ts' = some hp_bounds ∧
      tsk1 = tsk2 ∧
      R = per_task_rta task_cost task_period higher_priority alpha alpha' tsk1 hp_bounds
            (max_steps task_deadline task_cost tsk1) ∧
      R ≤ task_deadline tsk1 := by
  intro ts' hp_bounds tsk1 tsk2 R h
  have key : fp_bound_of_task task_cost task_period task_deadline higher_priority alpha alpha'
    (fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha' ts') tsk1 =
    some (hp_bounds ++ [(tsk2, R)]) := by
    unfold fp_claimed_bounds at h ⊢
    rw [List.foldl_append, List.foldl] at h
    exact h
  unfold fp_bound_of_task at key
  cases hprev : fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha' ts' with
  | none => simp [hprev] at key
  | some rt_bounds =>
    rw [hprev] at key
    simp only at key
    split_ifs at key with hle
    · have hinj := Option.some.inj key
      -- hinj : rt_bounds ++ [x] = hp_bounds ++ [y]
      -- From append_inj with length info
      have hlen : rt_bounds.length = hp_bounds.length := by
        have := congr_arg List.length hinj; simp at this; omega
      have hinj2 := List.append_inj hinj hlen
      have hbounds := hinj2.1
      have hpair_list := hinj2.2
      rw [List.cons_eq_cons] at hpair_list
      obtain ⟨hpair_eq, _⟩ := hpair_list
      subst hbounds
      obtain ⟨htsk, hR⟩ := Prod.mk.inj hpair_eq
      subst htsk; subst hR
      exact ⟨rfl, rfl, rfl, hle⟩

theorem fp_claimed_bounds_take :
    ∀ (ts : List sporadic_task) (hp_bounds : List (sporadic_task × Time)) (i : ℕ),
      fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha' ts = some hp_bounds →
      i ≤ hp_bounds.length →
      fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha'
        (ts.take i) = some (hp_bounds.take i) := by
  intro ts hp_bounds i hsome hle
  have hunzip := fp_claimed_bounds_unzip task_cost task_period task_deadline higher_priority alpha alpha' ts hp_bounds hsome
  subst hunzip
  -- Now the goal uses hp_bounds.map Prod.fst in place of ts
  -- Generalize to a helper lemma
  suffices aux : ∀ (bounds : List (sporadic_task × Time)) (j : ℕ),
    fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha'
      (bounds.map Prod.fst) = some bounds →
    j ≤ bounds.length →
    fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha'
      ((bounds.map Prod.fst).take j) = some (bounds.take j) from
    aux hp_bounds i hsome hle
  clear hsome hle hp_bounds i
  intro bounds
  induction bounds using List.reverseRecOn with
  | nil =>
    intro j _ hle
    simp at hle; subst hle
    unfold fp_claimed_bounds; simp
  | append_singleton bs b ih =>
    intro j hsome hle
    obtain ⟨tsk_b, R_b⟩ := b
    simp only [List.map_append, List.map_cons, List.map_nil, Prod.fst] at hsome ⊢
    have hrcons := fp_claimed_bounds_rcons task_cost task_period task_deadline higher_priority alpha alpha'
      (List.map Prod.fst bs) bs tsk_b tsk_b R_b hsome
    obtain ⟨hprev, _, _, _⟩ := hrcons
    simp [List.length_append] at hle
    by_cases hj : j ≤ bs.length
    · rw [List.take_append_of_le_length (by simp [List.length_map]; exact hj)]
      rw [List.take_append_of_le_length hj]
      exact ih j hprev hj
    · push_neg at hj
      have hj_eq : j = bs.length + 1 := by omega
      subst hj_eq
      -- take (bs.length + 1) (map fst bs ++ [tsk_b]) = map fst bs ++ [tsk_b]
      -- take (bs.length + 1) (bs ++ [(tsk_b, R_b)]) = bs ++ [(tsk_b, R_b)]
      have h1 : List.take (bs.length + 1) (List.map Prod.fst bs ++ [tsk_b]) = List.map Prod.fst bs ++ [tsk_b] := by
        rw [List.take_of_length_le]; simp [List.length_map]
      have h2 : List.take (bs.length + 1) (bs ++ [(tsk_b, R_b)]) = bs ++ [(tsk_b, R_b)] := by
        rw [List.take_of_length_le]; simp
      rw [h1, h2]
      exact hsome

theorem fp_claimed_bounds_le_deadline :
    ∀ (ts' : List sporadic_task) (rt_bounds : List (sporadic_task × Time))
      (tsk : sporadic_task) (R : Time),
      fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha' ts' = some rt_bounds →
      (tsk, R) ∈ rt_bounds →
      R ≤ task_deadline tsk := by
  intro ts'
  induction ts' using List.reverseRecOn with
  | nil =>
    intro rt_bounds tsk R h hmem
    unfold fp_claimed_bounds at h
    simp [List.foldl] at h
    subst h; simp at hmem
  | append_singleton ts_init tsk_last ih =>
    intro rt_bounds tsk_i R h hmem
    by_cases hempty : rt_bounds = []
    · subst hempty; simp at hmem
    · -- rt_bounds is nonempty, decompose as init ++ [last]
      have hdecomp := List.dropLast_append_getLast hempty
      set last_elem := rt_bounds.getLast hempty with hlast_def
      set init := rt_bounds.dropLast with hinit_def
      rw [← hdecomp] at h hmem
      obtain ⟨last_tsk, last_R⟩ := last_elem
      have hrcons := fp_claimed_bounds_rcons task_cost task_period task_deadline higher_priority alpha alpha' ts_init init tsk_last last_tsk last_R h
      obtain ⟨hprev, htsk_eq, _, hle_dl⟩ := hrcons
      subst htsk_eq
      rw [List.mem_append] at hmem
      rcases hmem with hmem_init | hmem_last
      · exact ih init tsk_i R hprev hmem_init
      · simp at hmem_last
        obtain ⟨htsk, hR⟩ := hmem_last
        subst htsk; subst hR
        exact hle_dl

theorem fp_claimed_bounds_ge_cost :
    ∀ (ts' : List sporadic_task) (rt_bounds : List (sporadic_task × Time))
      (tsk : sporadic_task) (R : Time),
      fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha' ts' = some rt_bounds →
      (tsk, R) ∈ rt_bounds →
      R ≥ task_cost tsk := by
  intro ts'
  induction ts' using List.reverseRecOn with
  | nil =>
    intro rt_bounds tsk R h hmem
    unfold fp_claimed_bounds at h
    simp [List.foldl] at h
    subst h; simp at hmem
  | append_singleton ts_init tsk_last ih =>
    intro rt_bounds tsk_i R h hmem
    by_cases hempty : rt_bounds = []
    · subst hempty; simp at hmem
    · have hdecomp := List.dropLast_append_getLast hempty
      set last_elem := rt_bounds.getLast hempty with hlast_def
      set init := rt_bounds.dropLast with hinit_def
      rw [← hdecomp] at h hmem
      obtain ⟨last_tsk, last_R⟩ := last_elem
      have hrcons := fp_claimed_bounds_rcons task_cost task_period task_deadline higher_priority alpha alpha' ts_init init tsk_last last_tsk last_R h
      obtain ⟨hprev, htsk_eq, hR_eq, _⟩ := hrcons
      subst htsk_eq
      rw [List.mem_append] at hmem
      rcases hmem with hmem_init | hmem_last
      · exact ih init tsk_i R hprev hmem_init
      · simp at hmem_last
        obtain ⟨htsk, hR⟩ := hmem_last
        subst htsk; subst hR
        rw [hR_eq]
        unfold per_task_rta
        -- Show f^[n] (task_cost tsk_i) ≥ task_cost tsk_i by induction on n
        set F := (fun t => task_cost tsk_i +
          div_floor
            (total_interference_bound_fp task_cost task_period alpha tsk_i (alpha' tsk_i) init t higher_priority)
            (alpha' tsk_i).card)
        suffices h : ∀ n, F^[n] (task_cost tsk_i) ≥ task_cost tsk_i by exact h _
        intro n; induction n with
        | zero => simp
        | succ n ih =>
          rw [Function.iterate_succ', Function.comp]
          exact Nat.le_add_right _ _

theorem per_task_rta_fold :
    ∀ (tsk : sporadic_task) (rt_bounds : List (sporadic_task × Time)),
      task_cost tsk +
        div_floor
          (total_interference_bound_fp task_cost task_period alpha tsk (alpha' tsk) rt_bounds
            (per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds
              (max_steps task_deadline task_cost tsk))
            higher_priority)
          (alpha' tsk).card =
      per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds
        (max_steps task_deadline task_cost tsk + 1) := by
  intro tsk rt_bounds
  unfold per_task_rta
  rw [Function.iterate_succ']
  rfl

end SimpleLemmas

section HighPriorityTasks

variable (ts : List sporadic_task)
variable (H_task_set_is_sorted : List.IsChain (fun a b => higher_priority a b = true) ts)
variable (H_task_set_has_unique_priorities :
  FP_is_antisymmetric_over_task_set higher_priority ts)
variable (H_priority_transitive : FP_is_transitive higher_priority)
variable (hp_bounds : List (sporadic_task × Time))
variable (R : Time)
variable (H_analysis_succeeds :
  fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha' ts = some hp_bounds)
variable (elem : sporadic_task)

include H_task_set_is_sorted H_task_set_has_unique_priorities
  H_priority_transitive H_analysis_succeeds in
include H_task_set_is_sorted H_task_set_has_unique_priorities H_priority_transitive H_analysis_succeeds in
theorem fp_claimed_bounds_hp_tasks_have_smaller_index :
    ∀ (hp_idx idx : ℕ),
      hp_idx < ts.length →
      idx < ts.length →
      hp_idx ≠ idx →
      higher_priority (ts.getD hp_idx elem) (ts.getD idx elem) = true →
      hp_idx < idx := by
  sorry

end HighPriorityTasks

section Convergence

variable (ts_hp : List sporadic_task)
variable (rt_bounds : List (sporadic_task × Time))
variable (H_test_succeeds :
  fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha' ts_hp = some rt_bounds)
variable (tsk : sporadic_task)
variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline (ts_hp ++ [tsk]))
variable (H_no_larger_than_deadline :
  per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds
    (max_steps task_deadline task_cost tsk) ≤ task_deadline tsk)

include H_test_succeeds H_valid_task_parameters H_no_larger_than_deadline in
theorem bertogna_fp_comp_f_monotonic :
    ∀ (x1 x2 : ℕ), x1 ≤ x2 →
      per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds x1 ≤
        per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds x2 := by
  intro x1 x2 hle
  unfold per_task_rta
  apply fun_mon_iter_mon
  · exact hle
  · -- f (task_cost tsk) ≥ task_cost tsk
    exact Nat.le_add_right _ _
  · -- f is monotone
    intro y1 y2 hle_y
    show task_cost tsk + div_floor (total_interference_bound_fp task_cost task_period alpha tsk (alpha' tsk) rt_bounds y1 higher_priority) (alpha' tsk).card ≤
         task_cost tsk + div_floor (total_interference_bound_fp task_cost task_period alpha tsk (alpha' tsk) rt_bounds y2 higher_priority) (alpha' tsk).card
    apply Nat.add_le_add_left
    apply Nat.div_le_div_right
    unfold total_interference_bound_fp
    -- Show pointwise sum comparison for the same filtered list
    have hpw : ∀ tsk_R, tsk_R ∈ rt_bounds →
        interference_bound_generic task_cost task_period tsk y1 tsk_R ≤
        interference_bound_generic task_cost task_period tsk y2 tsk_R := by
      intro ⟨i, R_i⟩ hmem_bounds
      unfold interference_bound_generic
      apply min_le_min
      · -- W monotonic in delta
        have hge_cost := fp_claimed_bounds_ge_cost task_cost task_period task_deadline higher_priority alpha alpha' ts_hp rt_bounds i R_i H_test_succeeds hmem_bounds
        have hunzip := fp_claimed_bounds_unzip task_cost task_period task_deadline higher_priority alpha alpha' ts_hp rt_bounds H_test_succeeds
        have hmem_ts : i ∈ ts_hp := by
          rw [← hunzip]; exact List.mem_map.mpr ⟨(i, R_i), hmem_bounds, rfl⟩
        have hvalid := H_valid_task_parameters i (List.mem_append_left [tsk] hmem_ts)
        obtain ⟨_, hperiod_pos, _, _, _⟩ := hvalid
        exact W_monotonic task_cost task_period i hperiod_pos R_i R_i hge_cost (le_refl _) y1 y2 hle_y
      · -- delta - task_cost tsk + 1 monotonic in delta
        omega
    -- Now prove the sum inequality
    set filtered := rt_bounds.filter (fun tsk_R =>
      decide (higher_priority_task_in alpha higher_priority tsk (alpha' tsk) tsk_R.1))
    have : ∀ x, x ∈ filtered → interference_bound_generic task_cost task_period tsk y1 x ≤
        interference_bound_generic task_cost task_period tsk y2 x := by
      intro x hx; exact hpw x (List.mem_of_mem_filter hx)
    -- Prove by induction on the filtered list
    have hsuf : ∀ (l : List (sporadic_task × Time)),
        (∀ x, x ∈ l → interference_bound_generic task_cost task_period tsk y1 x ≤
            interference_bound_generic task_cost task_period tsk y2 x) →
        (l.map (fun tsk_R => interference_bound_generic task_cost task_period tsk y1 tsk_R)).sum ≤
        (l.map (fun tsk_R => interference_bound_generic task_cost task_period tsk y2 tsk_R)).sum := by
      intro l hl
      induction l with
      | nil => simp
      | cons hd tl ihtl =>
        simp only [List.map_cons, List.sum_cons]
        apply Nat.add_le_add
        · exact hl hd (List.mem_cons.mpr (Or.inl rfl))
        · exact ihtl (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx)))
    exact hsuf filtered (fun x hx => hpw x (List.mem_of_mem_filter hx))

include H_test_succeeds H_valid_task_parameters H_no_larger_than_deadline in
theorem bertogna_fp_comp_f_converges_early :
    (∃ k, k ≤ max_steps task_deadline task_cost tsk ∧
      per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds k =
        per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds (k + 1)) →
    per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds
      (max_steps task_deadline task_cost tsk) =
      per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds
        (max_steps task_deadline task_cost tsk + 1) := by
  sorry

section DerivingContradiction

variable (H_keeps_diverging :
  ∀ k, k ≤ max_steps task_deadline task_cost tsk →
    per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds k ≠
      per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds (k + 1))

include H_test_succeeds H_valid_task_parameters H_no_larger_than_deadline
  H_keeps_diverging in
include H_test_succeeds H_valid_task_parameters H_no_larger_than_deadline H_keeps_diverging in
theorem bertogna_fp_comp_f_increases :
    ∀ k, k ≤ max_steps task_deadline task_cost tsk →
      per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds k <
        per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds (k + 1) := by
  sorry

include H_valid_task_parameters H_keeps_diverging H_test_succeeds H_no_larger_than_deadline in
theorem bertogna_fp_comp_rt_grows_too_much :
    ∀ k, k ≤ max_steps task_deadline task_cost tsk →
      per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds k >
        k + task_cost tsk - 1 := by
  sorry

end DerivingContradiction

include H_test_succeeds H_valid_task_parameters H_no_larger_than_deadline in
theorem per_task_rta_converges :
    per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds
      (max_steps task_deadline task_cost tsk) =
      per_task_rta task_cost task_period higher_priority alpha alpha' tsk rt_bounds
        (max_steps task_deadline task_cost tsk + 1) := by
  sorry

end Convergence

section MainProof

variable (ts : List sporadic_task)

variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)

variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable (H_non_empty_affinity :
  ∀ tsk, tsk ∈ ts → (alpha' tsk).card > 0)
variable (H_subaffinity :
  ∀ tsk, tsk ∈ ts → is_subaffinity (alpha' tsk) (alpha tsk))

variable (H_task_set_is_sorted :
  List.IsChain (fun a b => higher_priority a b = true) ts)
variable (H_task_set_has_unique_priorities :
  FP_is_antisymmetric_over_task_set higher_priority ts)
variable (H_priority_is_total :
  FP_is_total_over_task_set higher_priority ts)
variable (H_priority_transitive : FP_is_transitive higher_priority)

variable (arr_seq : arrival_sequence Job)

variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (H_valid_job_parameters :
  ∀ j,
    arrives_in arr_seq j →
    valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

variable (H_sporadic_tasks :
  sporadic_task_model task_period job_arrival job_task arr_seq)

variable (sched : schedule Job num_cpus)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_sequential_jobs : sequential_jobs sched)

variable (H_respects_affinity : respects_affinity job_task sched alpha)
variable (H_work_conserving :
  apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
variable (H_respects_FP_policy :
  respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched
    alpha higher_priority)

private noncomputable abbrev no_deadline_missed_by_task' (tsk : sporadic_task) :=
  task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

private noncomputable abbrev no_deadline_missed_by_job' (j : Job) :=
  job_misses_no_deadline job_arrival job_cost job_deadline sched j

private noncomputable abbrev response_time_bounded_by' (tsk : sporadic_task) (R : Time) :=
  is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R

include H_valid_task_parameters H_constrained_deadlines
  H_non_empty_affinity H_subaffinity
  H_task_set_is_sorted H_task_set_has_unique_priorities
  H_priority_is_total H_priority_transitive
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks
  H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_sequential_jobs
  H_respects_affinity H_work_conserving H_respects_FP_policy in
include H_valid_task_parameters H_constrained_deadlines H_non_empty_affinity H_subaffinity H_task_set_is_sorted H_task_set_has_unique_priorities H_priority_is_total H_priority_transitive H_all_jobs_from_taskset H_valid_job_parameters H_sporadic_tasks H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_respects_affinity H_work_conserving H_respects_FP_policy in
theorem fp_analysis_yields_response_time_bounds :
    ∀ (tsk : sporadic_task) (R : Time),
      (match fp_claimed_bounds task_cost task_period task_deadline higher_priority alpha alpha' ts with
       | some rt_bounds => (tsk, R) ∈ rt_bounds
       | none => False) →
      response_time_bounded_by' job_arrival job_cost job_task arr_seq sched tsk R := by
  sorry

variable (H_test_succeeds :
  fp_schedulable task_cost task_period task_deadline higher_priority alpha alpha' ts)

include H_valid_task_parameters H_constrained_deadlines
  H_non_empty_affinity H_subaffinity
  H_task_set_is_sorted H_task_set_has_unique_priorities
  H_priority_is_total H_priority_transitive
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks
  H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_sequential_jobs
  H_respects_affinity H_work_conserving H_respects_FP_policy
  H_test_succeeds in
include H_valid_task_parameters H_constrained_deadlines H_non_empty_affinity H_subaffinity H_task_set_is_sorted H_task_set_has_unique_priorities H_priority_is_total H_priority_transitive H_all_jobs_from_taskset H_valid_job_parameters H_sporadic_tasks H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_respects_affinity H_work_conserving H_respects_FP_policy H_test_succeeds in
theorem taskset_schedulable_by_fp_rta :
    ∀ tsk, tsk ∈ ts →
      no_deadline_missed_by_task' job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
  sorry

include H_valid_task_parameters H_constrained_deadlines
  H_non_empty_affinity H_subaffinity
  H_task_set_is_sorted H_task_set_has_unique_priorities
  H_priority_is_total H_priority_transitive
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks
  H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_sequential_jobs
  H_respects_affinity H_work_conserving H_respects_FP_policy
  H_test_succeeds in
include H_valid_task_parameters H_constrained_deadlines H_non_empty_affinity H_subaffinity H_task_set_is_sorted H_task_set_has_unique_priorities H_priority_is_total H_priority_transitive H_all_jobs_from_taskset H_valid_job_parameters H_sporadic_tasks H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_respects_affinity H_work_conserving H_respects_FP_policy H_test_succeeds in
theorem jobs_schedulable_by_fp_rta :
    ∀ j, arrives_in arr_seq j →
      no_deadline_missed_by_job' job_arrival job_cost job_deadline sched j := by
  sorry

end MainProof

end Analysis

end ResponseTimeIterationFP

end Prosa.Classic.Analysis.Apa.Bertogna_fp_comp
