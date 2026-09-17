-- Translated from: ../rt-proofs/classic/analysis/global/parallel/bertogna_edf_comp.v
import Prosa.Classic.Util.All
import Prosa.Classic.Analysis.Global.Parallel.Bertogna_edf_theory
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Global.Parallel.Bertogna_edf_comp

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
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference_edf.InterferenceEDF
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Global.Parallel.Bertogna_edf_theory.ResponseTimeAnalysisEDF
open Prosa.Classic.Analysis.Global.Parallel.Interference_bound_edf.InterferenceBoundEDF
open Prosa.Classic.Analysis.Global.Parallel.Workload_bound.WorkloadBound
open Prosa.Util.Div_mod
open Prosa.Classic.Util.Fixedpoint

attribute [local instance] Classical.propDecidable

namespace ResponseTimeIterationEDF

section Analysis

variable {sporadic_task : Type} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

abbrev task_with_response_time (sporadic_task : Type) := (sporadic_task × Time)

variable {Job : Type} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)

variable (num_cpus : ℕ)
private abbrev I (rt_bounds : List (sporadic_task × Time))
    (tsk : sporadic_task) (delta : Time) : ℕ :=
  total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds delta

def edf_response_time_bound (rt_bounds : List (sporadic_task × Time))
    (tsk : sporadic_task) (delta : Time) : Time :=
  task_cost tsk + div_floor (total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds delta) num_cpus

def R_le_deadline (pair : sporadic_task × Time) : Bool :=
  decide (pair.2 ≤ task_deadline pair.1)

def update_bound (rt_bounds : List (sporadic_task × Time))
    (pair : sporadic_task × Time) : sporadic_task × Time :=
  (pair.1, edf_response_time_bound task_cost task_period task_deadline num_cpus rt_bounds pair.1 pair.2)

private def initial_state (ts : List sporadic_task) : List (sporadic_task × Time) :=
  ts.map (fun t => (t, task_cost t))

def edf_rta_iteration (rt_bounds : List (sporadic_task × Time)) :
    List (sporadic_task × Time) :=
  rt_bounds.map (update_bound task_cost task_period task_deadline num_cpus rt_bounds)

private def max_steps (ts : List sporadic_task) : ℕ :=
  (ts.map (fun tsk => task_deadline tsk - task_cost tsk)).sum + 1

def edf_claimed_bounds (ts : List sporadic_task) :
    Option (List (sporadic_task × Time)) :=
  let R_values := (edf_rta_iteration task_cost task_period task_deadline num_cpus)^[max_steps task_deadline task_cost ts]
                    (initial_state task_cost ts)
  if R_values.all (R_le_deadline task_deadline) then
    some R_values
  else none

def edf_schedulable (ts : List sporadic_task) : Prop :=
  edf_claimed_bounds task_cost task_period task_deadline num_cpus ts ≠ none

section SimpleLemmas

theorem edf_claimed_bounds_unzip1_update_bound :
    ∀ (l rt_bounds : List (sporadic_task × Time)),
      (l.map (update_bound task_cost task_period task_deadline num_cpus rt_bounds)).map Prod.fst =
        l.map Prod.fst := by
    intro l rt_bounds
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp [update_bound, ih]

theorem edf_claimed_bounds_unzip1_iteration :
    ∀ (l : List sporadic_task) (k : ℕ),
      ((edf_rta_iteration task_cost task_period task_deadline num_cpus)^[k]
        (initial_state task_cost l)).map Prod.fst = l := by
    intro l k
    induction k with
    | zero =>
      simp [initial_state]
      induction l with
      | nil => simp
      | cons hd tl ih => simp [ih]
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp]
      unfold edf_rta_iteration
      rw [edf_claimed_bounds_unzip1_update_bound]
      exact ih

theorem edf_claimed_bounds_size :
    ∀ (l : List sporadic_task) (k : ℕ),
      ((edf_rta_iteration task_cost task_period task_deadline num_cpus)^[k]
        (initial_state task_cost l)).length = l.length := by
    intro l k
    have h := edf_claimed_bounds_unzip1_iteration task_cost task_period task_deadline num_cpus l k
    have : ((edf_rta_iteration task_cost task_period task_deadline num_cpus)^[k]
        (initial_state task_cost l)).length =
        (((edf_rta_iteration task_cost task_period task_deadline num_cpus)^[k]
        (initial_state task_cost l)).map Prod.fst).length := by
      rw [List.length_map]
    rw [this, h]

theorem edf_claimed_bounds_ge_cost :
    ∀ (l : List sporadic_task) (k : ℕ) (tsk : sporadic_task) (R : Time),
      (tsk, R) ∈ (edf_rta_iteration task_cost task_period task_deadline num_cpus)^[k]
        (initial_state task_cost l) →
      R ≤ task_cost tsk := by
    sorry
theorem edf_claimed_bounds_le_deadline :
    ∀ (ts : List sporadic_task) (rt_bounds : List (sporadic_task × Time))
      (tsk : sporadic_task) (R : Time),
      edf_claimed_bounds task_cost task_period task_deadline num_cpus ts = some rt_bounds →
      (tsk, R) ∈ rt_bounds →
      R ≤ task_deadline tsk := by
    intro ts rt_bounds tsk R SOME PAIR
    simp only [edf_claimed_bounds] at SOME
    set R_values := (edf_rta_iteration task_cost task_period task_deadline num_cpus)^[max_steps task_deadline task_cost ts]
                    (initial_state task_cost ts) with hRv
    by_cases h : R_values.all (R_le_deadline task_deadline) = true
    · simp [h] at SOME
      rw [← SOME] at PAIR
      rw [List.all_eq_true] at h
      have := h (tsk, R) PAIR
      simp [R_le_deadline] at this
      exact this
    · simp [h] at SOME

theorem edf_claimed_bounds_has_R_for_every_task :
    ∀ (ts : List sporadic_task) (rt_bounds : List (sporadic_task × Time))
      (tsk : sporadic_task),
      edf_claimed_bounds task_cost task_period task_deadline num_cpus ts = some rt_bounds →
      tsk ∈ ts →
      ∀ R, (tsk, R) ∈ rt_bounds := by
    sorry
end SimpleLemmas

section Convergence

variable (ts : List sporadic_task)
variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)

private abbrev f (k : ℕ) : List (sporadic_task × Time) :=
  (edf_rta_iteration task_cost task_period task_deadline num_cpus)^[k]
    (initial_state task_cost ts)

private def all_le (l1 l2 : List (sporadic_task × Time)) : Prop :=
  l1.map Prod.fst = l2.map Prod.fst ∧
  ∀ p, p ∈ l1.zip l2 → p.1.2 ≤ p.2.2

private def one_lt (l1 l2 : List (sporadic_task × Time)) : Prop :=
  l1.map Prod.fst = l2.map Prod.fst ∧
  ∃ p, p ∈ l1.zip l2 ∧ p.1.2 < p.2.2

section RelationProperties

include H_valid_task_parameters in
theorem all_le_reflexive :
    ∀ l : List (sporadic_task × Time),
      all_le l l := by
    intro l
    constructor
    · rfl
    · intro p hp
      rw [List.mem_iff_getElem] at hp
      obtain ⟨i, hi, hget⟩:= hp
      have hlen : (l.zip l).length = l.length := by simp [List.length_zip]
      have hi_l : i < l.length := by omega
      have hzip : (l.zip l)[i] = (l[i]'hi_l, l[i]'hi_l) := List.getElem_zip
      rw [hzip] at hget
      rw [← hget]

include H_valid_task_parameters in
theorem all_le_transitive :
    ∀ x y z : List (sporadic_task × Time),
      all_le x y → all_le y z → all_le x z := by
    intro x y z ⟨hxy_fst, hxy_le⟩⟨hyz_fst, hyz_le⟩
    constructor
    · rw [hxy_fst, hyz_fst]
    · intro p hp
      have hlen_xy : x.length = y.length := by
        have h := congrArg List.length hxy_fst; simp at h; exact h
      have hlen_yz : y.length = z.length := by
        have h := congrArg List.length hyz_fst; simp at h; exact h
      rw [List.mem_iff_getElem] at hp
      obtain ⟨i, hi, hget⟩:= hp
      have hlen_xz : (x.zip z).length = x.length := by simp [List.length_zip, hlen_xy, hlen_yz, Nat.min_eq_left (by omega : x.length ≤ z.length)]
      have hi_x : i < x.length := by omega
      have hi_y : i < y.length := by omega
      have hi_z : i < z.length := by omega
      have hzip_xz : (x.zip z)[i] = (x[i]'hi_x, z[i]'hi_z) := List.getElem_zip
      rw [hzip_xz] at hget
      rw [← hget]
      simp only
      have hxy_pair : (x[i]'hi_x, y[i]'hi_y) ∈ x.zip y := by
        rw [List.mem_iff_getElem]
        refine ⟨i, ?_, ?_⟩
        · simp [List.length_zip]; omega
        · exact List.getElem_zip
      have hyz_pair : (y[i]'hi_y, z[i]'hi_z) ∈ y.zip z := by
        rw [List.mem_iff_getElem]
        refine ⟨i, ?_, ?_⟩
        · simp [List.length_zip]; omega
        · exact List.getElem_zip
      have h1 := hxy_le _ hxy_pair
      have h2 := hyz_le _ hyz_pair
      simp at h1 h2
      exact le_trans h1 h2

include H_valid_task_parameters in
theorem bertogna_edf_comp_iteration_preserves_minimum :
    ∀ step,
      all_le (initial_state task_cost ts)
        (f task_cost task_period task_deadline num_cpus ts step) := by
    sorry
include H_valid_task_parameters in
theorem bertogna_edf_comp_iteration_inductive (P : List (sporadic_task × Time) → Prop) :
    P (initial_state task_cost ts) →
    (∀ k, P (f task_cost task_period task_deadline num_cpus ts k) →
      P (f task_cost task_period task_deadline num_cpus ts (k + 1))) →
    P (f task_cost task_period task_deadline num_cpus ts (max_steps task_deadline task_cost ts)) := by
    intro P0 Pn
    have : ∀ n, P (f task_cost task_period task_deadline num_cpus ts n) := by
      intro n
      induction n with
      | zero => exact P0
      | succ k ih => exact Pn k ih
    exact this _

include H_valid_task_parameters in
theorem bertogna_edf_comp_iteration_preserves_order :
    ∀ l1 l2 : List (sporadic_task × Time),
      all_le (initial_state task_cost ts) l1 →
      all_le l1 l2 →
      all_le (edf_rta_iteration task_cost task_period task_deadline num_cpus l1)
        (edf_rta_iteration task_cost task_period task_deadline num_cpus l2) := by
    sorry
include H_valid_task_parameters in
theorem bertogna_edf_comp_iteration_monotonic :
    ∀ k, all_le (f task_cost task_period task_deadline num_cpus ts k)
      (f task_cost task_period task_deadline num_cpus ts (k + 1)) := by
    intro k
    show all_le ((edf_rta_iteration task_cost task_period task_deadline num_cpus)^[k]
        (initial_state task_cost ts))
      ((edf_rta_iteration task_cost task_period task_deadline num_cpus)^[k + 1]
        (initial_state task_cost ts))
    exact fun_mon_iter_mon_helper _ (edf_rta_iteration task_cost task_period task_deadline num_cpus) all_le (initial_state task_cost ts) k
      (fun l => @all_le_reflexive _ _ task_cost task_period task_deadline ts H_valid_task_parameters l)
      (fun x y z hxy hyz => @all_le_transitive _ _ task_cost task_period task_deadline ts H_valid_task_parameters x y z hxy hyz)
      (fun n => @bertogna_edf_comp_iteration_preserves_minimum _ _ task_cost task_period task_deadline num_cpus ts H_valid_task_parameters n)
      (fun l1 l2 h1 h2 => @bertogna_edf_comp_iteration_preserves_order _ _ task_cost task_period task_deadline num_cpus ts H_valid_task_parameters l1 l2 h1 h2)

end RelationProperties

theorem bertogna_edf_comp_f_converges_with_no_tasks :
    ts.length = 0 →
    f task_cost task_period task_deadline num_cpus ts (max_steps task_deadline task_cost ts) =
      f task_cost task_period task_deadline num_cpus ts (max_steps task_deadline task_cost ts + 1) := by
    intro SIZE
    have hts : ts = [] := by
      cases ts with
      | nil => rfl
      | cons _ _ => simp at SIZE
    subst hts
    simp [f, max_steps, initial_state, edf_rta_iteration]

theorem bertogna_edf_comp_f_converges_early :
    (∃ k, k ≤ max_steps task_deadline task_cost ts ∧
      f task_cost task_period task_deadline num_cpus ts k =
        f task_cost task_period task_deadline num_cpus ts (k + 1)) →
    f task_cost task_period task_deadline num_cpus ts (max_steps task_deadline task_cost ts) =
      f task_cost task_period task_deadline num_cpus ts (max_steps task_deadline task_cost ts + 1) := by
    intro ⟨k, hk_le, hk_eq⟩
    show (edf_rta_iteration task_cost task_period task_deadline num_cpus)^[max_steps task_deadline task_cost ts]
        (initial_state task_cost ts) =
      (edf_rta_iteration task_cost task_period task_deadline num_cpus)^[max_steps task_deadline task_cost ts + 1]
        (initial_state task_cost ts)
    exact iter_fix _ (edf_rta_iteration task_cost task_period task_deadline num_cpus) (initial_state task_cost ts) k (max_steps task_deadline task_cost ts) hk_eq hk_le

section DerivingContradiction

variable (H_at_least_one_task : ts.length > 0)
variable (H_keeps_diverging :
  ∀ k, k ≤ max_steps task_deadline task_cost ts →
    f task_cost task_period task_deadline num_cpus ts k ≠
      f task_cost task_period task_deadline num_cpus ts (k + 1))

include H_valid_task_parameters H_at_least_one_task H_keeps_diverging in
theorem bertogna_edf_comp_f_increases :
    ∀ k, k ≤ max_steps task_deadline task_cost ts →
      one_lt (f task_cost task_period task_deadline num_cpus ts k)
        (f task_cost task_period task_deadline num_cpus ts (k + 1)) := by
    intro step hstep
    set fk := f task_cost task_period task_deadline num_cpus ts step with hfk_def
    set fk1 := f task_cost task_period task_deadline num_cpus ts (step + 1) with hfk1_def
    have MONO := @bertogna_edf_comp_iteration_monotonic _ _ task_cost task_period task_deadline num_cpus ts H_valid_task_parameters step
    change all_le (f task_cost task_period task_deadline num_cpus ts step) (f task_cost task_period task_deadline num_cpus ts (step + 1)) at MONO
    obtain ⟨hfst_eq, hle⟩:= MONO
    change fk.map Prod.fst = fk1.map Prod.fst at hfst_eq
    constructor
    · exact hfst_eq
    · -- Need to show: ∀p, p ∈fk.zip fk1 ∈p.1.2 < p.2.2
      -- By contradiction: if no pair is strictly less, then all are ≤from MONO and ≤from negation
      -- So all equal →fk = fk1 →contradicts H_keeps_diverging
      by_contra h_no_lt
      push_neg at h_no_lt
      -- h_no_lt : ∀ p ∈fk.zip fk1, ¬(p.1.2 < p.2.2), i.e., p.2.2 ≤p.1.2
      have h_eq : fk = fk1 := by
        have hlen_eq : fk.length = fk1.length := by
          have h := congrArg List.length hfst_eq; simp at h; exact h
        apply List.ext_getElem
        · exact hlen_eq
        · intro i hi hi'
          have hi_zip : i < (fk.zip fk1).length := by simp [List.length_zip]; omega
          have hmem : (fk[i], fk1[i]) ∈ fk.zip fk1 := by
            rw [List.mem_iff_getElem]
            exact ⟨i, hi_zip, List.getElem_zip⟩
          have h1 : (fk[i]).2 ≤ (fk1[i]).2 := by
            have := hle ((fk[i], fk1[i])) hmem; simp at this; exact this
          have h2 : (fk1[i]).2 ≤ (fk[i]).2 := by
            have := h_no_lt ((fk[i], fk1[i])) hmem; simp at this; exact this
          have hfst_i : (fk[i]).1 = (fk1[i]).1 := by
            have h1f : (fk.map Prod.fst)[i]'(by simp; exact hi) = (fk[i]).1 := List.getElem_map ..
            have h2f : (fk1.map Prod.fst)[i]'(by simp; exact hi') = (fk1[i]).1 := List.getElem_map ..
            have : (fk.map Prod.fst)[i]'(by simp; exact hi) = (fk1.map Prod.fst)[i]'(by simp; exact hi') := by
              congr 1
            rw [h1f] at this; rw [h2f] at this; exact this
          have h3 : (fk[i]).2 = (fk1[i]).2 := Nat.le_antisymm h1 h2
          exact Prod.ext hfst_i h3
      exact H_keeps_diverging step hstep h_eq

include H_valid_task_parameters H_at_least_one_task H_keeps_diverging in
theorem bertogna_edf_comp_rt_grows_too_much :
    ∀ k, k ≤ max_steps task_deadline task_cost ts →
      ((f task_cost task_period task_deadline num_cpus ts k).map
        (fun p => p.2 - task_cost p.1)).sum + 1 > k := by
    sorry
end DerivingContradiction

include H_valid_task_parameters in
theorem edf_claimed_bounds_finds_fixed_point_of_list :
    ∀ rt_bounds : List (sporadic_task × Time),
      edf_claimed_bounds task_cost task_period task_deadline num_cpus ts = some rt_bounds →
      valid_sporadic_taskset task_cost task_period task_deadline ts →
      f task_cost task_period task_deadline num_cpus ts (max_steps task_deadline task_cost ts) =
        edf_rta_iteration task_cost task_period task_deadline num_cpus
          (f task_cost task_period task_deadline num_cpus ts (max_steps task_deadline task_cost ts)) := by
    sorry
include H_valid_task_parameters in
theorem edf_claimed_bounds_finds_least_fixed_point :
    ∀ v : List (sporadic_task × Time),
      all_le (initial_state task_cost ts) v →
      v = edf_rta_iteration task_cost task_period task_deadline num_cpus v →
      all_le (f task_cost task_period task_deadline num_cpus ts (max_steps task_deadline task_cost ts)) v := by
    intro v GE0 EQ
    apply @bertogna_edf_comp_iteration_inductive _ _ task_cost task_period task_deadline num_cpus ts H_valid_task_parameters (fun l => all_le l v)
    · exact GE0
    · intro k GEk
      show all_le (f task_cost task_period task_deadline num_cpus ts (k + 1)) v
      have : f task_cost task_period task_deadline num_cpus ts (k + 1) =
        edf_rta_iteration task_cost task_period task_deadline num_cpus
          (f task_cost task_period task_deadline num_cpus ts k) := by
        show (edf_rta_iteration task_cost task_period task_deadline num_cpus)^[k + 1] (initial_state task_cost ts) =
          edf_rta_iteration task_cost task_period task_deadline num_cpus
            ((edf_rta_iteration task_cost task_period task_deadline num_cpus)^[k] (initial_state task_cost ts))
        rw [Function.iterate_succ']
        rfl
      rw [this, EQ]
      exact @bertogna_edf_comp_iteration_preserves_order _ _ task_cost task_period task_deadline num_cpus ts H_valid_task_parameters
        (f task_cost task_period task_deadline num_cpus ts k) v
        (@bertogna_edf_comp_iteration_preserves_minimum _ _ task_cost task_period task_deadline num_cpus ts H_valid_task_parameters k) GEk

include H_valid_task_parameters in
theorem edf_claimed_bounds_finds_fixed_point_for_each_bound :
    ∀ (tsk : sporadic_task) (R : Time) (rt_bounds : List (sporadic_task × Time)),
      edf_claimed_bounds task_cost task_period task_deadline num_cpus ts = some rt_bounds →
      (tsk, R) ∈ rt_bounds →
      R = edf_response_time_bound task_cost task_period task_deadline num_cpus rt_bounds tsk R := by
    intro tsk R rt_bounds SOME IN
    -- First derive that rt_bounds is the fixed-point iteration result
    have CONV := edf_claimed_bounds_finds_fixed_point_of_list task_cost task_period task_deadline num_cpus ts H_valid_task_parameters rt_bounds SOME H_valid_task_parameters
    -- Show rt_bounds = edf_rta_iteration rt_bounds
    -- CONV says f(ms) = edf_rta_iteration(f(ms)), and rt_bounds = f(ms) from SOME
    have h_rt_eq : rt_bounds = edf_rta_iteration task_cost task_period task_deadline num_cpus rt_bounds := by
      -- Extract from SOME that rt_bounds = f(ms)
      unfold edf_claimed_bounds at SOME
      set rv := (edf_rta_iteration task_cost task_period task_deadline num_cpus)^[max_steps task_deadline task_cost ts] (initial_state task_cost ts) with hrv
      by_cases hcond : rv.all (R_le_deadline task_deadline) = true
      · have h_some : some rv = some rt_bounds := by simpa [hcond] using SOME
        have h_eq : rv = rt_bounds := by exact Option.some_injective _ h_some
        rw [← h_eq]
        exact CONV
      · simp only [edf_claimed_bounds] at SOME
        simp only [Bool.not_eq_true] at hcond
        rw [hcond] at SOME
        simp at SOME
    -- rt_bounds = rt_bounds.map (update_bound rt_bounds)
    -- (tsk, R) ∈rt_bounds, so at some index i, rt_bounds[i] = (tsk, R)
    -- and rt_bounds[i] = update_bound rt_bounds (rt_bounds[i]) = update_bound rt_bounds (tsk, R)
    rw [List.mem_iff_getElem] at IN
    obtain ⟨i, hi, hget⟩:= IN
    have h_iter_len : (edf_rta_iteration task_cost task_period task_deadline num_cpus rt_bounds).length = rt_bounds.length := by
      simp [edf_rta_iteration]
    have hi2 : i < (edf_rta_iteration task_cost task_period task_deadline num_cpus rt_bounds).length := by omega
    have h_get_iter : (edf_rta_iteration task_cost task_period task_deadline num_cpus rt_bounds)[i] =
        update_bound task_cost task_period task_deadline num_cpus rt_bounds (rt_bounds[i]) := by
      simp [edf_rta_iteration, List.getElem_map]
    -- From h_rt_eq : rt_bounds = edf_rta_iteration rt_bounds
    -- rt_bounds[i] = (edf_rta_iteration rt_bounds)[i] = update_bound rt_bounds rt_bounds[i]
    -- Since rt_bounds[i] = (tsk, R), we get (tsk, R) = update_bound rt_bounds (tsk, R)
    -- use eq to transfer getElem
    have h2 : rt_bounds[i] = (edf_rta_iteration task_cost task_period task_deadline num_cpus rt_bounds)[i] := by
      congr 1
    rw [h_get_iter] at h2
    rw [hget] at h2
    simp only [update_bound] at h2
    exact congrArg Prod.snd h2

end Convergence

section MainProof

variable (ts : List sporadic_task)

variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)

variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable (arr_seq : arrival_sequence Job)

variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (H_valid_job_parameters :
  ∀ j,
    arrives_in arr_seq j →
    valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

variable (H_sporadic_tasks :
  sporadic_task_model task_period job_arrival job_task arr_seq)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (H_at_least_one_cpu : num_cpus > 0)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
variable (H_edf_policy : respects_JLFP_policy job_arrival job_cost arr_seq sched
                                             (EDF job_arrival job_deadline))

private abbrev no_deadline_missed_by_task_def (tsk : sporadic_task) :=
  task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

private abbrev no_deadline_missed_by_job_def :=
  job_misses_no_deadline job_arrival job_cost job_deadline sched

private abbrev response_time_bounded_by (tsk : sporadic_task) (R : Time) :=
  is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R

include H_valid_task_parameters H_constrained_deadlines
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks H_at_least_one_cpu
  H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_work_conserving H_edf_policy in
theorem edf_analysis_yields_response_time_bounds :
    ∀ (tsk : sporadic_task) (R : Time),
      (match edf_claimed_bounds task_cost task_period task_deadline num_cpus ts with
       | some rt_bounds => (tsk, R) ∈ rt_bounds
       | none => False) →
      response_time_bounded_by job_arrival job_cost job_task arr_seq sched tsk R := by
    intro tsk R IN
    match h : edf_claimed_bounds task_cost task_period task_deadline num_cpus ts with
    | some rt_bounds =>
      rw [h] at IN
      have h_unzip : rt_bounds.map Prod.fst = ts := by
        simp only [edf_claimed_bounds] at h
        set rv := (edf_rta_iteration task_cost task_period task_deadline num_cpus)^[max_steps task_deadline task_cost ts] (initial_state task_cost ts) with hrv
        by_cases hcond : rv.all (R_le_deadline task_deadline) = true
        · simp [hcond] at h; rw [← h]
          exact edf_claimed_bounds_unzip1_iteration task_cost task_period task_deadline num_cpus ts _
        · simp [hcond] at h
      have h_fixed : ∀ tsk' R', (tsk', R') ∈ rt_bounds →
          R' = edf_response_time_bound task_cost task_period task_deadline num_cpus rt_bounds tsk' R' :=
        fun tsk' R' h_in => edf_claimed_bounds_finds_fixed_point_for_each_bound task_cost task_period task_deadline num_cpus ts H_valid_task_parameters tsk' R' rt_bounds h h_in
      have h_fixed' : ∀ tsk' R', (tsk', R') ∈ rt_bounds →
          R' = task_cost tsk' + div_floor (total_interference_bound_edf task_cost task_period task_deadline tsk' rt_bounds R') num_cpus := by
        intro tsk' R' h_in
        exact h_fixed tsk' R' h_in
      have h_dl : ∀ tsk' R', (tsk', R') ∈ rt_bounds → R' ≤ task_deadline tsk' :=
        fun tsk' R' h_in => edf_claimed_bounds_le_deadline task_cost task_period task_deadline num_cpus ts rt_bounds tsk' R' h h_in
      exact Prosa.Classic.Analysis.Global.Parallel.Bertogna_edf_theory.ResponseTimeAnalysisEDF.bertogna_cirinei_response_time_bound_edf
        task_cost task_period task_deadline job_arrival job_cost job_deadline job_task arr_seq
        H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
        H_all_jobs_from_taskset sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu
        H_work_conserving H_edf_policy rt_bounds h_unzip h_fixed' h_dl tsk R IN
    | none =>
      rw [h] at IN
      exact absurd IN id

variable (H_test_succeeds :
  edf_schedulable task_cost task_period task_deadline num_cpus ts)

include H_valid_task_parameters H_constrained_deadlines
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks H_at_least_one_cpu
  H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_work_conserving H_edf_policy H_test_succeeds in
theorem taskset_schedulable_by_edf_rta :
    ∀ tsk, tsk ∈ ts →
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
    sorry
include H_valid_task_parameters H_constrained_deadlines
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks H_at_least_one_cpu
  H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_work_conserving H_edf_policy H_test_succeeds in
theorem jobs_schedulable_by_edf_rta :
    ∀ j, arrives_in arr_seq j →
      job_misses_no_deadline job_arrival job_cost job_deadline sched j := by
    intro j ARRj
    have := @taskset_schedulable_by_edf_rta sporadic_task _ task_cost task_period task_deadline Job _ job_arrival job_cost job_deadline job_task ts H_valid_task_parameters H_constrained_deadlines arr_seq H_all_jobs_from_taskset H_valid_job_parameters H_sporadic_tasks (num_cpus := num_cpus) sched H_at_least_one_cpu H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_edf_policy H_test_succeeds (job_task j) (H_all_jobs_from_taskset j ARRj)
    exact this j ARRj rfl

end MainProof

end Analysis

end ResponseTimeIterationEDF

end Prosa.Classic.Analysis.Global.Parallel.Bertogna_edf_comp
