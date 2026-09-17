-- Translated from: ../rt-proofs/classic/analysis/global/jitter/bertogna_edf_comp.v
import Prosa.Classic.Util.All
import Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_theory
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_comp

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Jitter.Job
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines
open Prosa.Classic.Model.Schedule.Global.Jitter.Interference_edf
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_theory.ResponseTimeAnalysisEDFJitter
open Prosa.Classic.Analysis.Global.Jitter.Workload_bound.WorkloadBoundJitter
open Prosa.Util.Div_mod
open Prosa.Classic.Util.Fixedpoint

attribute [local instance] Classical.propDecidable

namespace ResponseTimeIterationEDF

section Analysis

variable {sporadic_task : Type} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable (task_jitter : sporadic_task → Time)

abbrev task_with_response_time (sporadic_task : Type) := (sporadic_task × Time)

variable {Job : Type} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)
variable (job_jitter : Job → Time)

variable (num_cpus : ℕ)
private noncomputable abbrev I (rt_bounds : List (sporadic_task × Time))
    (tsk : sporadic_task) (delta : Time) : ℕ :=
  total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds delta

noncomputable def edf_response_time_bound (rt_bounds : List (sporadic_task × Time))
    (tsk : sporadic_task) (delta : Time) : Time :=
  task_cost tsk + div_floor (total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds delta) num_cpus

def jitter_plus_R_le_deadline (pair : sporadic_task × Time) : Bool :=
  decide (task_jitter pair.1 + pair.2 ≤ task_deadline pair.1)

noncomputable def update_bound (rt_bounds : List (sporadic_task × Time))
    (pair : sporadic_task × Time) : sporadic_task × Time :=
  (pair.1, edf_response_time_bound task_cost task_period task_deadline task_jitter num_cpus rt_bounds pair.1 pair.2)

private def initial_state (ts : List sporadic_task) : List (sporadic_task × Time) :=
  ts.map (fun t => (t, task_cost t))

noncomputable def edf_rta_iteration (rt_bounds : List (sporadic_task × Time)) :
    List (sporadic_task × Time) :=
  rt_bounds.map (update_bound task_cost task_period task_deadline task_jitter num_cpus rt_bounds)

private def max_steps (ts : List sporadic_task) : ℕ :=
  (ts.map (fun tsk => task_deadline tsk - task_cost tsk)).sum + 1

noncomputable def edf_claimed_bounds (ts : List sporadic_task) :
    Option (List (sporadic_task × Time)) :=
  let R_values := (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus)^[max_steps task_deadline task_cost ts]
                    (initial_state task_cost ts)
  if R_values.all (jitter_plus_R_le_deadline task_deadline task_jitter) then
    some R_values
  else none

def edf_schedulable (ts : List sporadic_task) : Prop :=
  edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts ≠ none

section SimpleLemmas

theorem edf_claimed_bounds_unzip1_update_bound :
    ∀ (l rt_bounds : List (sporadic_task × Time)),
      (l.map (update_bound task_cost task_period task_deadline task_jitter num_cpus rt_bounds)).map Prod.fst =
        l.map Prod.fst := by
  intro l rt_bounds
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨by simp [update_bound], ih⟩

theorem edf_claimed_bounds_unzip1_iteration :
    ∀ (l : List sporadic_task) (k : ℕ),
      ((edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus)^[k]
        (initial_state task_cost l)).map Prod.fst = l := by
  intro l k
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id]
    unfold initial_state
    simp [List.map_map, Function.comp_def]
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp]
    unfold edf_rta_iteration
    rw [edf_claimed_bounds_unzip1_update_bound]
    exact ih

theorem edf_claimed_bounds_size :
    ∀ (l : List sporadic_task) (k : ℕ),
      ((edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus)^[k]
        (initial_state task_cost l)).length = l.length := by
  intro l k
  have h := edf_claimed_bounds_unzip1_iteration task_cost task_period task_deadline task_jitter num_cpus l k
  have : (((edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus)^[k]
        (initial_state task_cost l)).map Prod.fst).length = l.length := by rw [h]
  rwa [List.length_map] at this

theorem edf_claimed_bounds_ge_cost :
    ∀ (l : List sporadic_task) (k : ℕ) (tsk : sporadic_task) (R : Time),
      (tsk, R) ∈ (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus)^[k]
        (initial_state task_cost l) →
      R ≤ task_cost tsk := by
    sorry
theorem edf_claimed_bounds_le_deadline :
    ∀ (ts : List sporadic_task) (rt_bounds : List (sporadic_task × Time))
      (tsk : sporadic_task) (R : Time),
      edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some rt_bounds →
      (tsk, R) ∈ rt_bounds →
      task_jitter tsk + R ≤ task_deadline tsk := by
  intro ts rt_bounds tsk R SOME PAIR
  simp only [edf_claimed_bounds] at SOME
  split_ifs at SOME with h
  · have heq := Option.some.inj SOME
    rw [← heq] at PAIR
    have hall := List.all_eq_true.mp h
    have hmem := hall (tsk, R) PAIR
    simp [jitter_plus_R_le_deadline] at hmem
    exact hmem

theorem edf_claimed_bounds_has_R_for_every_task :
    ∀ (ts : List sporadic_task) (rt_bounds : List (sporadic_task × Time))
      (tsk : sporadic_task),
      edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some rt_bounds →
      tsk ∈ ts →
      ∀ R, (tsk, R) ∈ rt_bounds := by
    sorry
end SimpleLemmas

section MonotonicityOfInterferenceBound

variable (tsk tsk_other : sporadic_task)
variable (H_period_positive : task_period tsk_other > 0)

variable (delta delta' R R' : Time)
variable (H_delta_monotonic : delta ≤ delta')
variable (H_response_time_monotonic : R ≤ R')
variable (H_cost_le_rt_bound : task_cost tsk_other ≤ R)

include H_period_positive H_delta_monotonic H_response_time_monotonic H_cost_le_rt_bound in
theorem interference_bound_edf_monotonic :
    interference_bound_edf task_cost task_period task_deadline task_jitter tsk delta (tsk_other, R) ≤
    interference_bound_edf task_cost task_period task_deadline task_jitter tsk delta' (tsk_other, R') := by
    sorry
end MonotonicityOfInterferenceBound

section Convergence

variable (ts : List sporadic_task)
variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)

private noncomputable abbrev f (k : ℕ) : List (sporadic_task × Time) :=
  (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus)^[k]
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
  unfold all_le
  refine ⟨rfl, fun p hp => ?_⟩
  induction l with
  | nil => simp [List.zip] at hp
  | cons hd tl ih =>
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Nat.le_refl _
    · exact ih hp

include H_valid_task_parameters in
theorem all_le_transitive :
    ∀ x y z : List (sporadic_task × Time),
      all_le x y → all_le y z → all_le x z := by
  intro x y z hxy hyz
  unfold all_le at *
  obtain ⟨hfst_xy, hle_xy⟩:= hxy
  obtain ⟨hfst_yz, hle_yz⟩:= hyz
  refine ⟨by rw [hfst_xy, hfst_yz], fun p hp => ?_⟩
  have hlen_xy : x.length = y.length := by
    have := congr_arg List.length hfst_xy; simp [List.length_map] at this; exact this
  have hlen_yz : y.length = z.length := by
    have := congr_arg List.length hfst_yz; simp [List.length_map] at this; exact this
  rw [List.mem_iff_getElem] at hp
  obtain ⟨i, hi, heq⟩:= hp
  have hi_x : i < x.length := by simp [List.length_zip] at hi; omega
  have hi_y : i < y.length := by omega
  have hi_z : i < z.length := by omega
  rw [show (x.zip z)[i] = (x[i], z[i]) from List.getElem_zip] at heq
  rw [← heq]; simp only
  have hle1 : x[i].2 ≤ y[i].2 := by
    have hmem : (x[i], y[i]) ∈ x.zip y := by
      rw [List.mem_iff_getElem]
      refine ⟨i, by simp [List.length_zip]; omega, ?_⟩
      exact List.getElem_zip
    exact hle_xy _ hmem
  have hle2 : y[i].2 ≤ z[i].2 := by
    have hmem : (y[i], z[i]) ∈ y.zip z := by
      rw [List.mem_iff_getElem]
      refine ⟨i, by simp [List.length_zip]; omega, ?_⟩
      exact List.getElem_zip
    exact hle_yz _ hmem
  exact Nat.le_trans hle1 hle2

include H_valid_task_parameters in
theorem bertogna_edf_comp_iteration_preserves_minimum :
    ∀ step,
      all_le (initial_state task_cost ts)
        (f task_cost task_period task_deadline task_jitter num_cpus ts step) := by
    sorry
include H_valid_task_parameters in
theorem bertogna_edf_comp_iteration_inductive (P : List (sporadic_task × Time) → Prop) :
    P (initial_state task_cost ts) →
    (∀ k, P (f task_cost task_period task_deadline task_jitter num_cpus ts k) →
      P (f task_cost task_period task_deadline task_jitter num_cpus ts (k + 1))) →
    P (f task_cost task_period task_deadline task_jitter num_cpus ts (max_steps task_deadline task_cost ts)) := by
  intro P0 Pn
  induction (max_steps task_deadline task_cost ts) with
  | zero => exact P0
  | succ n ih => exact Pn n ih

include H_valid_task_parameters in
theorem bertogna_edf_comp_iteration_preserves_order :
    ∀ l1 l2 : List (sporadic_task × Time),
      all_le (initial_state task_cost ts) l1 →
      all_le l1 l2 →
      all_le (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus l1)
        (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus l2) := by
  intro l1 l2 LEinit LE
  obtain ⟨hfst_le, hle⟩:= LE
  have hlen1 : l1.length = l2.length := by
    have := congr_arg List.length hfst_le; simp [List.length_map] at this; exact this
  unfold all_le
  constructor
  · -- tasks preserved by iteration
    unfold edf_rta_iteration
    rw [edf_claimed_bounds_unzip1_update_bound, edf_claimed_bounds_unzip1_update_bound, hfst_le]
  · -- R values
    intro p hp
    unfold edf_rta_iteration at hp
    set m1 := l1.map (update_bound task_cost task_period task_deadline task_jitter num_cpus l1) with hm1_def
    set m2 := l2.map (update_bound task_cost task_period task_deadline task_jitter num_cpus l2) with hm2_def
    rw [List.mem_iff_getElem] at hp
    obtain ⟨i, hi_zip, heq⟩:= hp
    have hlen_m1 : m1.length = l1.length := by simp [hm1_def]
    have hlen_m2 : m2.length = l2.length := by simp [hm2_def]
    have hi : i < l2.length := by
      rw [List.length_zip, hlen_m1, hlen_m2, hlen1, Nat.min_self] at hi_zip; exact hi_zip
    have hi1 : i < l1.length := by omega
    have hi_m1 : i < m1.length := by omega
    have hi_m2 : i < m2.length := by omega
    have hi_l1 : i < l1.length := by rw [← hlen_m1]; exact hi_m1
    have hi_l2 : i < l2.length := hi
    rw [show (m1.zip m2)[i]'(by rw [List.length_zip]; omega) = (m1[i]'hi_m1, m2[i]'hi_m2) from List.getElem_zip] at heq
    rw [← heq]; simp only
    simp only [hm1_def, hm2_def, List.getElem_map]
    -- Need: (update_bound ... l1 l1[i]).2 ≤(update_bound ... l2 l2[i]).2
    unfold update_bound edf_response_time_bound
    simp only
    have hfst_i : (l1[i]'hi_l1).1 = (l2[i]'hi_l2).1 := by
      have : (l1.map Prod.fst)[i]? = (l2.map Prod.fst)[i]? := by rw [hfst_le]
      simp [hi_l1, hi_l2] at this
      exact this
    rw [hfst_i]
    apply Nat.add_le_add_left
    unfold div_floor
    apply Nat.div_le_div_right
    -- total_interference_bound_edf monotonic
    -- Need to show the sum over filtered+mapped elements is ≤
    have hle_i : (l1[i]'hi_l1).2 ≤ (l2[i]'hi_l2).2 := by
      have hmem : ((l1[i]'hi_l1), (l2[i]'hi_l2)) ∈ l1.zip l2 := by
        rw [List.mem_iff_getElem]
        exact ⟨i, by simp [List.length_zip]; omega, List.getElem_zip⟩
      exact hle _ hmem
    have GE_COST : ∀ q, q ∈ l1 → task_cost q.1 ≤ q.2 := by
      obtain ⟨hfst_init, hle_init⟩:= LEinit
      intro q hq; rw [List.mem_iff_getElem] at hq; obtain ⟨j, hj, hget_j⟩:= hq
      have hlen_init : (initial_state task_cost ts).length = l1.length := by
        have h := congrArg List.length hfst_init; rw [List.length_map, List.length_map] at h; exact h
      have hj_init : j < (initial_state task_cost ts).length := by omega
      have hmz : ((initial_state task_cost ts)[j]'hj_init, l1[j]) ∈ (initial_state task_cost ts).zip l1 := by
        rw [List.mem_iff_getElem]; exact ⟨j, by rw [List.length_zip]; omega, List.getElem_zip⟩
      have hle_j := hle_init _ hmz; simp at hle_j
      have hinit_eq : (initial_state task_cost ts)[j]'hj_init = (l1[j].1, task_cost l1[j].1) := by
        have hfm : ((initial_state task_cost ts).map Prod.fst)[j]'(by simp; exact hj_init) =
            (l1.map Prod.fst)[j]'(by simp; exact hj) := by congr 1
        simp [initial_state, List.getElem_map] at hfm
        simp [initial_state, List.getElem_map] at *
        exact ⟨hfm, by rw [hfm]⟩
      rw [hinit_eq] at hle_j; simp at hle_j; rw [← hget_j]; simpa
    have VALID' : ∀ tsk', tsk' ∈ l1.map Prod.fst → is_valid_sporadic_task task_cost task_period task_deadline tsk' := by
      obtain ⟨hfst_init, _⟩:= LEinit; intro tsk' hmem
      have : tsk' ∈ (initial_state task_cost ts).map Prod.fst := by rw [hfst_init]; exact hmem
      simp [initial_state, List.map_map, Function.comp] at this
      exact H_valid_task_parameters tsk' this
    unfold total_interference_bound_edf
    suffices hsuff : ∀ (a b : List (sporadic_task × Time)),
        a.map Prod.fst = b.map Prod.fst → (∀ q, q ∈ a.zip b → q.1.2 ≤ q.2.2) →
        (∀ q, q ∈ a → task_cost q.1 ≤ q.2) →
        (∀ tsk', tsk' ∈ a.map Prod.fst → is_valid_sporadic_task task_cost task_period task_deadline tsk') →
        ∀ (tsk0 : sporadic_task) (d1 d2 : Time), d1 ≤ d2 →
        ((a.filter (fun q => different_task tsk0 q.1)).map (fun tsk_R => interference_bound_edf task_cost task_period task_deadline task_jitter tsk0 d1 tsk_R)).sum ≤
        ((b.filter (fun q => different_task tsk0 q.1)).map (fun tsk_R => interference_bound_edf task_cost task_period task_deadline task_jitter tsk0 d2 tsk_R)).sum by
      exact hsuff l1 l2 hfst_le hle GE_COST VALID' _ _ _ hle_i
    intro a b hfst_ab hle_ab hge_cost hvalid tsk0 d1 d2 hd
    induction a generalizing b with
    | nil => simp
    | cons ahd atl iha =>
      match b with
      | [] => simp at hfst_ab
      | bhd :: btl =>
        simp only [List.map_cons, List.cons.injEq] at hfst_ab
        obtain ⟨hfst_hd, hfst_tl⟩:= hfst_ab
        have hle_hd : ahd.2 ≤ bhd.2 := by
          have := hle_ab (ahd, bhd) (by simp [List.zip_cons_cons]); simpa using this
        have hle_tl : ∀ q, q ∈ atl.zip btl → q.1.2 ≤ q.2.2 :=
          fun q hq => hle_ab q (by simp [List.zip_cons_cons]; exact Or.inr hq)
        have hge_tl : ∀ q, q ∈ atl → task_cost q.1 ≤ q.2 :=
          fun q hq => hge_cost q (List.mem_cons_of_mem ahd hq)
        have hv_tl : ∀ tsk', tsk' ∈ atl.map Prod.fst → is_valid_sporadic_task task_cost task_period task_deadline tsk' :=
          fun tsk' h => hvalid tsk' (List.mem_cons_of_mem _ h)
        simp only [List.filter_cons]
        have hdiff_eq : (different_task tsk0 ahd.1) = (different_task tsk0 bhd.1) := by
          unfold different_task; rw [hfst_hd]
        split
        · -- different_task tsk0 ahd.1 = true case
          rename_i hdf
          rw [hdiff_eq] at hdf; simp [hdf, List.map_cons, List.sum_cons]
          apply Nat.add_le_add
          · conv_lhs => rw [show ahd = (ahd.1, ahd.2) from Prod.eta ahd]
            conv_rhs => rw [show bhd = (bhd.1, bhd.2) from Prod.eta bhd]
            rw [← hfst_hd]
            have hmem_ahd : ahd ∈ ahd :: atl := by simp
            have hmem_fst : ahd.1 ∈ (ahd :: atl).map Prod.fst := by simp
            exact interference_bound_edf_monotonic task_cost task_period task_deadline task_jitter tsk0 ahd.1
              (hvalid ahd.1 hmem_fst).2.1
              d1 d2 ahd.2 bhd.2 hd hle_hd (hge_cost ahd hmem_ahd)
          · exact iha btl hfst_tl hle_tl hge_tl hv_tl
        · -- different_task tsk0 ahd.1 = false case
          rename_i hdf
          rw [hdiff_eq] at hdf; simp [hdf]
          exact iha btl hfst_tl hle_tl hge_tl hv_tl
include H_valid_task_parameters in
theorem bertogna_edf_comp_iteration_monotonic :
    ∀ k, all_le (f task_cost task_period task_deadline task_jitter num_cpus ts k)
      (f task_cost task_period task_deadline task_jitter num_cpus ts (k + 1)) := by
  intro k
  simp only [f]
  apply fun_mon_iter_mon_generic _ (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) all_le (initial_state task_cost ts) k (k + 1)
  · exact all_le_reflexive task_cost task_period task_deadline ts H_valid_task_parameters
  · exact all_le_transitive task_cost task_period task_deadline ts H_valid_task_parameters
  · omega
  · intro x1 x2 h1 h2
    exact bertogna_edf_comp_iteration_preserves_order task_cost task_period task_deadline task_jitter num_cpus ts H_valid_task_parameters x1 x2 h1 h2
  · exact bertogna_edf_comp_iteration_preserves_minimum task_cost task_period task_deadline task_jitter num_cpus ts H_valid_task_parameters

end RelationProperties

theorem bertogna_edf_comp_f_converges_with_no_tasks :
    ts.length = 0 →
    f task_cost task_period task_deadline task_jitter num_cpus ts (max_steps task_deadline task_cost ts) =
      f task_cost task_period task_deadline task_jitter num_cpus ts (max_steps task_deadline task_cost ts + 1) := by
  intro hlen
  have hnil : ts = [] := List.eq_nil_of_length_eq_zero hlen
  subst hnil
  simp only [f, max_steps, List.map_nil, List.sum_nil]
  simp only [initial_state, List.map_nil]
  unfold edf_rta_iteration
  simp

theorem bertogna_edf_comp_f_converges_early :
    (∀ k, k ≤ max_steps task_deadline task_cost ts ∧
      f task_cost task_period task_deadline task_jitter num_cpus ts k =
        f task_cost task_period task_deadline task_jitter num_cpus ts (k + 1)) →
    f task_cost task_period task_deadline task_jitter num_cpus ts (max_steps task_deadline task_cost ts) =
      f task_cost task_period task_deadline task_jitter num_cpus ts (max_steps task_deadline task_cost ts + 1) := by
    sorry
section DerivingContradiction

variable (H_at_least_one_task : ts.length > 0)
variable (H_keeps_diverging :
  ∀ k, k ≤ max_steps task_deadline task_cost ts →
    f task_cost task_period task_deadline task_jitter num_cpus ts k ≠
      f task_cost task_period task_deadline task_jitter num_cpus ts (k + 1))

include H_valid_task_parameters H_at_least_one_task H_keeps_diverging in
theorem bertogna_edf_comp_f_increases :
    ∀ k, k ≤ max_steps task_deadline task_cost ts →
      one_lt (f task_cost task_period task_deadline task_jitter num_cpus ts k)
        (f task_cost task_period task_deadline task_jitter num_cpus ts (k + 1)) := by
  intro k hk
  unfold one_lt
  set fk := f task_cost task_period task_deadline task_jitter num_cpus ts k with hfk_def
  set fk1 := f task_cost task_period task_deadline task_jitter num_cpus ts (k + 1) with hfk1_def
  have hMONO := bertogna_edf_comp_iteration_monotonic task_cost task_period task_deadline task_jitter num_cpus ts H_valid_task_parameters k
  obtain ⟨hfst_eq, hle⟩:= hMONO
  constructor
  · -- tasks are the same
    exact hfst_eq
  · -- there exists a strictly increasing element
    by_contra h_all_le
    push_neg at h_all_le
    -- If no element strictly increases, then all are ≤and none are <, so all are =
    have hDIFF := H_keeps_diverging k hk
    apply hDIFF
    -- Show fk = fk1
    have hlen_eq : fk.length = fk1.length := by
      have := congr_arg List.length hfst_eq; simp [List.length_map] at this; exact this
    apply List.ext_getElem hlen_eq
    intro i hi1 hi2
    have hmem : (fk[i], fk1[i]) ∈ fk.zip fk1 := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp [List.length_zip]; omega, List.getElem_zip⟩
    have hle_i := hle _ hmem
    -- Also need to show fk1[i].2 ≤fk[i].2
    have hge_i : fk1[i].2 ≤ fk[i].2 := by
      exact h_all_le _ hmem
    have heq_snd : fk[i].2 = fk1[i].2 := Nat.le_antisymm hle_i hge_i
    -- Also need first components equal
    have hfst_i : fk[i].1 = fk1[i].1 := by
      have : (fk.map Prod.fst)[i]? = (fk1.map Prod.fst)[i]? := by rw [hfst_eq]
      simp [List.getElem?_eq_getElem, hi1, hi2] at this
      exact this
    exact Prod.ext hfst_i heq_snd

include H_valid_task_parameters H_at_least_one_task H_keeps_diverging in
theorem bertogna_edf_comp_rt_grows_too_much :
    ∀ k, k ≤ max_steps task_deadline task_cost ts →
      ((f task_cost task_period task_deadline task_jitter num_cpus ts k).map
        (fun p => p.2 - task_cost p.1)).sum + 1 > k := by sorry

end DerivingContradiction

include H_valid_task_parameters in
theorem edf_claimed_bounds_finds_fixed_point_of_list :
    ∀ rt_bounds : List (sporadic_task × Time),
      edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some rt_bounds →
      valid_sporadic_taskset task_cost task_period task_deadline ts →
      f task_cost task_period task_deadline task_jitter num_cpus ts (max_steps task_deadline task_cost ts) =
        edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus
          (f task_cost task_period task_deadline task_jitter num_cpus ts (max_steps task_deadline task_cost ts)) := by
  sorry

include H_valid_task_parameters in
theorem edf_claimed_bounds_finds_least_fixed_point :
    ∀ v : List (sporadic_task × Time),
      all_le (initial_state task_cost ts) v →
      v = edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus v →
      all_le (f task_cost task_period task_deadline task_jitter num_cpus ts (max_steps task_deadline task_cost ts)) v := by
  intro v hge0 heq
  apply bertogna_edf_comp_iteration_inductive task_cost task_period task_deadline task_jitter num_cpus ts H_valid_task_parameters (P := fun l => all_le l v)
  · exact hge0
  · intro k hk
    have hord := bertogna_edf_comp_iteration_preserves_order task_cost task_period task_deadline task_jitter num_cpus ts H_valid_task_parameters
      (f task_cost task_period task_deadline task_jitter num_cpus ts k) v
      (bertogna_edf_comp_iteration_preserves_minimum task_cost task_period task_deadline task_jitter num_cpus ts H_valid_task_parameters k) hk
    have hfk1 : f task_cost task_period task_deadline task_jitter num_cpus ts (k + 1) =
      edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus (f task_cost task_period task_deadline task_jitter num_cpus ts k) := by
      simp only [f, Function.iterate_succ', Function.comp]
    rw [hfk1, heq]
    exact hord

include H_valid_task_parameters in
theorem edf_claimed_bounds_finds_fixed_point_for_each_bound :
    ∀ (tsk : sporadic_task) (R : Time) (rt_bounds : List (sporadic_task × Time)),
      edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some rt_bounds →
      (tsk, R) ∈ rt_bounds →
      R = edf_response_time_bound task_cost task_period task_deadline task_jitter num_cpus rt_bounds tsk R := by sorry

include H_valid_task_parameters in
theorem edf_claimed_bounds_converges :
    ∀ (tsk : sporadic_task) (R : Time) (rt_bounds : List (sporadic_task × Time)),
      edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some rt_bounds →
      (tsk, R) ∈ rt_bounds →
      R = task_cost tsk + div_floor (total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds R) num_cpus := by
  intro tsk R rt_bounds SOME IN
  have := edf_claimed_bounds_finds_fixed_point_for_each_bound task_cost task_period task_deadline task_jitter num_cpus ts H_valid_task_parameters tsk R rt_bounds SOME IN
  rw [edf_response_time_bound] at this
  exact this

end Convergence

section MainProof

variable (ts : List sporadic_task)

variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)

variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable {arr_seq : arrival_sequence Job}

variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (H_valid_job_parameters :
  ∀ j,
    arrives_in arr_seq j →
    valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost
                                   job_deadline job_task job_jitter j)

variable (H_sporadic_tasks :
  Prosa.Classic.Model.Arrival.Basic.Task_arrival.sporadic_task_model task_period job_arrival job_task arr_seq)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (H_at_least_one_cpu : num_cpus > 0)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_execute_after_jitter :
  ScheduleWithJitter.jobs_execute_after_jitter job_arrival job_jitter sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_sequential_jobs : sequential_jobs sched)

variable (H_work_conserving :
  Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines.work_conserving
    job_arrival job_cost job_jitter arr_seq sched)
variable (H_edf_policy :
  Prosa.Classic.Model.Schedule.Global.Jitter.Interference_edf.InterferenceEDF.respects_JLFP_policy_edf
    job_arrival job_cost job_jitter arr_seq sched
    (EDF job_arrival job_deadline))

private abbrev no_deadline_missed_by_task_def (tsk : sporadic_task) :=
  task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

private abbrev no_deadline_missed_by_job_def :=
  job_misses_no_deadline job_arrival job_cost job_deadline sched

private abbrev response_time_bounded_by_def (tsk : sporadic_task) :=
  is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk

include H_valid_task_parameters H_constrained_deadlines
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks H_at_least_one_cpu
  H_jobs_come_from_arrival_sequence
  H_jobs_execute_after_jitter H_completed_jobs_dont_execute
  H_sequential_jobs H_work_conserving H_edf_policy in
theorem edf_analysis_yields_response_time_bounds :
    ∀ (tsk : sporadic_task) (R : Time),
      (match edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts with
       | some rt_bounds => (tsk, R) ∈ rt_bounds
       | none => False) →
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (task_jitter tsk + R) := by
    sorry
variable (H_test_succeeds :
  edf_schedulable task_cost task_period task_deadline task_jitter num_cpus ts)

include H_valid_task_parameters H_constrained_deadlines
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks H_at_least_one_cpu
  H_jobs_come_from_arrival_sequence
  H_jobs_execute_after_jitter H_completed_jobs_dont_execute
  H_sequential_jobs H_work_conserving H_edf_policy H_test_succeeds in
theorem taskset_schedulable_by_edf_rta :
    ∀ tsk, tsk ∈ ts →
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
    sorry
include H_valid_task_parameters H_constrained_deadlines
  H_all_jobs_from_taskset H_valid_job_parameters
  H_sporadic_tasks H_at_least_one_cpu
  H_jobs_come_from_arrival_sequence
  H_jobs_execute_after_jitter H_completed_jobs_dont_execute
  H_sequential_jobs H_work_conserving H_edf_policy H_test_succeeds in
theorem jobs_schedulable_by_edf_rta :
    ∀ j, arrives_in arr_seq j →
      job_misses_no_deadline job_arrival job_cost job_deadline sched j := by
  intro j ARRj
  have SCHED := @taskset_schedulable_by_edf_rta sporadic_task _ task_cost task_period task_deadline task_jitter Job _ job_arrival job_cost job_deadline job_task job_jitter ts H_valid_task_parameters H_constrained_deadlines arr_seq H_all_jobs_from_taskset H_valid_job_parameters H_sporadic_tasks num_cpus sched H_at_least_one_cpu H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving H_edf_policy H_test_succeeds
  exact SCHED (job_task j) (H_all_jobs_from_taskset j ARRj) j ARRj rfl

end MainProof

end Analysis

end ResponseTimeIterationEDF

end Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_comp
