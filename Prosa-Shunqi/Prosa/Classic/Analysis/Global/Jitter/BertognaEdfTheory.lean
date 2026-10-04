-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/jitter/bertogna_edf_theory.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 172)

import Prosa.Util.Sum
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Global.Jitter.Platform
import Prosa.Classic.Model.Schedule.Global.Jitter.Interference
import Prosa.Classic.Model.Schedule.Global.Jitter.ConstrainedDeadlines
import Prosa.Classic.Analysis.Global.Jitter.WorkloadBound
import Prosa.Classic.Analysis.Global.Jitter.InterferenceBoundEdf

/-!
Bertogna and Cirinei's response-time analysis for global EDF scheduling with release jitter (Rocq module
`ResponseTimeAnalysisEDFJitter` of `classic/analysis/global/jitter/bertogna_edf_theory.v`): for any fixed point `R`
in `rt_bounds`, `task_jitter tsk + R` is a safe response-time bound.

Representation notes (as in the accepted `classic/analysis/global/basic/bertogna_edf_theory.v` translation):
* The section-local `Let`s are unfolded in the statements: `t1` is `job_arrival j + job_jitter j`; `I tsk delta` is
  `total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds delta`; `x tsk_other` is
  the jitter-aware `task_interference job_arrival job_cost job_task job_jitter sched j tsk_other t1 (t1 + R)`; `X` is
  `total_interference job_arrival job_cost job_jitter sched j t1 (t1 + R)`; `workload_bound`, `edf_specific_bound`
  and `interference_bound` are `W_jitter …`, `edf_specific_interference_bound … task_jitter tsk …` and
  `interference_bound_edf … task_jitter tsk R (tsk_other, R_other)`; `other_task` is `different_task tsk`,
  `other_tasks` is `ts.val.filter (fun tsk_other => different_task tsk tsk_other)`, `other_scheduled_task t` is
  `fun tsk_other => task_is_scheduled job_task sched tsk_other t && different_task tsk tsk_other`,
  `num_tasks_exceeding delta` is `other_tasks.countP (fun i => decide (delta ≤ x i))` and `response_time_bounded_by`
  is `is_response_time_bound_of_task … sched`.
* `unzip1 rt_bounds = ts` is `rt_bounds.map Prod.fst = ts.val`; `count P s` is `s.countP P`; `\sum_(i <- s) F i` is
  `Prosa.Util.Sum.sumSeq s F`, `\sum_(i <- s | P i) F i` is `Prosa.Util.Sum.sumFiltered s P F`, and
  `\sum_((tsk_other, R_other) <- s | P) F` binds the pair by pattern matching; `minn` is `min`; Boolean chains
  `a <= b < c` in proposition position are `(decide (a ≤ b) && decide (b < c)) = true`; `x != y` in proposition
  position is `(!decide (x = y)) = true`.
* `backlogged`, `pending` and `task_scheduled_on`/`task_is_scheduled` are the jitter-aware versions, as exported by
  the Rocq module.
* Binder lists follow the Rocq contract. The proofs follow the accepted basic translation; the LEAN_HELPER lemmas
  `countP_eq_sum_toNat`, `sum_min_split`, `interference_in_non_full_processors_core` and `mem_ts_iff_bound` are copied
  from it (they are private there), and `job_jitter_le` is copied from the jitter FP translation. The main theorem is
  proved, as in Rocq, by strong induction on the absolute response-time bound `job_arrival j + task_jitter tsk + R`.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Global.Jitter.BertognaEdfTheory.ResponseTimeAnalysisEDFJitter

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule hiding pending backlogged scheduled_implies_pending
open Prosa.Classic.Model.Schedule.Global.Jitter.Job.JobWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Jitter.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Jitter.Interference.Interference
open Prosa.Classic.Model.Schedule.Global.Jitter.ConstrainedDeadlines.ConstrainedDeadlines
open Prosa.Classic.Analysis.Global.Jitter.WorkloadBound.WorkloadBoundJitter
open Prosa.Classic.Analysis.Global.Jitter.InterferenceBoundEdf.InterferenceBoundEDFJitter
open Prosa.Classic.Util.DivMod (div_floor ltn_div_trunc)
open Prosa.Classic.Util.Counting (count_or sub_in_count)
open Prosa.Util.Sum (sumSeq sumFiltered)
open BigOperators

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### LEAN_HELPER lemmas -/

/-- LEAN_HELPER: counting as a sum of indicators. -/
private theorem countP_eq_sum_toNat {K : Type _} (L : List K) (f : K → Bool) :
    L.countP f = (L.map (fun k => (f k).toNat)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
      cases f a <;> simp [Nat.add_comm]

/-- LEAN_HELPER: splitting a sum of minima at a threshold. -/
private theorem sum_min_split {K : Type _} (L : List K) (f : K → Nat) (δ : Nat) :
    sumSeq L (fun k => min (f k) δ) =
      δ * L.countP (fun k => decide (δ ≤ f k)) + sumFiltered L (fun k => decide (f k < δ)) f := by
  unfold sumSeq sumFiltered
  induction L with
  | nil => simp
  | cons a L ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons, List.filter_cons]
      by_cases h : δ ≤ f a
      · have h' : ¬ f a < δ := by omega'
        simp only [h, h', decide_true, decide_false, ↓reduceIte, Bool.false_eq_true,
          min_eq_right h]
        rw [Nat.mul_add, Nat.mul_one]
        omega'
      · have h' : f a < δ := by omega'
        simp only [h, h', decide_true, decide_false, ↓reduceIte, Bool.false_eq_true,
          min_eq_left (Nat.le_of_lt h'), List.map_cons, List.sum_cons, Nat.add_zero]
        omega'

/-- LEAN_HELPER: the combinatorial core of lemma (4).  `b t` says whether the analyzed
job is backlogged at `t`, `tso k cpu t` whether task `k` is scheduled on `cpu` at `t`,
and `x k` is the interference caused by task `k`; at each backlogged time every
processor of a set of `c` processors runs a task of `H` (`busy`), and a task of `H`
runs on at most one processor at a time (`uniq`). -/
private theorem interference_in_non_full_processors_core {K : Type u} [DecidableEq K]
    {m : Nat} (T : Finset Nat) (b : Nat → Bool) (tso : K → Fin m → Nat → Bool) (x : K → Nat)
    (hx : ∀ k, x k = ∑ t ∈ T, ∑ cpu : Fin m, (b t && tso k cpu t).toNat)
    (H : List K) (hnd : H.Nodup)
    (uniq : ∀ k ∈ H, ∀ t ∈ T, b t = true →
      ∀ c1 c2, tso k c1 t = true → tso k c2 t = true → c1 = c2)
    (c : Nat)
    (busy : ∀ t ∈ T, b t = true →
      c ≤ H.countP (fun k => (List.finRange m).any (fun cc => tso k cc t)))
    (δ : Nat) (hN : 0 < H.countP (fun k => decide (δ ≤ x k)))
    (hNm : H.countP (fun k => decide (δ ≤ x k)) < c) :
    δ * (c - H.countP (fun k => decide (δ ≤ x k))) ≤
      sumFiltered H (fun k => decide (x k < δ)) x := by
  have hFnd : (H.filter (fun k => decide (x k < δ))).Nodup := hnd.filter _
  -- (a) some task of `H` causes at least `δ` interference, which is bounded by the
  -- number of backlogged times at which a task exceeding `δ` runs.
  obtain ⟨ka, hka, hδ⟩ : ∃ ka ∈ H, δ ≤ x ka := by
    obtain ⟨ka, h1, h2⟩ := List.countP_pos_iff.mp hN
    exact ⟨ka, h1, by simpa using h2⟩
  have step1 : δ ≤ ∑ t ∈ T,
      (b t && H.any (fun k => decide (δ ≤ x k) &&
        (List.finRange m).any (fun cc => tso k cc t))).toNat := by
    refine le_trans hδ ?_
    rw [hx]
    apply Finset.sum_le_sum
    intro t ht
    cases hb : b t
    · simp
    · by_cases hs : (List.finRange m).any (fun cc => tso ka cc t) = true
      · have hany : H.any (fun k => decide (δ ≤ x k) &&
            (List.finRange m).any (fun cc => tso k cc t)) = true :=
          List.any_eq_true.mpr ⟨ka, hka, by simp only [hδ, hs, decide_true, Bool.and_self]⟩
        rw [hany]
        simp only [Bool.true_and, Bool.toNat_true]
        have hcard : (∑ cpu : Fin m, (tso ka cpu t).toNat) =
            (Finset.univ.filter (fun c => tso ka c t = true)).card := by
          rw [Finset.card_filter]
          apply Finset.sum_congr rfl
          intro c _
          cases tso ka c t <;> rfl
        rw [hcard]
        apply Finset.card_le_one.mpr
        intro c1 h1 c2 h2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact uniq ka hka t ht hb c1 c2 h1 h2
      · have hnone : ∀ c, tso ka c t = false := by
          intro c
          by_contra hc
          apply hs
          rw [List.any_eq_true]
          exact ⟨c, List.mem_finRange c, by simpa using hc⟩
        simp [hnone]
  -- (b) at such a time at least `m - N` tasks below `δ` run.
  have step2 : ∀ t ∈ T,
      (b t && H.any (fun k => decide (δ ≤ x k) &&
          (List.finRange m).any (fun cc => tso k cc t))).toNat *
        (c - H.countP (fun k => decide (δ ≤ x k))) ≤
      (b t).toNat * ((H.filter (fun k => decide (x k < δ))).map
        (fun k => ((List.finRange m).any (fun cc => tso k cc t)).toNat)).sum := by
    intro t ht
    cases hb : b t
    · simp
    · simp only [Bool.true_and, Bool.toNat_true, Nat.one_mul]
      have hbusy := busy t ht hb
      have hsplit : H.countP (fun k => (List.finRange m).any (fun cc => tso k cc t)) ≤
          H.countP (fun k => decide (δ ≤ x k) && (List.finRange m).any (fun cc => tso k cc t)) +
          H.countP (fun k => decide (x k < δ) && (List.finRange m).any (fun cc => tso k cc t)) := by
        calc H.countP (fun k => (List.finRange m).any (fun cc => tso k cc t))
            = H.countP (fun k =>
                (decide (δ ≤ x k) && (List.finRange m).any (fun cc => tso k cc t)) ||
                (decide (x k < δ) && (List.finRange m).any (fun cc => tso k cc t))) := by
              congr 1
              funext k
              by_cases h : δ ≤ x k
              · have h' : ¬ x k < δ := by omega'
                simp [h, h']
              · have h' : x k < δ := by omega'
                simp [h, h']
          _ ≤ _ := count_or _ H _ _
      have hle : H.countP (fun k => decide (δ ≤ x k) &&
            (List.finRange m).any (fun cc => tso k cc t)) ≤
          H.countP (fun k => decide (δ ≤ x k)) := by
        apply sub_in_count
        intro k _ h
        simp only [Bool.and_eq_true] at h
        exact h.1
      have hF : ((H.filter (fun k => decide (x k < δ))).map
            (fun k => ((List.finRange m).any (fun cc => tso k cc t)).toNat)).sum =
          H.countP (fun k => decide (x k < δ) && (List.finRange m).any (fun cc => tso k cc t)) := by
        rw [← countP_eq_sum_toNat, List.countP_filter]
        congr 1
        funext k
        exact Bool.and_comm _ _
      rw [hF]
      have hA1 := Bool.toNat_le (H.any (fun k => decide (δ ≤ x k) &&
        (List.finRange m).any (fun cc => tso k cc t)))
      have := Nat.mul_le_mul_right (c - H.countP (fun k => decide (δ ≤ x k))) hA1
      omega'
  -- (c) the interference of the tasks below `δ` covers those times.
  have step3 : ∑ t ∈ T, (b t).toNat * ((H.filter (fun k => decide (x k < δ))).map
        (fun k => ((List.finRange m).any (fun cc => tso k cc t)).toNat)).sum ≤
      sumFiltered H (fun k => decide (x k < δ)) x := by
    unfold sumFiltered
    have e1 : ∀ g : K → Nat, ((H.filter (fun k => decide (x k < δ))).map g).sum =
        ∑ k ∈ (H.filter (fun k => decide (x k < δ))).toFinset, g k :=
      fun g => (List.sum_toFinset g hFnd).symm
    simp only [e1, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro k _
    rw [hx k]
    apply Finset.sum_le_sum
    intro t _
    cases hb : b t
    · simp
    · by_cases hs : (List.finRange m).any (fun cc => tso k cc t) = true
      · obtain ⟨c, _, hc⟩ := List.any_eq_true.mp hs
        rw [hs]
        have := Finset.single_le_sum (f := fun cpu => (true && tso k cpu t).toNat)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
        simpa [hc] using this
      · simp only [Bool.not_eq_true] at hs
        simp [hs]
  calc δ * (c - H.countP (fun k => decide (δ ≤ x k)))
      ≤ (∑ t ∈ T, (b t && H.any (fun k => decide (δ ≤ x k) &&
          (List.finRange m).any (fun cc => tso k cc t))).toNat) *
        (c - H.countP (fun k => decide (δ ≤ x k))) := Nat.mul_le_mul_right _ step1
    _ = ∑ t ∈ T, (b t && H.any (fun k => decide (δ ≤ x k) &&
          (List.finRange m).any (fun cc => tso k cc t))).toNat *
        (c - H.countP (fun k => decide (δ ≤ x k))) := Finset.sum_mul _ _ _
    _ ≤ _ := Finset.sum_le_sum step2
    _ ≤ _ := step3


/-- LEAN_HELPER: every task of `rt_bounds` is in the task set, and conversely. -/
private theorem mem_ts_iff_bound {sporadic_task : Type u} [DecidableEq sporadic_task]
    (ts : taskset_of sporadic_task) (rt_bounds : List (sporadic_task × time))
    (H : rt_bounds.map Prod.fst = ts.val) (tsk : sporadic_task) :
    tsk ∈ ts ↔ ∃ R : time, (tsk, R) ∈ rt_bounds := by
  show tsk ∈ ts.val ↔ _
  rw [← H, List.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hmem, rfl⟩
    exact ⟨b, hmem⟩
  · rintro ⟨R, hR⟩
    exact ⟨(tsk, R), hR, rfl⟩

/-- LEAN_HELPER: the jitter of a job of `tsk` is bounded by the task jitter. -/
private theorem job_jitter_le {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (job_jitter : Job → time)
    (j : Job) (tsk : sporadic_task)
    (H : valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (H_job_of_tsk : job_task j = tsk) :
    job_jitter j ≤ task_jitter tsk := by
  have := H.2
  simp only [job_jitter_leq_task_jitter, decide_eq_true_eq] at this
  rw [H_job_of_tsk] at this
  exact this

/-! ### Lemmas about the interfering tasks -/

theorem bertogna_edf_tsk_other_in_ts
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (ts : taskset_of sporadic_task)
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (tsk_other : sporadic_task)
    (R_other : time)
    (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ rt_bounds)
    :
    tsk_other ∈ ts :=
  (mem_ts_iff_bound ts rt_bounds H_rt_bounds_contains_all_tasks tsk_other).mpr
    ⟨R_other, H_response_time_of_tsk_other⟩

theorem bertogna_edf_R_other_ge_cost
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    (num_cpus : Nat)
    (rt_bounds : List (sporadic_task × time))
    (H_response_time_is_fixed_point :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds →
        R = task_cost tsk +
          div_floor (total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds R)
            num_cpus)
    (tsk_other : sporadic_task)
    (R_other : time)
    (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ rt_bounds)
    :
    task_cost tsk_other ≤ R_other := by
  have := H_response_time_is_fixed_point tsk_other R_other H_response_time_of_tsk_other
  omega'

theorem bertogna_edf_workload_bounds_interference
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_response_time_is_fixed_point :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds →
        R = task_cost tsk +
          div_floor (total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds R)
            num_cpus)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds → task_jitter tsk + R ≤ task_deadline tsk)
    (tsk : sporadic_task)
    (R : time)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + task_jitter tsk_other + R_other < job_arrival j + task_jitter tsk + R →
        completed job_cost sched j_other (job_arrival j_other + task_jitter tsk_other + R_other) = true)
    (tsk_other : sporadic_task)
    (R_other : time)
    (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ rt_bounds)
    :
    task_interference job_arrival job_cost job_task job_jitter sched j tsk_other (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) ≤ W_jitter task_cost task_period task_jitter tsk_other R_other R := by
  have INts := bertogna_edf_tsk_other_in_ts ts rt_bounds H_rt_bounds_contains_all_tasks tsk_other R_other H_response_time_of_tsk_other
  have hJIT := job_jitter_le task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j tsk
    (H_valid_job_parameters j H_j_arrives) H_job_of_tsk
  calc task_interference job_arrival job_cost job_task job_jitter sched j tsk_other (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)
      ≤ workload job_task sched tsk_other (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) :=
        task_interference_le_workload job_arrival job_cost job_task job_jitter sched j tsk_other _ _
    _ ≤ W_jitter task_cost task_period task_jitter tsk_other R_other R :=
        workload_bounded_by_W task_cost task_period task_deadline task_jitter job_arrival job_cost
          job_task job_deadline job_jitter arr_seq H_valid_job_parameters sched
          H_jobs_come_from_arrival_sequence H_execute_after_jitter
          H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks tsk_other
          (H_valid_task_parameters tsk_other INts) (H_constrained_deadlines tsk_other INts)
          (job_arrival j + job_jitter j) R R_other
          (bertogna_edf_R_other_ge_cost task_cost task_period task_deadline task_jitter num_cpus rt_bounds H_response_time_is_fixed_point tsk_other R_other H_response_time_of_tsk_other)
          (H_tasks_miss_no_deadlines _ _ H_response_time_of_tsk_other)
          (fun j' ARR' JOB' LT' => H_all_previous_jobs_completed_on_time j' tsk_other R_other ARR'
            JOB' H_response_time_of_tsk_other (by omega'))

theorem bertogna_edf_specific_bound_holds
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds → task_jitter tsk + R ≤ task_deadline tsk)
    (tsk : sporadic_task)
    (R : time)
    (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + job_jitter j + R)) = true)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + task_jitter tsk_other + R_other < job_arrival j + task_jitter tsk + R →
        completed job_cost sched j_other (job_arrival j_other + task_jitter tsk_other + R_other) = true)
    (tsk_other : sporadic_task)
    (R_other : time)
    (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ rt_bounds)
    :
    task_interference job_arrival job_cost job_task job_jitter sched j tsk_other (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) ≤
      edf_specific_interference_bound task_cost task_period task_deadline task_jitter tsk tsk_other R_other := by
  have Htsk : tsk ∈ ts :=
    (mem_ts_iff_bound ts rt_bounds H_rt_bounds_contains_all_tasks tsk).mpr ⟨R, H_tsk_R_in_rt_bounds⟩
  have Hother : tsk_other ∈ ts :=
    (mem_ts_iff_bound ts rt_bounds H_rt_bounds_contains_all_tasks tsk_other).mpr
      ⟨R_other, H_response_time_of_tsk_other⟩
  have hRD := H_tasks_miss_no_deadlines tsk R H_tsk_R_in_rt_bounds
  exact interference_bound_edf_bounds_interference task_cost task_period task_deadline task_jitter job_arrival
    job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters num_cpus sched
    H_jobs_come_from_arrival_sequence H_execute_after_jitter H_completed_jobs_dont_execute
    H_sequential_jobs H_at_least_one_cpu ts H_valid_task_parameters H_constrained_deadlines
    H_edf_policy tsk Htsk j H_j_arrives H_job_of_tsk tsk_other Hother R_other
    (H_tasks_miss_no_deadlines _ _ H_response_time_of_tsk_other) R (by omega')
    (fun j_k ARR JOB LT => H_all_previous_jobs_completed_on_time j_k tsk_other R_other ARR JOB
      H_response_time_of_tsk_other LT)

/-! ### Deriving a contradiction -/

theorem bertogna_edf_too_much_interference
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (rt_bounds : List (sporadic_task × time))
    (H_response_time_is_fixed_point :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds →
        R = task_cost tsk +
          div_floor (total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds R)
            num_cpus)
    (tsk : sporadic_task)
    (R : time)
    (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + job_jitter j + R)) = true)
    :
    R - task_cost tsk + 1 ≤ total_interference job_arrival job_cost job_jitter sched j (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) := by
  have hRe : task_cost tsk ≤ R := by
    have := H_response_time_is_fixed_point tsk R H_tsk_R_in_rt_bounds
    omega'
  have NOTCOMP := H_j_not_completed
  simp only [completed, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at NOTCOMP
  have hcost : job_cost j ≤ task_cost tsk := by
    have := (H_valid_job_parameters j H_j_arrives).1.2.1
    simp only [job_cost_le_task_cost, decide_eq_true_eq] at this
    rw [H_job_of_tsk] at this
    exact this
  have hsvc : service sched j (job_arrival j + job_jitter j + R) =
      ∑ t ∈ Finset.Ico (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R), service_at sched j t := by
    unfold service
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le (job_arrival j + job_jitter j)) (Nat.le_add_right _ R),
      cumulative_service_before_jitter_zero job_arrival job_jitter sched H_execute_after_jitter j 0 _
        (Nat.le_refl _), Nat.zero_add]
  have hcover : R ≤ ∑ t ∈ Finset.Ico (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R),
      ((backlogged job_arrival job_cost job_jitter sched j t).toNat + service_at sched j t) := by
    calc R = ∑ _t ∈ Finset.Ico (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R), 1 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_Ico] at ht
        cases hb : backlogged job_arrival job_cost job_jitter sched j t
        · simp only [Bool.toNat_false, Nat.zero_add]
          have hpend : pending job_arrival job_cost job_jitter sched j t = true := by
            simp only [pending, jitter_has_passed, actual_arrival, Bool.and_eq_true, Bool.not_eq_true']
            refine ⟨decide_eq_true ht.1, ?_⟩
            cases hc : completed job_cost sched j t
            · rfl
            · have := completion_monotonic job_cost sched j t (job_arrival j + job_jitter j + R)
                (Nat.le_of_lt ht.2) hc
              simp only [completed, decide_eq_true_eq] at this
              omega'
          simp only [backlogged, hpend, Bool.true_and, Bool.not_eq_false'] at hb
          have := not_scheduled_no_service sched j t
          rw [hb] at this
          have hne : service_at sched j t ≠ 0 := by
            intro h0; rw [h0] at this; simp at this
          omega'
        · simp
  unfold total_interference
  rw [Finset.sum_add_distrib] at hcover
  rw [hsvc] at NOTCOMP
  omega'

theorem bertogna_edf_interference_by_different_tasks
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (ts : taskset_of sporadic_task)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (rt_bounds : List (sporadic_task × time))
    (H_tasks_miss_no_deadlines :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds → task_jitter tsk + R ≤ task_deadline tsk)
    (tsk : sporadic_task)
    (R : time)
    (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + task_jitter tsk_other + R_other < job_arrival j + task_jitter tsk + R →
        completed job_cost sched j_other (job_arrival j_other + task_jitter tsk_other + R_other) = true)
    :
    ∀ (t : time) (j_other : Job),
      (decide ((job_arrival j + job_jitter j) ≤ t) && decide (t < (job_arrival j + job_jitter j + R))) = true →
      backlogged job_arrival job_cost job_jitter sched j t = true →
      scheduled sched j_other t = true →
      (!decide (job_task j_other = tsk)) = true := by
  intro t j_other RANGE BACK SCHED
  simp only [Bool.and_eq_true, decide_eq_true_eq] at RANGE
  obtain ⟨LEt, GEt⟩ := RANGE
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  intro SAMEtsk
  have ARRother := H_jobs_come_from_arrival_sequence j_other t SCHED
  have PENDING := scheduled_implies_pending job_arrival job_cost job_jitter sched
    H_execute_after_jitter H_completed_jobs_dont_execute j_other t SCHED
  simp only [pending, jitter_has_passed, actual_arrival, Bool.and_eq_true, Bool.not_eq_true'] at PENDING
  obtain ⟨ARRIVED0, NOTCOMP⟩ := PENDING
  have ARRIVED : job_arrival j_other + job_jitter j_other ≤ t := of_decide_eq_true ARRIVED0
  have hDp : task_deadline tsk ≤ task_period tsk := by
    apply H_constrained_deadlines
    rw [← H_job_of_tsk]
    exact H_all_jobs_from_taskset j H_j_arrives
  have hRD := H_tasks_miss_no_deadlines tsk R H_tsk_R_in_rt_bounds
  have hJIT := job_jitter_le task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j tsk
    (H_valid_job_parameters j H_j_arrives) H_job_of_tsk
  rcases Nat.lt_or_ge (job_arrival j_other) (job_arrival j) with BEFORE | AFTER
  · have DIFF : j_other ≠ j := by
      rintro rfl
      exact Nat.lt_irrefl _ BEFORE
    have SPO := H_sporadic_tasks j_other j DIFF ARRother H_j_arrives
      (by rw [SAMEtsk, H_job_of_tsk]) (Nat.le_of_lt BEFORE)
    rw [SAMEtsk] at SPO
    have COMP := H_all_previous_jobs_completed_on_time j_other tsk R ARRother SAMEtsk
      H_tsk_R_in_rt_bounds (by omega')
    have := completion_monotonic job_cost sched j_other _ t (by omega') COMP
    rw [this] at NOTCOMP
    exact Bool.noConfusion NOTCOMP
  · by_cases EQ : j = j_other
    · subst EQ
      simp [backlogged, SCHED] at BACK
    · have SPO := H_sporadic_tasks j j_other EQ H_j_arrives ARRother
        (by rw [SAMEtsk, H_job_of_tsk]) AFTER
      rw [H_job_of_tsk] at SPO
      omega'

theorem bertogna_edf_all_previous_jobs_complete_by_their_period
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (ts : taskset_of sporadic_task)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds → task_jitter tsk + R ≤ task_deadline tsk)
    (tsk : sporadic_task)
    (R : time)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + task_jitter tsk_other + R_other < job_arrival j + task_jitter tsk + R →
        completed job_cost sched j_other (job_arrival j_other + task_jitter tsk_other + R_other) = true)
    :
    ∀ (t : time) (j0 : Job),
      t < (job_arrival j + job_jitter j + R) →
      arrives_in arr_seq j0 →
      job_arrival j0 + task_period (job_task j0) ≤ t →
      completed job_cost sched j0 (job_arrival j0 + task_period (job_task j0)) = true := by
  intro t j0 LEt ARR0 LE
  have IN : job_task j0 ∈ ts := H_all_jobs_from_taskset j0 ARR0
  obtain ⟨R0, hR0⟩ := (mem_ts_iff_bound ts rt_bounds H_rt_bounds_contains_all_tasks _).mp IN
  have hND := H_tasks_miss_no_deadlines _ _ hR0
  have hDP := H_constrained_deadlines _ IN
  have hJIT := job_jitter_le task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j tsk
    (H_valid_job_parameters j H_j_arrives) H_job_of_tsk
  apply completion_monotonic job_cost sched j0 (job_arrival j0 + task_jitter (job_task j0) + R0)
  · omega'
  · exact H_all_previous_jobs_completed_on_time j0 (job_task j0) R0 ARR0 rfl hR0 (by omega')

theorem bertogna_edf_all_cpus_are_busy
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds → task_jitter tsk + R ≤ task_deadline tsk)
    (tsk : sporadic_task)
    (R : time)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + task_jitter tsk_other + R_other < job_arrival j + task_jitter tsk + R →
        completed job_cost sched j_other (job_arrival j_other + task_jitter tsk_other + R_other) = true)
    :
    ∀ t : time,
      (decide ((job_arrival j + job_jitter j) ≤ t) && decide (t < (job_arrival j + job_jitter j + R))) = true →
      backlogged job_arrival job_cost job_jitter sched j t = true →
      ts.val.countP (fun tsk_other => task_is_scheduled job_task sched tsk_other t &&
        different_task tsk tsk_other) = num_cpus := by
  intro t RANGE BACK
  simp only [Bool.and_eq_true, decide_eq_true_eq] at RANGE
  have Htsk : tsk ∈ ts := by rw [← H_job_of_tsk]; exact H_all_jobs_from_taskset j H_j_arrives
  have COMP := bertogna_edf_all_previous_jobs_complete_by_their_period task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_valid_job_parameters ts H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched rt_bounds H_rt_bounds_contains_all_tasks H_tasks_miss_no_deadlines tsk R j H_j_arrives H_job_of_tsk H_all_previous_jobs_completed_on_time
  exact platform_cpus_busy_with_interfering_tasks task_cost task_period task_deadline job_arrival
    job_cost job_task job_jitter arr_seq sched H_jobs_come_from_arrival_sequence H_work_conserving ts
    H_all_jobs_from_taskset H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute
    H_sporadic_tasks tsk (H_valid_task_parameters tsk Htsk) j
    H_j_arrives H_job_of_tsk t BACK
    (fun j0 tsk0 ARR0 TSK0 LE0 => by
      subst TSK0
      exact COMP t j0 RANGE.2 ARR0 LE0)

theorem bertogna_edf_interference_on_all_cpus
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds → task_jitter tsk + R ≤ task_deadline tsk)
    (tsk : sporadic_task)
    (R : time)
    (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + task_jitter tsk_other + R_other < job_arrival j + task_jitter tsk + R →
        completed job_cost sched j_other (job_arrival j_other + task_jitter tsk_other + R_other) = true)
    :
    sumSeq (ts.val.filter (fun tsk_other => different_task tsk tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task job_jitter sched j tsk_k (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)) = total_interference job_arrival job_cost job_jitter sched j (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) * num_cpus := by
  have DIFFTASK := bertogna_edf_interference_by_different_tasks task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters ts H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence H_execute_after_jitter H_completed_jobs_dont_execute rt_bounds H_tasks_miss_no_deadlines tsk R H_tsk_R_in_rt_bounds j H_j_arrives H_job_of_tsk H_all_previous_jobs_completed_on_time
  have hHnd : (ts.val.filter (fun tsk_other => different_task tsk tsk_other)).Nodup := ts.nodup.filter _
  unfold sumSeq
  rw [← List.sum_toFinset _ hHnd]
  unfold total_interference task_interference
  rw [Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  rw [Finset.sum_comm]
  cases hb : backlogged job_arrival job_cost job_jitter sched j t
  · simp
  · simp only [Bool.true_and, Bool.toNat_true, Nat.one_mul]
    calc ∑ cpu : Fin num_cpus, ∑ k ∈ (ts.val.filter (fun tsk_other => different_task tsk tsk_other)).toFinset,
          (task_scheduled_on job_task sched k cpu t).toNat
        = ∑ _cpu : Fin num_cpus, 1 := by
          apply Finset.sum_congr rfl
          intro cpu _
          obtain ⟨j_other, SCHEDon⟩ := H_work_conserving j t H_j_arrives hb cpu
          have hs : sched cpu t = some j_other := by simpa [scheduled_on] using SCHEDon
          have SCHED : scheduled sched j_other t = true := by
            simp only [scheduled, List.any_eq_true, List.mem_finRange, true_and]
            exact ⟨cpu, SCHEDon⟩
          have ARRother := H_jobs_come_from_arrival_sequence j_other t SCHED
          have INH : job_task j_other ∈ (ts.val.filter (fun tsk_other => different_task tsk tsk_other)).toFinset := by
            rw [List.mem_toFinset, List.mem_filter]
            exact ⟨H_all_jobs_from_taskset j_other ARRother,
              DIFFTASK t j_other (by simp [ht.1, ht.2]) hb SCHED⟩
          have hind : ∀ k, (task_scheduled_on job_task sched k cpu t).toNat =
              if job_task j_other = k then 1 else 0 := by
            intro k
            simp only [task_scheduled_on, hs]
            by_cases h : job_task j_other = k <;> simp [h]
          rw [Finset.sum_congr rfl (fun k _ => hind k), Finset.sum_ite_eq, if_pos INH]
      _ = num_cpus := by simp

theorem bertogna_edf_interference_in_non_full_processors
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds → task_jitter tsk + R ≤ task_deadline tsk)
    (tsk : sporadic_task)
    (R : time)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + task_jitter tsk_other + R_other < job_arrival j + task_jitter tsk + R →
        completed job_cost sched j_other (job_arrival j_other + task_jitter tsk_other + R_other) = true)
    :
    ∀ delta : time,
      (decide (0 < (ts.val.filter (fun tsk_other => different_task tsk tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task job_jitter sched j i (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)))) && decide ((ts.val.filter (fun tsk_other => different_task tsk tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task job_jitter sched j i (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R))) < num_cpus)) = true →
      delta * (num_cpus - (ts.val.filter (fun tsk_other => different_task tsk tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task job_jitter sched j i (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)))) ≤
        sumFiltered (ts.val.filter (fun tsk_other => different_task tsk tsk_other)) (fun i => decide (task_interference job_arrival job_cost job_task job_jitter sched j i (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) < delta)) (fun i => task_interference job_arrival job_cost job_task job_jitter sched j i (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)) := by
  intro delta HAS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at HAS
  have hHnd : (ts.val.filter (fun tsk_other => different_task tsk tsk_other)).Nodup := ts.nodup.filter _
  have Htsk : tsk ∈ ts := by rw [← H_job_of_tsk]; exact H_all_jobs_from_taskset j H_j_arrives
  have INV := bertogna_edf_all_cpus_are_busy task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving rt_bounds H_rt_bounds_contains_all_tasks H_tasks_miss_no_deadlines tsk R j H_j_arrives H_job_of_tsk H_all_previous_jobs_completed_on_time
  have COMP := bertogna_edf_all_previous_jobs_complete_by_their_period task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_valid_job_parameters ts H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched rt_bounds H_rt_bounds_contains_all_tasks H_tasks_miss_no_deadlines tsk R j H_j_arrives H_job_of_tsk H_all_previous_jobs_completed_on_time
  refine interference_in_non_full_processors_core
    (Finset.Ico (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R))
    (fun t => backlogged job_arrival job_cost job_jitter sched j t)
    (fun k cpu t => task_scheduled_on job_task sched k cpu t)
    (fun k => task_interference job_arrival job_cost job_task job_jitter sched j k (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)) (fun k => rfl) (ts.val.filter (fun tsk_other => different_task tsk tsk_other)) hHnd ?_ num_cpus ?_ delta HAS.1 HAS.2
  · intro k hk t ht _ c1 c2 h1 h2
    rw [Finset.mem_Ico] at ht
    simp only [task_scheduled_on] at h1 h2
    cases hs1 : sched c1 t with
    | none => simp [hs1] at h1
    | some j1 =>
      cases hs2 : sched c2 t with
      | none => simp [hs2] at h2
      | some j2 =>
        simp only [hs1, hs2, decide_eq_true_eq] at h1 h2
        have SCHED1 : scheduled sched j1 t = true := by
          simp only [scheduled, scheduled_on, List.any_eq_true, List.mem_finRange, true_and,
            decide_eq_true_eq]
          exact ⟨c1, hs1⟩
        have SCHED2 : scheduled sched j2 t = true := by
          simp only [scheduled, scheduled_on, List.any_eq_true, List.mem_finRange, true_and,
            decide_eq_true_eq]
          exact ⟨c2, hs2⟩
        have EQ : j1 = j2 := platform_at_most_one_pending_job_of_each_task task_cost task_period
          task_deadline job_arrival job_cost job_task job_jitter arr_seq sched H_sporadic_tasks tsk
          (H_valid_task_parameters tsk Htsk) j H_job_of_tsk t
          (fun j0 tsk0 ARR0 TSK0 LE0 => by
            subst TSK0
            exact COMP t j0 ht.2 ARR0 LE0)
          j1 j2 (H_jobs_come_from_arrival_sequence j1 t SCHED1)
          (H_jobs_come_from_arrival_sequence j2 t SCHED2)
          (scheduled_implies_pending job_arrival job_cost job_jitter sched H_execute_after_jitter
            H_completed_jobs_dont_execute j1 t SCHED1)
          (scheduled_implies_pending job_arrival job_cost job_jitter sched H_execute_after_jitter
            H_completed_jobs_dont_execute j2 t SCHED2)
          (h1.trans h2.symm)
        subst EQ
        exact H_sequential_jobs j1 t c1 c2 hs1 hs2
  · intro t ht hb
    rw [Finset.mem_Ico] at ht
    rw [List.countP_filter]
    exact le_of_eq (INV t (by simp [ht.1, ht.2]) hb).symm

theorem bertogna_edf_minimum_exceeds_interference
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds → task_jitter tsk + R ≤ task_deadline tsk)
    (tsk : sporadic_task)
    (R : time)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + task_jitter tsk_other + R_other < job_arrival j + task_jitter tsk + R →
        completed job_cost sched j_other (job_arrival j_other + task_jitter tsk_other + R_other) = true)
    :
    ∀ delta : time,
      delta * num_cpus ≤ sumSeq (ts.val.filter (fun tsk_other => different_task tsk tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task job_jitter sched j tsk_k (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)) →
      delta * num_cpus ≤ sumSeq (ts.val.filter (fun tsk_other => different_task tsk tsk_other)) (fun tsk_k => min (task_interference job_arrival job_cost job_task job_jitter sched j tsk_k (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)) delta) := by
  intro delta SUMLESS
  rw [sum_min_split (ts.val.filter (fun tsk_other => different_task tsk tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task job_jitter sched j tsk_k (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)) delta]
  by_cases hN0 : (ts.val.filter (fun tsk_other => different_task tsk tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task job_jitter sched j i (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R))) = 0
  · have hall : sumFiltered (ts.val.filter (fun tsk_other => different_task tsk tsk_other)) (fun i => decide (task_interference job_arrival job_cost job_task job_jitter sched j i (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) < delta)) (fun i => task_interference job_arrival job_cost job_task job_jitter sched j i (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)) =
        sumSeq (ts.val.filter (fun tsk_other => different_task tsk tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task job_jitter sched j tsk_k (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)) := by
      unfold sumFiltered sumSeq
      congr 2
      apply List.filter_eq_self.mpr
      intro k hk
      have := List.countP_eq_zero.mp hN0 k hk
      simp only [decide_eq_true_eq, Nat.not_le] at this
      simpa using this
    rw [hall, hN0]
    omega'
  · by_cases hNm : num_cpus ≤ (ts.val.filter (fun tsk_other => different_task tsk tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task job_jitter sched j i (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)))
    · have := Nat.mul_le_mul_left delta hNm
      omega'
    · have NONFULL := bertogna_edf_interference_in_non_full_processors task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving rt_bounds H_rt_bounds_contains_all_tasks H_tasks_miss_no_deadlines tsk R j H_j_arrives H_job_of_tsk H_all_previous_jobs_completed_on_time delta
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
      have e : delta * (ts.val.filter (fun tsk_other => different_task tsk tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task job_jitter sched j i (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R))) + delta * (num_cpus - (ts.val.filter (fun tsk_other => different_task tsk tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task job_jitter sched j i (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)))) = delta * num_cpus := by
        rw [← Nat.mul_add]
        congr 1
        omega'
      omega'

theorem bertogna_edf_sum_exceeds_total_interference
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_response_time_is_fixed_point :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds →
        R = task_cost tsk +
          div_floor (total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds R)
            num_cpus)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds → task_jitter tsk + R ≤ task_deadline tsk)
    (tsk : sporadic_task)
    (R : time)
    (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + job_jitter j + R)) = true)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + task_jitter tsk_other + R_other < job_arrival j + task_jitter tsk + R →
        completed job_cost sched j_other (job_arrival j_other + task_jitter tsk_other + R_other) = true)
    :
    total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds R <
      sumFiltered rt_bounds (fun (tsk_other, _R_other) => different_task tsk tsk_other)
        (fun (tsk_other, R_other) => min (task_interference job_arrival job_cost job_task job_jitter sched j tsk_other (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)) (R - task_cost tsk + 1)) := by
  have EXCEEDS := bertogna_edf_minimum_exceeds_interference task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving rt_bounds H_rt_bounds_contains_all_tasks H_tasks_miss_no_deadlines tsk R j H_j_arrives H_job_of_tsk H_all_previous_jobs_completed_on_time
  have ALLBUSY := bertogna_edf_interference_on_all_cpus task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence H_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving rt_bounds H_rt_bounds_contains_all_tasks H_tasks_miss_no_deadlines tsk R H_tsk_R_in_rt_bounds j H_j_arrives H_job_of_tsk H_all_previous_jobs_completed_on_time
  have TOOMUCH := bertogna_edf_too_much_interference task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_valid_job_parameters num_cpus sched H_execute_after_jitter rt_bounds H_response_time_is_fixed_point tsk R H_tsk_R_in_rt_bounds j H_j_arrives H_job_of_tsk H_j_not_completed
  have hsub : sumSeq (ts.val.filter (fun tsk_other => different_task tsk tsk_other)) (fun tsk_k => min (task_interference job_arrival job_cost job_task job_jitter sched j tsk_k (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)) (R - task_cost tsk + 1)) =
      sumFiltered rt_bounds (fun (tsk_other, _R_other) => different_task tsk tsk_other)
        (fun (tsk_other, R_other) => min (task_interference job_arrival job_cost job_task job_jitter sched j tsk_other (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)) (R - task_cost tsk + 1)) := by
    unfold sumSeq sumFiltered
    rw [← H_rt_bounds_contains_all_tasks, List.filter_map, List.map_map]
    rfl
  have REC := H_response_time_is_fixed_point tsk R H_tsk_R_in_rt_bounds
  unfold div_floor at REC
  apply ltn_div_trunc _ _ num_cpus H_at_least_one_cpu
  have hdiv : total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds R /
      num_cpus = R - task_cost tsk := by
    generalize total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds R /
      num_cpus = q at REC ⊢
    omega'
  rw [hdiv]
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
  rw [Nat.le_div_iff_mul_le H_at_least_one_cpu, ← hsub]
  apply EXCEEDS
  rw [ALLBUSY]
  exact Nat.mul_le_mul_right _ TOOMUCH

theorem bertogna_edf_exists_task_that_exceeds_bound
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_response_time_is_fixed_point :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds →
        R = task_cost tsk +
          div_floor (total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds R)
            num_cpus)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds → task_jitter tsk + R ≤ task_deadline tsk)
    (tsk : sporadic_task)
    (R : time)
    (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + job_jitter j + R)) = true)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + task_jitter tsk_other + R_other < job_arrival j + task_jitter tsk + R →
        completed job_cost sched j_other (job_arrival j_other + task_jitter tsk_other + R_other) = true)
    :
    ∃ (tsk_other : sporadic_task) (R_other : time),
      (tsk_other, R_other) ∈ rt_bounds ∧
      interference_bound_edf task_cost task_period task_deadline task_jitter tsk R (tsk_other, R_other) <
        min (task_interference job_arrival job_cost job_task job_jitter sched j tsk_other (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)) (R - task_cost tsk + 1) := by
  have SUM := bertogna_edf_sum_exceeds_total_interference task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving rt_bounds H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines tsk R H_tsk_R_in_rt_bounds j H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time
  by_contra NOT
  simp only [not_exists, not_and, Nat.not_lt] at NOT
  apply absurd SUM
  apply Nat.not_lt.mpr
  unfold total_interference_bound_edf sumFiltered
  apply List.sum_le_sum
  rintro ⟨k, Rk⟩ hk
  rw [List.mem_filter] at hk
  exact NOT k Rk hk.1

/-! ### Main theorem -/

theorem bertogna_cirinei_response_time_bound_edf
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → time)
    {arr_seq : arrival_sequence Job}
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_response_time_is_fixed_point :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds →
        R = task_cost tsk +
          div_floor (total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds R)
            num_cpus)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds → task_jitter tsk + R ≤ task_deadline tsk)
    (tsk : sporadic_task)
    (R : time)
    (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)
    :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (task_jitter tsk + R) := by
  suffices MAIN : ∀ (n : Nat) (j : Job) (tsk : sporadic_task) (R : time),
      job_arrival j + task_jitter tsk + R = n → (tsk, R) ∈ rt_bounds → arrives_in arr_seq j →
      job_task j = tsk → completed job_cost sched j (job_arrival j + task_jitter tsk + R) = true by
    intro j ARRj JOBtsk
    rw [← Nat.add_assoc]
    exact MAIN _ j tsk R rfl H_tsk_R_in_rt_bounds ARRj JOBtsk
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro j tsk' R' hn INbounds ARRj JOBtsk
    have hJIT := job_jitter_le task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j tsk'
      (H_valid_job_parameters j ARRj) JOBtsk
    apply completion_monotonic job_cost sched j (job_arrival j + job_jitter j + R') _ (by omega')
    by_contra NOTCOMP
    have NOTCOMP' : (!completed job_cost sched j (job_arrival j + job_jitter j + R')) = true := by
      simpa using NOTCOMP
    have BEFOREok : ∀ (j0 : Job) (tsk0 : sporadic_task) (R0 : time),
        arrives_in arr_seq j0 → job_task j0 = tsk0 → (tsk0, R0) ∈ rt_bounds →
        job_arrival j0 + task_jitter tsk0 + R0 < job_arrival j + task_jitter tsk' + R' →
        completed job_cost sched j0 (job_arrival j0 + task_jitter tsk0 + R0) = true :=
      fun j0 tsk0 R0 ARR0 JOB0 IN0 LT0 => IH _ (hn ▸ LT0) j0 tsk0 R0 rfl IN0 ARR0 JOB0
    obtain ⟨tsk_other, R_other, HP, LTmin⟩ := bertogna_edf_exists_task_that_exceeds_bound task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy rt_bounds H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines tsk' R' INbounds j ARRj JOBtsk NOTCOMP' BEFOREok
    have BASIC := bertogna_edf_workload_bounds_interference task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines num_cpus sched H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute rt_bounds H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines tsk' R' j ARRj JOBtsk BEFOREok tsk_other R_other HP
    have EDFB := bertogna_edf_specific_bound_holds task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines num_cpus sched H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_edf_policy rt_bounds H_rt_bounds_contains_all_tasks H_tasks_miss_no_deadlines tsk' R' INbounds j ARRj JOBtsk NOTCOMP' BEFOREok tsk_other R_other HP
    simp only [interference_bound_edf, interference_bound_generic] at LTmin
    have h : min (task_interference job_arrival job_cost job_task job_jitter sched j tsk_other (job_arrival j + job_jitter j)
          (job_arrival j + job_jitter j + R')) (R' - task_cost tsk' + 1) ≤
        min (min (W_jitter task_cost task_period task_jitter tsk_other R_other R') (R' - task_cost tsk' + 1))
          (edf_specific_interference_bound task_cost task_period task_deadline task_jitter tsk' tsk_other
            R_other) :=
      le_min (le_min (le_trans (min_le_left _ _) BASIC) (min_le_right _ _))
        (le_trans (min_le_left _ _) EDFB)
    exact absurd LTmin (Nat.not_lt.mpr h)

end Prosa.Classic.Analysis.Global.Jitter.BertognaEdfTheory.ResponseTimeAnalysisEDFJitter
