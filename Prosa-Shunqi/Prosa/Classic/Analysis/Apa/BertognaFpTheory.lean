-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/apa/bertogna_fp_theory.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 46)

import Prosa.Util.Sum
import Prosa.Classic.Util.Counting
import Prosa.Classic.Util.DivMod
import Prosa.Classic.Util.Sum
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Platform
import Prosa.Classic.Model.Schedule.Apa.ConstrainedDeadlines
import Prosa.Classic.Model.Schedule.Apa.Interference
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Analysis.Apa.WorkloadBound
import Prosa.Classic.Analysis.Apa.InterferenceBoundFp

/-!
The APA reduction of Bertogna and Cirinei's response-time analysis for global FP
scheduling with processor affinities (Rocq module `ResponseTimeAnalysisFP`,
`classic/analysis/apa`): any fixed point of the recurrence computed with a
subaffinity `alpha'` is a safe response-time bound (Lemma 9 of the revised APA
paper, ECRTS 2013).

Representation notes:
* The section-local `Let`s are unfolded in the statements: `x tsk_other` is
  `task_interference job_arrival job_cost job_task sched alpha j tsk_other
  (job_arrival j) (job_arrival j + R)`, `X` is `total_interference job_arrival
  job_cost sched j (job_arrival j) (job_arrival j + R)`, `workload_bound tsk_other
  R_other` is `W task_cost task_period tsk_other R_other R`, `hp_task_in a` is
  `higher_priority_task_in alpha higher_eq_priority tsk a`, `hp_tasks_in a'` is
  `ts.val.filter (fun tsk_other => higher_priority_task_in alpha higher_eq_priority
  tsk (a' tsk) tsk_other)`, `scheduled_on_alpha_tsk t tsk_k` is
  `task_scheduled_on_affinity job_task sched (alpha tsk) tsk_k t`,
  `num_tasks_exceeding delta` is
  `(hp_tasks_in alpha').countP (fun i => decide (delta ≤ x i))` and
  `response_time_bounded_by` is `is_response_time_bound_of_task … sched`.
* `#|alpha' tsk|` is `(Finset.univ.filter (fun x => x ∈ alpha' tsk)).card` (as in
  `Affinity`); `count P s` is `s.countP P`; `\sum_(i <- s) F i` is
  `Prosa.Util.Sum.sumSeq s F` and `\sum_(i <- s | P i) F i` is
  `Prosa.Util.Sum.sumFiltered s P F`, with pairs bound by pattern matching; `minn`
  is `min`; Boolean chains `a <= b < c` in proposition position are
  `(decide (a ≤ b) && decide (b < c)) = true`; `x != y` in proposition position is
  `(!decide (x = y)) = true`.
* The Rocq module `Export`s the classic model modules it uses; Lean clients open
  those namespaces directly.
* Binder lists follow the Rocq contract (`About` on the Rocq 9.3 reference build),
  including which section hypotheses each lemma abstracts; Rocq abstracts every
  section hypothesis its proof script mentions, so some binders are unused here
  (e.g. `bertogna_fp_workload_bounds_interference` does not take
  `H_tsk_other_has_higher_priority`, which its proof does not use).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Apa.BertognaFpTheory.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority (FP_policy)
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity
open Prosa.Classic.Model.Schedule.Apa.Platform.Platform
open Prosa.Classic.Model.Schedule.Apa.Interference.Interference
open Prosa.Classic.Model.Schedule.Apa.ConstrainedDeadlines.ConstrainedDeadlines
open Prosa.Classic.Analysis.Apa.WorkloadBound.WorkloadBound
open Prosa.Classic.Analysis.Apa.InterferenceBoundFp.InterferenceBoundFP
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


/-! ### Lemmas about the higher-priority tasks -/

theorem bertogna_fp_workload_bounds_interference
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds →
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_response_time_bounds_ge_cost :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds → task_cost hp_tsk ≤ R)
    (H_interfering_tasks_miss_no_deadlines :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time)
    (j : Job)
    (tsk_other : sporadic_task)
    (R_other : time)
    (H_tsk_other_already_processed : (tsk_other, R_other) ∈ hp_bounds) :
    task_interference job_arrival job_cost job_task sched alpha j tsk_other (job_arrival j) (job_arrival j + R) ≤ W task_cost task_period tsk_other R_other R := by
  by_cases hx0 : task_interference job_arrival job_cost job_task sched alpha j tsk_other (job_arrival j) (job_arrival j + R) = 0
  · rw [hx0]; exact Nat.zero_le _
  unfold task_interference at hx0
  obtain ⟨t, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx0
  obtain ⟨cpu, _, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hts : task_scheduled_on job_task sched tsk_other cpu t = true := by
    by_contra h
    simp only [Bool.not_eq_true] at h
    simp [h] at hne'
  unfold task_scheduled_on at hts
  cases hs : sched cpu t with
  | none => simp [hs] at hts
  | some j0 =>
      simp only [hs, decide_eq_true_eq] at hts
      have SCHED : scheduled sched j0 t = true := by
        simp only [scheduled, scheduled_on, List.any_eq_true, List.mem_finRange, true_and,
          decide_eq_true_eq]
        exact ⟨cpu, hs⟩
      have INts : tsk_other ∈ ts := by
        rw [← hts]
        exact H_all_jobs_from_taskset j0 (H_jobs_come_from_arrival_sequence j0 t SCHED)
      calc task_interference job_arrival job_cost job_task sched alpha j tsk_other (job_arrival j) (job_arrival j + R)
          ≤ workload job_task sched tsk_other (job_arrival j) (job_arrival j + R) :=
            task_interference_le_workload job_arrival job_cost job_task sched alpha j tsk_other
              _ _
        _ ≤ W task_cost task_period tsk_other R_other R :=
            workload_bounded_by_W task_cost task_period task_deadline job_arrival job_cost
              job_task job_deadline arr_seq H_valid_job_parameters sched
              H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
              H_completed_jobs_dont_execute H_sequential_jobs H_sporadic_tasks tsk_other
              (H_valid_task_parameters tsk_other INts) (H_constrained_deadlines tsk_other INts)
              (job_arrival j) R R_other
              (fun j' ARR' JOB' _ => H_response_time_of_interfering_tasks_is_known tsk_other
                R_other H_tsk_other_already_processed j' ARR' JOB')
              (H_response_time_bounds_ge_cost _ _ H_tsk_other_already_processed)
              (H_interfering_tasks_miss_no_deadlines _ _ H_tsk_other_already_processed)

/-! ### Deriving a contradiction -/

theorem bertogna_fp_too_much_interference
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (higher_eq_priority : FP_policy sporadic_task)
    (tsk : sporadic_task)
    (alpha' : task_affinity sporadic_task num_cpus)
    (hp_bounds : List (sporadic_task × time))
    (R : time)
    (H_response_time_recurrence_holds :
      R = task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period alpha tsk (alpha' tsk)
          hp_bounds R higher_eq_priority) (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true) :
    R - task_cost tsk + 1 ≤ total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R) := by
  have hRe : task_cost tsk ≤ R := by
    have := H_response_time_recurrence_holds
    omega'
  have NOTCOMP := H_j_not_completed
  simp only [completed, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at NOTCOMP
  have hcost : job_cost j ≤ task_cost tsk := by
    have := (H_valid_job_parameters j H_j_arrives).2.1
    simp only [job_cost_le_task_cost, decide_eq_true_eq] at this
    rw [H_job_of_tsk] at this
    exact this
  have hsvc : service sched j (job_arrival j + R) =
      ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), service_at sched j t :=
    service_before_arrival_eq_service_during job_arrival sched j H_jobs_must_arrive_to_execute 0 R
      (Nat.zero_le _)
  have hcover : R ≤ ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
      ((backlogged job_arrival job_cost sched j t).toNat + service_at sched j t) := by
    calc R = ∑ _t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), 1 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_Ico] at ht
        cases hb : backlogged job_arrival job_cost sched j t
        · simp only [Bool.toNat_false, Nat.zero_add]
          have hpend : pending job_arrival job_cost sched j t = true := by
            simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq,
              Bool.not_eq_true']
            refine ⟨ht.1, ?_⟩
            cases hc : completed job_cost sched j t
            · rfl
            · have := completion_monotonic job_cost sched j t (job_arrival j + R)
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

theorem bertogna_fp_interference_by_different_tasks
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (ts : taskset_of sporadic_task)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (R : time)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed :
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) :
    ∀ (t : time) (j_other : Job),
      (decide (job_arrival j ≤ t) && decide (t < job_arrival j + R)) = true →
      arrives_in arr_seq j_other →
      backlogged job_arrival job_cost sched j t = true →
      scheduled sched j_other t = true →
      (!decide (job_task j_other = tsk)) = true := by
  intro t j_other RANGE ARRother BACK SCHED
  simp only [Bool.and_eq_true, decide_eq_true_eq] at RANGE
  obtain ⟨LEt, GEt⟩ := RANGE
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  intro SAMEtsk
  have PENDING := scheduled_implies_pending job_arrival job_cost sched j_other
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t SCHED
  simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at PENDING
  obtain ⟨ARRIVED, NOTCOMP⟩ := PENDING
  have hDp : task_deadline tsk ≤ task_period tsk := by
    apply H_constrained_deadlines
    rw [← H_job_of_tsk]
    exact H_all_jobs_from_taskset j H_j_arrives
  have hRD := H_response_time_no_larger_than_deadline
  rcases Nat.lt_or_ge (job_arrival j_other) (job_arrival j) with BEFORE | AFTER
  · have DIFF : j_other ≠ j := by
      rintro rfl
      exact Nat.lt_irrefl _ BEFORE
    have SPO := H_sporadic_tasks j_other j DIFF ARRother H_j_arrives
      (by rw [SAMEtsk, H_job_of_tsk]) (Nat.le_of_lt BEFORE)
    rw [SAMEtsk] at SPO
    have COMP := H_previous_jobs_of_tsk_completed j_other ARRother SAMEtsk BEFORE
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


theorem bertogna_fp_previous_interfering_jobs_complete_by_their_period
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (ts : taskset_of sporadic_task)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (higher_eq_priority : FP_policy sporadic_task)
    (tsk : sporadic_task)
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds →
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_interfering_tasks_miss_no_deadlines :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk) :
    ∀ j0 : Job,
      arrives_in arr_seq j0 →
      higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) (job_task j0) = true →
      completed job_cost sched j0 (job_arrival j0 + task_period (job_task j0)) = true := by
  intro j0 ARR0 INTERF
  have IN : job_task j0 ∈ ts := H_all_jobs_from_taskset j0 ARR0
  obtain ⟨R0, hR0⟩ := H_hp_bounds_has_interfering_tasks (job_task j0) IN INTERF
  apply completion_monotonic job_cost sched j0 (job_arrival j0 + R0)
  · exact Nat.add_le_add_left (Nat.le_trans (H_interfering_tasks_miss_no_deadlines _ _ hR0)
      (H_constrained_deadlines _ IN)) _
  · exact H_response_time_of_interfering_tasks_is_known _ _ hR0 j0 ARR0 rfl

/-- LEAN_HELPER: the job running on a processor of `alpha' tsk` (or `alpha tsk`) while
`j` is backlogged belongs to a higher-priority task that can run there. -/
private theorem running_job_is_hp
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (ts : taskset_of sporadic_task)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_respects_affinity : respects_affinity job_task sched alpha)
    (H_work_conserving :
      apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
    (H_respects_FP_policy :
      respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched alpha
        higher_eq_priority)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (R : time)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed :
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) (t : time)
    (RANGE : job_arrival j ≤ t ∧ t < job_arrival j + R)
    (BACK : backlogged job_arrival job_cost sched j t = true)
    (cpu : Fin num_cpus) (hcpu : cpu ∈ alpha tsk) :
    ∃ jo : Job, sched cpu t = some jo ∧ arrives_in arr_seq jo ∧
      scheduled sched jo t = true ∧ cpu ∈ alpha (job_task jo) ∧
      job_task jo ∈ ts ∧
      higher_eq_priority (job_task jo) tsk = true ∧ (!decide (job_task jo = tsk)) = true := by
  have DIFFTASK := bertogna_fp_interference_by_different_tasks task_period task_deadline
    job_arrival job_cost job_task arr_seq H_sporadic_tasks ts H_constrained_deadlines
    H_all_jobs_from_taskset sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    tsk task_in_ts R H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk
    H_previous_jobs_of_tsk_completed
  have CAN : can_execute_on alpha (job_task j) cpu = true := by
    simp [can_execute_on, H_job_of_tsk, hcpu]
  obtain ⟨jo, SCHEDon⟩ := H_work_conserving j t H_j_arrives BACK cpu CAN
  have hs : sched cpu t = some jo := by simpa [scheduled_on] using SCHEDon
  have SCHED : scheduled sched jo t = true := by
    simp only [scheduled, List.any_eq_true, List.mem_finRange, true_and]
    exact ⟨cpu, SCHEDon⟩
  have ARR := H_jobs_come_from_arrival_sequence jo t SCHED
  have AFF : cpu ∈ alpha (job_task jo) := by
    simpa [can_execute_on] using H_respects_affinity jo cpu t SCHEDon
  have HEP := H_respects_FP_policy j jo cpu t H_j_arrives BACK SCHEDon CAN
  rw [H_job_of_tsk] at HEP
  exact ⟨jo, hs, ARR, SCHED, AFF, H_all_jobs_from_taskset jo ARR, HEP,
    DIFFTASK t jo (by simp [RANGE.1, RANGE.2]) ARR BACK SCHED⟩

/-- LEAN_HELPER: a task of the form above interferes within any affinity containing `cpu`. -/
private theorem hp_task_in_of_cpu {sporadic_task : Type u} [DecidableEq sporadic_task]
    {num_cpus : Nat} (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : FP_policy sporadic_task) (tsk k : sporadic_task)
    (a : affinity num_cpus) (cpu : Fin num_cpus) (hca : cpu ∈ a) (hck : cpu ∈ alpha k)
    (HEP : higher_eq_priority k tsk = true) (NE : (!decide (k = tsk)) = true) :
    higher_priority_task_in alpha higher_eq_priority tsk a k = true := by
  simp only [higher_priority_task_in, affinity_intersects, Bool.and_eq_true, HEP, NE,
    true_and, List.any_eq_true]
  exact ⟨cpu, List.mem_finRange _, by simp [hca, hck]⟩

theorem bertogna_fp_all_cpus_in_affinity_busy
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_respects_affinity : respects_affinity job_task sched alpha)
    (H_work_conserving :
      apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
    (H_respects_FP_policy :
      respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched alpha
        higher_eq_priority)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (alpha' : task_affinity sporadic_task num_cpus)
    (H_affinity_subset :
      ∀ tsk : sporadic_task, tsk ∈ ts → is_subaffinity (alpha' tsk) (alpha tsk))
    (H_at_least_one_cpu :
      ∀ tsk : sporadic_task, tsk ∈ ts → 0 < (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (hp_bounds : List (sporadic_task × time))
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (R : time)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed :
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) :
    sumSeq (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task sched alpha j tsk_k (job_arrival j) (job_arrival j + R)) = total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R) * (Finset.univ.filter (fun x => x ∈ alpha tsk)).card := by
  have hHnd : ((ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) tsk_other))).Nodup := ts.nodup.filter _
  unfold sumSeq
  rw [← List.sum_toFinset _ hHnd]
  unfold total_interference task_interference
  rw [Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  rw [Finset.sum_comm]
  cases hb : backlogged job_arrival job_cost sched j t
  · simp
  · simp only [Bool.true_and, Bool.toNat_true, Nat.one_mul]
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro cpu _
    by_cases hcpu : cpu ∈ alpha tsk
    · have CAN : can_execute_on alpha (job_task j) cpu = true := by
        simp [can_execute_on, H_job_of_tsk, hcpu]
      obtain ⟨jo, hs, _, _, AFF, INts, HEP, NE⟩ := running_job_is_hp task_period task_deadline job_arrival job_cost job_task arr_seq
        H_sporadic_tasks ts H_constrained_deadlines H_all_jobs_from_taskset alpha sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity H_work_conserving
        H_respects_FP_policy tsk task_in_ts R H_response_time_no_larger_than_deadline j
        H_j_arrives H_job_of_tsk H_previous_jobs_of_tsk_completed t ht hb cpu hcpu
      have INH : job_task jo ∈ ((ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) tsk_other))).toFinset := by
        rw [List.mem_toFinset, List.mem_filter]
        exact ⟨INts, hp_task_in_of_cpu alpha higher_eq_priority tsk _ _ cpu hcpu AFF HEP NE⟩
      have hind : ∀ k, (can_execute_on alpha (job_task j) cpu &&
          task_scheduled_on job_task sched k cpu t).toNat =
          if job_task jo = k then 1 else 0 := by
        intro k
        simp only [CAN, Bool.true_and, task_scheduled_on, hs]
        by_cases h : job_task jo = k <;> simp [h]
      rw [Finset.sum_congr rfl (fun k _ => hind k), Finset.sum_ite_eq, if_pos INH, if_pos hcpu]
    · have CAN : can_execute_on alpha (job_task j) cpu = false := by
        simp [can_execute_on, H_job_of_tsk, hcpu]
      simp [CAN, hcpu]

theorem bertogna_fp_all_cpus_in_subaffinity_busy
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_respects_affinity : respects_affinity job_task sched alpha)
    (H_work_conserving :
      apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
    (H_respects_FP_policy :
      respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched alpha
        higher_eq_priority)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (alpha' : task_affinity sporadic_task num_cpus)
    (H_affinity_subset :
      ∀ tsk : sporadic_task, tsk ∈ ts → is_subaffinity (alpha' tsk) (alpha tsk))
    (H_at_least_one_cpu :
      ∀ tsk : sporadic_task, tsk ∈ ts → 0 < (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (hp_bounds : List (sporadic_task × time))
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (R : time)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed :
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) :
    total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R) * (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card ≤ sumSeq (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task sched alpha j tsk_k (job_arrival j) (job_arrival j + R)) := by
  have hHnd : ((ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))).Nodup := ts.nodup.filter _
  unfold sumSeq
  rw [← List.sum_toFinset _ hHnd]
  unfold total_interference task_interference
  rw [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.mem_Ico] at ht
  rw [Finset.sum_comm]
  cases hb : backlogged job_arrival job_cost sched j t
  · simp
  · simp only [Bool.true_and, Bool.toNat_true, Nat.one_mul]
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro cpu _
    by_cases hcpu : cpu ∈ alpha' tsk
    · have hsub := H_affinity_subset tsk task_in_ts cpu hcpu
      have CAN : can_execute_on alpha (job_task j) cpu = true := by
        simp [can_execute_on, H_job_of_tsk, hsub]
      obtain ⟨jo, hs, _, _, AFF, INts, HEP, NE⟩ := running_job_is_hp task_period task_deadline job_arrival job_cost job_task arr_seq
        H_sporadic_tasks ts H_constrained_deadlines H_all_jobs_from_taskset alpha sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity H_work_conserving
        H_respects_FP_policy tsk task_in_ts R H_response_time_no_larger_than_deadline j
        H_j_arrives H_job_of_tsk H_previous_jobs_of_tsk_completed t ht hb cpu hsub
      have INH : job_task jo ∈ ((ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))).toFinset := by
        rw [List.mem_toFinset, List.mem_filter]
        exact ⟨INts, hp_task_in_of_cpu alpha higher_eq_priority tsk _ _ cpu hcpu AFF HEP NE⟩
      have hind : ∀ k, (can_execute_on alpha (job_task j) cpu &&
          task_scheduled_on job_task sched k cpu t).toNat =
          if job_task jo = k then 1 else 0 := by
        intro k
        simp only [CAN, Bool.true_and, task_scheduled_on, hs]
        by_cases h : job_task jo = k <;> simp [h]
      rw [Finset.sum_congr rfl (fun k _ => hind k), Finset.sum_ite_eq, if_pos INH, if_pos hcpu]
    · rw [if_neg hcpu]
      exact Nat.zero_le _

theorem bertogna_fp_alpha'_is_full
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_respects_affinity : respects_affinity job_task sched alpha)
    (H_work_conserving :
      apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
    (H_respects_FP_policy :
      respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched alpha
        higher_eq_priority)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (alpha' : task_affinity sporadic_task num_cpus)
    (H_affinity_subset :
      ∀ tsk : sporadic_task, tsk ∈ ts → is_subaffinity (alpha' tsk) (alpha tsk))
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds →
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_interfering_tasks_miss_no_deadlines :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time)
    (H_response_time_recurrence_holds :
      R = task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period alpha tsk (alpha' tsk)
          hp_bounds R higher_eq_priority) (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed :
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) :
    ∀ t : time,
      (decide (job_arrival j ≤ t) && decide (t < job_arrival j + R)) = true →
      backlogged job_arrival job_cost sched j t = true →
      (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card ≤
        ((ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))).countP (fun tsk_k =>
          task_scheduled_on_affinity job_task sched (alpha tsk) tsk_k t) := by
  intro t RANGE BACK
  simp only [Bool.and_eq_true, decide_eq_true_eq] at RANGE
  have PREVhp := bertogna_fp_previous_interfering_jobs_complete_by_their_period task_period
    task_deadline job_arrival job_cost job_task arr_seq ts H_constrained_deadlines
    H_all_jobs_from_taskset alpha sched higher_eq_priority tsk hp_bounds
    H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
    H_interfering_tasks_miss_no_deadlines
  have key := running_job_is_hp task_period task_deadline job_arrival job_cost job_task arr_seq
    H_sporadic_tasks ts H_constrained_deadlines H_all_jobs_from_taskset alpha sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity H_work_conserving
    H_respects_FP_policy tsk task_in_ts R H_response_time_no_larger_than_deadline j
    H_j_arrives H_job_of_tsk H_previous_jobs_of_tsk_completed t RANGE BACK
  have hinj : Set.InjOn (fun cpu => ((sched cpu t).map job_task).getD tsk)
      ↑(Finset.univ.filter (fun x => x ∈ alpha' tsk)) := by
    intro c1 h1 c2 h2 hf
    rw [Finset.mem_coe, Finset.mem_filter] at h1 h2
    obtain ⟨j1, hs1, ARR1, SCHED1, AFF1, _, HEP1, NE1⟩ :=
      key c1 (H_affinity_subset tsk task_in_ts c1 h1.2)
    obtain ⟨j2, hs2, ARR2, SCHED2, _, _, _, _⟩ :=
      key c2 (H_affinity_subset tsk task_in_ts c2 h2.2)
    simp only [hs1, hs2, Option.map_some, Option.getD_some] at hf
    have EQ : j1 = j2 := platform_fp_no_multiple_jobs_of_interfering_tasks task_period
      job_arrival job_cost job_task arr_seq sched alpha higher_eq_priority H_sporadic_tasks tsk t
      (fun jo ko A T HP => by subst T; exact PREVhp jo A HP) j1 j2 ARR1 ARR2
      (scheduled_implies_pending job_arrival job_cost sched j1 H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute t SCHED1)
      (scheduled_implies_pending job_arrival job_cost sched j2 H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute t SCHED2)
      hf (hp_task_in_of_cpu alpha higher_eq_priority tsk _ _ c1
        (H_affinity_subset tsk task_in_ts c1 h1.2) AFF1 HEP1 NE1)
    subst EQ
    exact H_sequential_jobs j1 t c1 c2 hs1 hs2
  have himg : (Finset.univ.filter (fun x => x ∈ alpha' tsk)).image
        (fun cpu => ((sched cpu t).map job_task).getD tsk) ⊆
      (((ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))).filter (fun tsk_k =>
        task_scheduled_on_affinity job_task sched (alpha tsk) tsk_k t)).toFinset := by
    intro k hk
    obtain ⟨cpu, hcpu, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_filter] at hcpu
    have hsub := H_affinity_subset tsk task_in_ts cpu hcpu.2
    obtain ⟨jo, hs, _, _, AFF, INts, HEP, NE⟩ := key cpu hsub
    simp only [hs, Option.map_some, Option.getD_some]
    rw [List.mem_toFinset, List.mem_filter, List.mem_filter]
    refine ⟨⟨INts, hp_task_in_of_cpu alpha higher_eq_priority tsk _ _ cpu hcpu.2 AFF HEP NE⟩, ?_⟩
    simp only [task_scheduled_on_affinity, List.any_eq_true]
    exact ⟨cpu, List.mem_finRange _, by simp [hsub, task_scheduled_on, hs]⟩
  calc (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card
      = ((Finset.univ.filter (fun x => x ∈ alpha' tsk)).image
          (fun cpu => ((sched cpu t).map job_task).getD tsk)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card himg
    _ ≤ _ := List.toFinset_card_le _
    _ = _ := List.countP_eq_length_filter.symm

theorem bertogna_fp_interference_in_non_full_processors
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_respects_affinity : respects_affinity job_task sched alpha)
    (H_work_conserving :
      apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
    (H_respects_FP_policy :
      respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched alpha
        higher_eq_priority)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (alpha' : task_affinity sporadic_task num_cpus)
    (H_affinity_subset :
      ∀ tsk : sporadic_task, tsk ∈ ts → is_subaffinity (alpha' tsk) (alpha tsk))
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds →
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_interfering_tasks_miss_no_deadlines :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time)
    (H_response_time_recurrence_holds :
      R = task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period alpha tsk (alpha' tsk)
          hp_bounds R higher_eq_priority) (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed :
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) :
    ∀ delta : time,
      (decide (0 < (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task sched alpha j i (job_arrival j) (job_arrival j + R)))) && decide ((ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task sched alpha j i (job_arrival j) (job_arrival j + R))) < (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)) = true →
      delta * ((Finset.univ.filter (fun x => x ∈ alpha' tsk)).card - (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task sched alpha j i (job_arrival j) (job_arrival j + R)))) ≤
        sumFiltered (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)) (fun i => decide (task_interference job_arrival job_cost job_task sched alpha j i (job_arrival j) (job_arrival j + R) < delta)) (fun i => task_interference job_arrival job_cost job_task sched alpha j i (job_arrival j) (job_arrival j + R)) := by
  intro delta HAS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at HAS
  have hHnd : ((ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))).Nodup := ts.nodup.filter _
  have INV := bertogna_fp_alpha'_is_full task_cost task_period task_deadline job_arrival
    job_cost job_task arr_seq H_sporadic_tasks ts H_valid_task_parameters H_constrained_deadlines
    H_all_jobs_from_taskset alpha sched H_jobs_come_from_arrival_sequence H_sequential_jobs
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority
    H_respects_affinity H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
    H_affinity_subset hp_bounds H_response_time_of_interfering_tasks_is_known
    H_hp_bounds_has_interfering_tasks H_interfering_tasks_miss_no_deadlines R
    H_response_time_recurrence_holds H_response_time_no_larger_than_deadline j H_j_arrives
    H_job_of_tsk H_previous_jobs_of_tsk_completed
  have PREVhp := bertogna_fp_previous_interfering_jobs_complete_by_their_period task_period
    task_deadline job_arrival job_cost job_task arr_seq ts H_constrained_deadlines
    H_all_jobs_from_taskset alpha sched higher_eq_priority tsk hp_bounds
    H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
    H_interfering_tasks_miss_no_deadlines
  refine interference_in_non_full_processors_core
    (Finset.Ico (job_arrival j) (job_arrival j + R))
    (fun t => backlogged job_arrival job_cost sched j t)
    (fun k cpu t => decide (cpu ∈ alpha tsk) && task_scheduled_on job_task sched k cpu t)
    (fun k => task_interference job_arrival job_cost job_task sched alpha j k (job_arrival j) (job_arrival j + R)) ?_ (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)) hHnd ?_ (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card ?_ delta HAS.1 HAS.2
  · intro k
    unfold task_interference
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro cpu _
    simp only [can_execute_on, H_job_of_tsk, Bool.and_assoc]
  · intro k hk t _ _ c1 c2 h1 h2
    simp only [Bool.and_eq_true, decide_eq_true_eq, task_scheduled_on] at h1 h2
    obtain ⟨hc1, h1⟩ := h1
    obtain ⟨hc2, h2⟩ := h2
    rw [List.mem_filter] at hk
    have hk2 := hk.2
    simp only [higher_priority_task_in, Bool.and_eq_true] at hk2
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
        have AFF1 : c1 ∈ alpha (job_task j1) := by
          have := H_respects_affinity j1 c1 t (by simp [scheduled_on, hs1])
          simpa [can_execute_on] using this
        rw [h1] at AFF1
        have HP1 : higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk)
            (job_task j1) = true := by
          rw [h1]
          exact hp_task_in_of_cpu alpha higher_eq_priority tsk _ _ c1 hc1 AFF1 hk2.1.1 hk2.1.2
        have EQ : j1 = j2 := platform_fp_no_multiple_jobs_of_interfering_tasks task_period
          job_arrival job_cost job_task arr_seq sched alpha higher_eq_priority H_sporadic_tasks
          tsk t (fun jo ko A T HP => by subst T; exact PREVhp jo A HP) j1 j2
          (H_jobs_come_from_arrival_sequence j1 t SCHED1)
          (H_jobs_come_from_arrival_sequence j2 t SCHED2)
          (scheduled_implies_pending job_arrival job_cost sched j1 H_jobs_must_arrive_to_execute
            H_completed_jobs_dont_execute t SCHED1)
          (scheduled_implies_pending job_arrival job_cost sched j2 H_jobs_must_arrive_to_execute
            H_completed_jobs_dont_execute t SCHED2)
          (h1.trans h2.symm) HP1
        subst EQ
        exact H_sequential_jobs j1 t c1 c2 hs1 hs2
  · intro t ht hb
    rw [Finset.mem_Ico] at ht
    exact INV t (by simp [ht.1, ht.2]) hb

theorem bertogna_fp_minimum_exceeds_interference
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_respects_affinity : respects_affinity job_task sched alpha)
    (H_work_conserving :
      apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
    (H_respects_FP_policy :
      respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched alpha
        higher_eq_priority)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (alpha' : task_affinity sporadic_task num_cpus)
    (H_affinity_subset :
      ∀ tsk : sporadic_task, tsk ∈ ts → is_subaffinity (alpha' tsk) (alpha tsk))
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds →
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_interfering_tasks_miss_no_deadlines :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time)
    (H_response_time_recurrence_holds :
      R = task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period alpha tsk (alpha' tsk)
          hp_bounds R higher_eq_priority) (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed :
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) :
    ∀ delta : time,
      delta * (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card ≤ sumSeq (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task sched alpha j tsk_k (job_arrival j) (job_arrival j + R)) →
      delta * (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card ≤ sumSeq (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)) (fun tsk_k => min (task_interference job_arrival job_cost job_task sched alpha j tsk_k (job_arrival j) (job_arrival j + R)) delta) := by
  intro delta SUMLESS
  rw [sum_min_split (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task sched alpha j tsk_k (job_arrival j) (job_arrival j + R)) delta]
  by_cases hN0 : (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task sched alpha j i (job_arrival j) (job_arrival j + R))) = 0
  · have hall : sumFiltered (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)) (fun i => decide (task_interference job_arrival job_cost job_task sched alpha j i (job_arrival j) (job_arrival j + R) < delta)) (fun i => task_interference job_arrival job_cost job_task sched alpha j i (job_arrival j) (job_arrival j + R)) =
        sumSeq (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task sched alpha j tsk_k (job_arrival j) (job_arrival j + R)) := by
      unfold sumFiltered sumSeq
      congr 2
      apply List.filter_eq_self.mpr
      intro k hk
      have := List.countP_eq_zero.mp hN0 k hk
      simp only [decide_eq_true_eq, Nat.not_le] at this
      simpa using this
    rw [hall, hN0]
    omega'
  · by_cases hNm : (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card ≤ (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task sched alpha j i (job_arrival j) (job_arrival j + R)))
    · have := Nat.mul_le_mul_left delta hNm
      omega'
    · have NONFULL := bertogna_fp_interference_in_non_full_processors task_cost task_period
        task_deadline job_arrival job_cost job_task arr_seq H_sporadic_tasks ts
        H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset alpha sched
        H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity H_work_conserving
        H_respects_FP_policy tsk task_in_ts alpha' H_affinity_subset hp_bounds
        H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
        H_interfering_tasks_miss_no_deadlines R H_response_time_recurrence_holds
        H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk
        H_previous_jobs_of_tsk_completed delta
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
      have e : delta * (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task sched alpha j i (job_arrival j) (job_arrival j + R))) + delta * ((Finset.univ.filter (fun x => x ∈ alpha' tsk)).card - (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)).countP (fun i => decide (delta ≤ task_interference job_arrival job_cost job_task sched alpha j i (job_arrival j) (job_arrival j + R)))) = delta * (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card := by
        rw [← Nat.mul_add]
        congr 1
        omega'
      omega'

theorem bertogna_fp_interference_on_subaffinity
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_respects_affinity : respects_affinity job_task sched alpha)
    (H_work_conserving :
      apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
    (H_respects_FP_policy :
      respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched alpha
        higher_eq_priority)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (alpha' : task_affinity sporadic_task num_cpus)
    (H_affinity_subset :
      ∀ tsk : sporadic_task, tsk ∈ ts → is_subaffinity (alpha' tsk) (alpha tsk))
    (H_at_least_one_cpu :
      ∀ tsk : sporadic_task, tsk ∈ ts → 0 < (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (hp_bounds : List (sporadic_task × time))
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (R : time)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed :
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) :
    ∀ delta : time,
      delta * (Finset.univ.filter (fun x => x ∈ alpha tsk)).card ≤ sumSeq (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task sched alpha j tsk_k (job_arrival j) (job_arrival j + R)) →
      delta * (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card ≤ sumSeq (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task sched alpha j tsk_k (job_arrival j) (job_arrival j + R)) := by
  intro delta LE
  have ALL := bertogna_fp_all_cpus_in_affinity_busy task_cost task_period task_deadline
    job_arrival job_cost job_task arr_seq H_sporadic_tasks ts H_valid_task_parameters
    H_constrained_deadlines H_all_jobs_from_taskset alpha sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority
    H_respects_affinity H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
    H_affinity_subset H_at_least_one_cpu hp_bounds H_hp_bounds_has_interfering_tasks R
    H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk
    H_previous_jobs_of_tsk_completed
  have SUB := bertogna_fp_all_cpus_in_subaffinity_busy task_cost task_period task_deadline
    job_arrival job_cost job_task arr_seq H_sporadic_tasks ts H_valid_task_parameters
    H_constrained_deadlines H_all_jobs_from_taskset alpha sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority
    H_respects_affinity H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
    H_affinity_subset H_at_least_one_cpu hp_bounds H_hp_bounds_has_interfering_tasks R
    H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk
    H_previous_jobs_of_tsk_completed
  rw [ALL] at LE
  have hpos' := H_at_least_one_cpu tsk task_in_ts
  have hle := leq_subaffinity (alpha' tsk) (alpha tsk) (H_affinity_subset tsk task_in_ts)
  have hδ : delta ≤ total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R) := Nat.le_of_mul_le_mul_right LE (Nat.lt_of_lt_of_le hpos' hle)
  exact Nat.le_trans (Nat.mul_le_mul_right _ hδ) SUB

theorem bertogna_fp_sum_exceeds_total_interference
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_respects_affinity : respects_affinity job_task sched alpha)
    (H_work_conserving :
      apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
    (H_respects_FP_policy :
      respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched alpha
        higher_eq_priority)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (alpha' : task_affinity sporadic_task num_cpus)
    (H_affinity_subset :
      ∀ tsk : sporadic_task, tsk ∈ ts → is_subaffinity (alpha' tsk) (alpha tsk))
    (H_at_least_one_cpu :
      ∀ tsk : sporadic_task, tsk ∈ ts → 0 < (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds →
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_interfering_tasks_miss_no_deadlines :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time)
    (H_response_time_recurrence_holds :
      R = task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period alpha tsk (alpha' tsk)
          hp_bounds R higher_eq_priority) (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true)
    (H_previous_jobs_of_tsk_completed :
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) :
    total_interference_bound_fp task_cost task_period alpha tsk (alpha' tsk) hp_bounds R
        higher_eq_priority <
      sumFiltered hp_bounds
        (fun (tsk_other, _R_other) =>
          higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)
        (fun (tsk_other, R_other) => min (task_interference job_arrival job_cost job_task sched alpha j tsk_other (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1)) := by
  have EXCEEDS := bertogna_fp_minimum_exceeds_interference task_cost task_period task_deadline
    job_arrival job_cost job_task arr_seq H_sporadic_tasks ts H_valid_task_parameters
    H_constrained_deadlines H_all_jobs_from_taskset alpha sched
    H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity H_work_conserving
    H_respects_FP_policy tsk task_in_ts alpha' H_affinity_subset hp_bounds
    H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
    H_interfering_tasks_miss_no_deadlines R H_response_time_recurrence_holds
    H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk
    H_previous_jobs_of_tsk_completed
  have SUBAFF := bertogna_fp_interference_on_subaffinity task_cost task_period task_deadline
    job_arrival job_cost job_task arr_seq H_sporadic_tasks ts H_valid_task_parameters
    H_constrained_deadlines H_all_jobs_from_taskset alpha sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority
    H_respects_affinity H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
    H_affinity_subset H_at_least_one_cpu hp_bounds H_hp_bounds_has_interfering_tasks R
    H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk
    H_previous_jobs_of_tsk_completed
  have ALLBUSY := bertogna_fp_all_cpus_in_affinity_busy task_cost task_period task_deadline
    job_arrival job_cost job_task arr_seq H_sporadic_tasks ts H_valid_task_parameters
    H_constrained_deadlines H_all_jobs_from_taskset alpha sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority
    H_respects_affinity H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
    H_affinity_subset H_at_least_one_cpu hp_bounds H_hp_bounds_has_interfering_tasks R
    H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk
    H_previous_jobs_of_tsk_completed
  have TOOMUCH := bertogna_fp_too_much_interference task_cost task_period task_deadline
    job_arrival job_cost job_deadline job_task arr_seq H_valid_job_parameters alpha sched
    H_jobs_must_arrive_to_execute higher_eq_priority tsk alpha' hp_bounds R
    H_response_time_recurrence_holds j H_j_arrives H_job_of_tsk H_j_not_completed
  have hHnd : ((ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))).Nodup := ts.nodup.filter _
  have hpos' := H_at_least_one_cpu tsk task_in_ts
  have hsub : sumSeq (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)) (fun tsk_k => min (task_interference job_arrival job_cost job_task sched alpha j tsk_k (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1)) ≤
      sumFiltered hp_bounds
        (fun (tsk_other, _R_other) =>
          higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)
        (fun (tsk_other, R_other) => min (task_interference job_arrival job_cost job_task sched alpha j tsk_other (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1)) := by
    have := Prosa.Classic.Util.Sum.leq_sum_sub_uniq _ (ts.val.filter (fun tsk_other =>
        higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other))
      ((hp_bounds.filter (fun (tsk_other, _R_other) =>
          higher_priority_task_in alpha higher_eq_priority tsk (alpha' tsk) tsk_other)).map
        Prod.fst)
      (fun tsk_k => min (task_interference job_arrival job_cost job_task sched alpha j tsk_k (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1)) hHnd (by
        intro k hk
        rw [List.mem_filter] at hk
        have hk2 := hk.2
        have HPk : higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) k = true := by
          simp only [higher_priority_task_in, affinity_intersects, Bool.and_eq_true,
            List.any_eq_true, decide_eq_true_eq] at hk2 ⊢
          obtain ⟨hhp, cpu, _, hc, hc'⟩ := hk2
          exact ⟨hhp, cpu, List.mem_finRange _, H_affinity_subset tsk task_in_ts cpu hc, hc'⟩
        obtain ⟨R0, hR0⟩ := H_hp_bounds_has_interfering_tasks k hk.1 HPk
        exact List.mem_map.mpr ⟨(k, R0), List.mem_filter.mpr ⟨hR0, hk2⟩, rfl⟩)
    refine le_trans this (le_of_eq ?_)
    unfold sumSeq sumFiltered
    rw [List.map_map]
    rfl
  have REC := H_response_time_recurrence_holds
  unfold div_floor at REC
  apply ltn_div_trunc _ _ _ hpos'
  have hdiv : total_interference_bound_fp task_cost task_period alpha tsk (alpha' tsk) hp_bounds
      R higher_eq_priority / (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card = R - task_cost tsk := by omega'
  rw [hdiv]
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
  rw [Nat.le_div_iff_mul_le hpos']
  refine le_trans ?_ hsub
  apply EXCEEDS
  apply SUBAFF
  rw [ALLBUSY]
  exact Nat.mul_le_mul_right _ TOOMUCH

theorem bertogna_fp_exists_task_that_exceeds_bound
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_respects_affinity : respects_affinity job_task sched alpha)
    (H_work_conserving :
      apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
    (H_respects_FP_policy :
      respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched alpha
        higher_eq_priority)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (alpha' : task_affinity sporadic_task num_cpus)
    (H_affinity_subset :
      ∀ tsk : sporadic_task, tsk ∈ ts → is_subaffinity (alpha' tsk) (alpha tsk))
    (H_at_least_one_cpu :
      ∀ tsk : sporadic_task, tsk ∈ ts → 0 < (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds →
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_interfering_tasks_miss_no_deadlines :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time)
    (H_response_time_recurrence_holds :
      R = task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period alpha tsk (alpha' tsk)
          hp_bounds R higher_eq_priority) (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true)
    (H_previous_jobs_of_tsk_completed :
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) :
    ∃ (tsk_k : sporadic_task) (R_k : time),
      (tsk_k, R_k) ∈ hp_bounds ∧
      min (W task_cost task_period tsk_k R_k R) (R - task_cost tsk + 1) <
        min (task_interference job_arrival job_cost job_task sched alpha j tsk_k (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1) := by
  have SUM := bertogna_fp_sum_exceeds_total_interference task_cost task_period task_deadline
    job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts
    H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset alpha sched
    H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute higher_eq_priority H_respects_affinity H_work_conserving
    H_respects_FP_policy tsk task_in_ts alpha' H_affinity_subset H_at_least_one_cpu hp_bounds
    H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
    H_interfering_tasks_miss_no_deadlines R H_response_time_recurrence_holds
    H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk H_j_not_completed
    H_previous_jobs_of_tsk_completed
  by_contra NOT
  simp only [not_exists, not_and, Nat.not_lt] at NOT
  apply absurd SUM
  apply Nat.not_lt.mpr
  unfold total_interference_bound_fp sumFiltered
  apply List.sum_le_sum
  rintro ⟨k, Rk⟩ hk
  rw [List.mem_filter] at hk
  simp only [interference_bound_generic]
  exact NOT k Rk hk.1

/-! ### Main theorem -/

theorem bertogna_cirinei_response_time_bound_fp
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_respects_affinity : respects_affinity job_task sched alpha)
    (H_work_conserving :
      apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
    (H_respects_FP_policy :
      respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq sched alpha
        higher_eq_priority)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (alpha' : task_affinity sporadic_task num_cpus)
    (H_affinity_subset :
      ∀ tsk : sporadic_task, tsk ∈ ts → is_subaffinity (alpha' tsk) (alpha tsk))
    (H_at_least_one_cpu :
      ∀ tsk : sporadic_task, tsk ∈ ts → 0 < (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds →
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_response_time_bounds_ge_cost :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds → task_cost hp_tsk ≤ R)
    (H_interfering_tasks_miss_no_deadlines :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time)
    (H_response_time_recurrence_holds :
      R = task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period alpha tsk (alpha' tsk)
          hp_bounds R higher_eq_priority) (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  suffices MAIN : ∀ (n : Nat) (j : Job), job_arrival j = n → arrives_in arr_seq j →
      job_task j = tsk → completed job_cost sched j (job_arrival j + R) = true by
    intro j ARRj JOBtsk
    exact MAIN _ j rfl ARRj JOBtsk
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro j hn ARRj JOBtsk
    by_contra NOTCOMP
    have NOTCOMP' : (!completed job_cost sched j (job_arrival j + R)) = true := by
      simpa using NOTCOMP
    have BEFOREok : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true :=
      fun j0 ARR0 JOB0 LT0 => IH (job_arrival j0) (hn ▸ LT0) j0 rfl ARR0 JOB0
    obtain ⟨tsk_k, R_k, HPk, LTmin⟩ := bertogna_fp_exists_task_that_exceeds_bound task_cost
      task_period task_deadline job_arrival job_cost job_deadline job_task arr_seq
      H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
      H_all_jobs_from_taskset alpha sched H_jobs_come_from_arrival_sequence H_sequential_jobs
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority
      H_respects_affinity H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
      H_affinity_subset H_at_least_one_cpu hp_bounds
      H_response_time_of_interfering_tasks_is_known H_hp_bounds_has_interfering_tasks
      H_interfering_tasks_miss_no_deadlines R H_response_time_recurrence_holds
      H_response_time_no_larger_than_deadline j ARRj JOBtsk NOTCOMP' BEFOREok
    have WORKLOAD := bertogna_fp_workload_bounds_interference task_cost task_period
      task_deadline job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks
      H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
      H_all_jobs_from_taskset alpha sched H_jobs_come_from_arrival_sequence H_sequential_jobs
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute hp_bounds
      H_response_time_of_interfering_tasks_is_known H_response_time_bounds_ge_cost
      H_interfering_tasks_miss_no_deadlines R j tsk_k R_k HPk
    exact absurd LTmin (Nat.not_lt.mpr (min_le_min_right _ WORKLOAD))

end Prosa.Classic.Analysis.Apa.BertognaFpTheory.ResponseTimeAnalysisFP
