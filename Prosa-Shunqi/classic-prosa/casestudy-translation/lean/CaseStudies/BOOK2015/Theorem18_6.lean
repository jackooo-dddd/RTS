-- Case study: RTS_Papers/2015-book-Theorem18_6/Theorem18_6.v
-- (Baruah, Bertogna & Buttazzo, Multiprocessor Scheduling for Real-Time Systems (2015), Theorem 18.6);
-- sha256 and elaborated contract: classic-prosa/casestudy-translation/contracts/
import Prosa.Util.Sum
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task

/-!
Theorem 18.6 of Baruah, Bertogna & Buttazzo, *Multiprocessor Scheduling for Real-Time Systems* (2015), as stated
by the case study `2015-book-Theorem18_6` (Rocq section `Theorem18_6_Model`): for a task set of at most `2m`
tasks, indexed by decreasing fixed priority, the fixed-priority response-time analyses of Theorem 18.4
(recurrence `ftp_rta_recurrence_18_4`) and Theorem 18.5 (`ftp_rta_recurrence_18_5`, which adds only the `m - 1`
largest carry-in differences) return the same upper bound for every task.  The bounds returned by each analysis
are modelled by the mutually inductive `returned_bound_by_18_x` / `analysis_prefix_18_x`: an analysis prefix
stores the bounds already returned for the higher-priority tasks, and a returned bound is a fixed point reached
by iterating the recurrence from the task's cost.  Lemma 18.1 (the `m` highest-priority tasks get their cost as
bound under both analyses) is a hypothesis.

Representation notes: `minn` is `min`; `x %/ y` is `x / y` and `x %% y` is `x % y`; `\sum_(x <- s) F x` is
`sumSeq s F`; `nth default_task ts k` is `ts.val.getD k default_task`; `take k ts` is `ts.val.take k`;
`size ts` is `ts.val.length`; `n.-1` is `n - 1`; `n.*2` is `2 * n`; `iter n f x` is `f^[n] x`;
`sort geq s` is `s.mergeSort (fun x y => decide (y ≤ x))`; `rcons s x` is `s ++ [x]`; `tsk == tsk'` is
`decide (tsk = tsk')`; Boolean-valued definitions (`ftp_bcl_test_18_2`, `ftp_rta_interference_test_18_3`,
`at_most_two_m_tasks`) are `Bool`s and are `= true` in proposition position.  Binder lists follow the Rocq
contract (each definition abstracts the section variables it uses, the theorem every variable and hypothesis
declared before it).
-/

set_option linter.unusedVariables false
-- the case study names its file and its theorem `Theorem18_6`
set_option linter.dupNamespace false

namespace CaseStudies.BOOK2015.Theorem18_6

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Util.Sum (sumSeq)

universe u

def task_at {sporadic_task : Type u} [DecidableEq sporadic_task] (ts : taskset_of sporadic_task)
    (default_task : sporadic_task) (k : Nat) : sporadic_task :=
  ts.val.getD k default_task

def higher_priority_tasks_of {sporadic_task : Type u} [DecidableEq sporadic_task]
    (ts : taskset_of sporadic_task) (k : Nat) : List sporadic_task :=
  ts.val.take k

def lower_priority_tasks_do_not_interfere {sporadic_task : Type u} [DecidableEq sporadic_task]
    (ts : taskset_of sporadic_task) (default_task : sporadic_task)
    (ftp_interference : sporadic_task → sporadic_task → time → time) : Prop :=
  ∀ (i k : Nat) (R : time), k < ts.val.length → i < ts.val.length → k < i →
    ftp_interference (task_at ts default_task i) (task_at ts default_task k) R = 0

def ftp_total_interference_18_1 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (ts : taskset_of sporadic_task) (default_task : sporadic_task) (num_cpus : Nat)
    (ftp_interference : sporadic_task → sporadic_task → time → time) (k R : time) : Nat :=
  sumSeq (higher_priority_tasks_of ts k)
    (fun hp_tsk => ftp_interference hp_tsk (task_at ts default_task k) R) / num_cpus

def generic_workload_bound_17_3 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (Rub_i L : time) : Nat :=
  let C := task_cost tsk
  let T := task_period tsk
  ((L + Rub_i - C) / T) * C + min C ((L + Rub_i - C) % T)

def ftp_bcl_workload_bound_18_2 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) (hp_tsk tsk : sporadic_task) : Nat :=
  let C := task_cost hp_tsk
  let T := task_period hp_tsk
  let D := task_deadline hp_tsk
  let Dk := task_deadline tsk
  ((Dk + D - C) / T) * C + min C ((Dk + D - C) % T)

def ftp_bcl_test_18_2 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) (ts : taskset_of sporadic_task)
    (default_task : sporadic_task) (num_cpus k : Nat) : Bool :=
  let tsk := task_at ts default_task k
  decide (sumSeq (higher_priority_tasks_of ts k)
      (fun hp_tsk => min (task_deadline tsk - task_cost tsk)
        (ftp_bcl_workload_bound_18_2 task_cost task_period task_deadline hp_tsk tsk)) <
    num_cpus * (task_deadline tsk - task_cost tsk))

def ftp_rta_interference_test_18_3 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time) (ts : taskset_of sporadic_task) (default_task : sporadic_task)
    (num_cpus : Nat) (ftp_interference : sporadic_task → sporadic_task → time → time) (k : Nat)
    (Rub_k : time) : Bool :=
  let tsk := task_at ts default_task k
  decide (sumSeq (higher_priority_tasks_of ts k)
      (fun hp_tsk => min (ftp_interference hp_tsk tsk Rub_k) (Rub_k - task_cost tsk + 1)) <
    num_cpus * (Rub_k - task_cost tsk + 1))

abbrev hp_response_bounds (sporadic_task : Type u) [DecidableEq sporadic_task] : Type u :=
  List (sporadic_task × time)

def response_bound_of {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time) : hp_response_bounds sporadic_task → sporadic_task → time
  | (tsk', R) :: hp_bounds', tsk =>
      if decide (tsk = tsk') then R else response_bound_of task_cost hp_bounds' tsk
  | [], tsk => task_cost tsk

def ftp_rta_recurrence_18_4 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (ts : taskset_of sporadic_task)
    (default_task : sporadic_task) (num_cpus : Nat) (hp_bounds : hp_response_bounds sporadic_task)
    (k : Nat) (Rub_k : time) : Nat :=
  let tsk := task_at ts default_task k
  task_cost tsk +
    sumSeq (higher_priority_tasks_of ts k)
      (fun hp_tsk => min (generic_workload_bound_17_3 task_cost task_period hp_tsk
        (response_bound_of task_cost hp_bounds hp_tsk) Rub_k) (Rub_k - task_cost tsk + 1)) / num_cpus

def iterate_18_4 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (ts : taskset_of sporadic_task)
    (default_task : sporadic_task) (num_cpus : Nat) (hp_bounds : hp_response_bounds sporadic_task)
    (k steps : Nat) : time :=
  (ftp_rta_recurrence_18_4 task_cost task_period ts default_task num_cpus hp_bounds k)^[steps]
    (task_cost (task_at ts default_task k))

def carry_in_workload_17_7 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (hp_bounds : hp_response_bounds sporadic_task)
    (hp_tsk tsk : sporadic_task) (L : time) : Nat :=
  min (generic_workload_bound_17_3 task_cost task_period hp_tsk (response_bound_of task_cost hp_bounds hp_tsk) L)
    (L - task_cost tsk + 1)

def non_carry_in_workload_17_8 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (hp_tsk tsk : sporadic_task) (L : time) : Nat :=
  let C := task_cost hp_tsk
  let T := task_period hp_tsk
  min ((L / T) * C + min C (L % T)) (L - task_cost tsk + 1)

def carry_in_difference_17_9 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (hp_bounds : hp_response_bounds sporadic_task)
    (hp_tsk tsk : sporadic_task) (L : time) : Nat :=
  carry_in_workload_17_7 task_cost task_period hp_bounds hp_tsk tsk L -
    non_carry_in_workload_17_8 task_cost task_period hp_tsk tsk L

def largest_carry_in_differences {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (ts : taskset_of sporadic_task)
    (default_task : sporadic_task) (num_cpus : Nat) (hp_bounds : hp_response_bounds sporadic_task)
    (k : Nat) (L : time) : List Nat :=
  let tsk := task_at ts default_task k
  let deltas := (higher_priority_tasks_of ts k).map
    (fun hp_tsk => carry_in_difference_17_9 task_cost task_period hp_bounds hp_tsk tsk L)
  (deltas.mergeSort (fun x y => decide (y ≤ x))).take (num_cpus - 1)

def ftp_rta_recurrence_18_5 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (ts : taskset_of sporadic_task)
    (default_task : sporadic_task) (num_cpus : Nat) (hp_bounds : hp_response_bounds sporadic_task)
    (k : Nat) (Rub_k : time) : Nat :=
  let tsk := task_at ts default_task k
  task_cost tsk +
    (sumSeq (higher_priority_tasks_of ts k)
        (fun hp_tsk => non_carry_in_workload_17_8 task_cost task_period hp_tsk tsk Rub_k) +
      sumSeq (largest_carry_in_differences task_cost task_period ts default_task num_cpus hp_bounds k Rub_k)
        (fun delta => delta)) / num_cpus

def iterate_18_5 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (ts : taskset_of sporadic_task)
    (default_task : sporadic_task) (num_cpus : Nat) (hp_bounds : hp_response_bounds sporadic_task)
    (k steps : Nat) : time :=
  (ftp_rta_recurrence_18_5 task_cost task_period ts default_task num_cpus hp_bounds k)^[steps]
    (task_cost (task_at ts default_task k))

mutual
inductive returned_bound_by_18_4 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (ts : taskset_of sporadic_task)
    (default_task : sporadic_task) (num_cpus : Nat) : Nat → time → Prop
  | ReturnedBound18_4 : ∀ (k : Nat) (hp_bounds : hp_response_bounds sporadic_task) (steps : Nat) (Rub_k : time),
      analysis_prefix_18_4 task_cost task_period ts default_task num_cpus k hp_bounds →
      Rub_k = iterate_18_4 task_cost task_period ts default_task num_cpus hp_bounds k steps →
      ftp_rta_recurrence_18_4 task_cost task_period ts default_task num_cpus hp_bounds k Rub_k = Rub_k →
      returned_bound_by_18_4 task_cost task_period ts default_task num_cpus k Rub_k

inductive analysis_prefix_18_4 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (ts : taskset_of sporadic_task)
    (default_task : sporadic_task) (num_cpus : Nat) : Nat → hp_response_bounds sporadic_task → Prop
  | AnalysisPrefix18_4_nil : analysis_prefix_18_4 task_cost task_period ts default_task num_cpus 0 []
  | AnalysisPrefix18_4_rcons : ∀ (k : Nat) (hp_bounds : hp_response_bounds sporadic_task) (Rub_k : time),
      analysis_prefix_18_4 task_cost task_period ts default_task num_cpus k hp_bounds →
      returned_bound_by_18_4 task_cost task_period ts default_task num_cpus k Rub_k →
      analysis_prefix_18_4 task_cost task_period ts default_task num_cpus (k + 1)
        (hp_bounds ++ [(task_at ts default_task k, Rub_k)])
end

mutual
inductive returned_bound_by_18_5 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (ts : taskset_of sporadic_task)
    (default_task : sporadic_task) (num_cpus : Nat) : Nat → time → Prop
  | ReturnedBound18_5 : ∀ (k : Nat) (hp_bounds : hp_response_bounds sporadic_task) (steps : Nat) (Rub_k : time),
      analysis_prefix_18_5 task_cost task_period ts default_task num_cpus k hp_bounds →
      Rub_k = iterate_18_5 task_cost task_period ts default_task num_cpus hp_bounds k steps →
      ftp_rta_recurrence_18_5 task_cost task_period ts default_task num_cpus hp_bounds k Rub_k = Rub_k →
      returned_bound_by_18_5 task_cost task_period ts default_task num_cpus k Rub_k

inductive analysis_prefix_18_5 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (ts : taskset_of sporadic_task)
    (default_task : sporadic_task) (num_cpus : Nat) : Nat → hp_response_bounds sporadic_task → Prop
  | AnalysisPrefix18_5_nil : analysis_prefix_18_5 task_cost task_period ts default_task num_cpus 0 []
  | AnalysisPrefix18_5_rcons : ∀ (k : Nat) (hp_bounds : hp_response_bounds sporadic_task) (Rub_k : time),
      analysis_prefix_18_5 task_cost task_period ts default_task num_cpus k hp_bounds →
      returned_bound_by_18_5 task_cost task_period ts default_task num_cpus k Rub_k →
      analysis_prefix_18_5 task_cost task_period ts default_task num_cpus (k + 1)
        (hp_bounds ++ [(task_at ts default_task k, Rub_k)])
end

def at_most_two_m_tasks {sporadic_task : Type u} [DecidableEq sporadic_task]
    (ts : taskset_of sporadic_task) (num_cpus : Nat) : Bool :=
  decide (ts.val.length ≤ 2 * num_cpus)

def theorems_18_4_and_18_5_are_equivalent {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (ts : taskset_of sporadic_task)
    (default_task : sporadic_task) (num_cpus : Nat) : Prop :=
  ∀ (k : Nat) (Rub_k : time), k < ts.val.length →
    (returned_bound_by_18_4 task_cost task_period ts default_task num_cpus k Rub_k ↔
      returned_bound_by_18_5 task_cost task_period ts default_task num_cpus k Rub_k)

theorem Theorem18_6 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time) (ts : taskset_of sporadic_task)
    (default_task : sporadic_task) (num_cpus : Nat)
    (H_num_cpus_positive : 0 < num_cpus)
    (H_valid_taskset : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines : ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (ftp_interference : sporadic_task → sporadic_task → time → time)
    (Lemma18_1 : ∀ k : Nat, k < min num_cpus ts.val.length →
      returned_bound_by_18_4 task_cost task_period ts default_task num_cpus k
          (task_cost (task_at ts default_task k)) ∧
        returned_bound_by_18_5 task_cost task_period ts default_task num_cpus k
          (task_cost (task_at ts default_task k))) :
    at_most_two_m_tasks ts num_cpus = true →
      theorems_18_4_and_18_5_are_equivalent task_cost task_period ts default_task num_cpus := by
  intro H2m
  have h2m : ts.val.length ≤ 2 * num_cpus := by simpa [at_most_two_m_tasks] using H2m
  -- tasks by index
  have tget : ∀ i (h : i < ts.val.length), task_at ts default_task i = ts.val[i] := by
    intro i h
    simp [task_at, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  have tinj : ∀ i j, i < ts.val.length → j < ts.val.length →
      task_at ts default_task i = task_at ts default_task j → i = j := by
    intro i j hi hj h
    rw [tget i hi, tget j hj] at h
    exact (ts.nodup.getElem_inj_iff).mp h
  -- looking up a bound in a prefix extended at the end
  have lookup_append : ∀ (l : hp_response_bounds sporadic_task) (a : sporadic_task) (b : time) (x : sporadic_task),
      response_bound_of task_cost (l ++ [(a, b)]) x =
        if x ∈ l.map Prod.fst then response_bound_of task_cost l x else if x = a then b else task_cost x := by
    intro l
    induction l with
    | nil => intro a b x; by_cases hx : x = a <;> simp [response_bound_of, hx]
    | cons p l ih =>
        intro a b x
        obtain ⟨c, r⟩ := p
        by_cases hx : x = c
        · simp [response_bound_of, hx]
        · simp only [List.cons_append, response_bound_of, hx, decide_false, Bool.false_eq_true, if_false,
            List.map_cons, List.mem_cons, false_or]
          exact ih a b x
  -- the tasks stored in a prefix of analysis 18.4
  have keys : ∀ k hp, analysis_prefix_18_4 task_cost task_period ts default_task num_cpus k hp →
      hp.map Prod.fst = (List.range k).map (task_at ts default_task) := by
    intro k
    induction k with
    | zero => intro hp h; cases h; rfl
    | succ k ih =>
        intro hp h
        cases h with
        | AnalysisPrefix18_4_rcons _ hp0 R h0 hr =>
            rw [List.map_append, ih hp0 h0, List.range_succ, List.map_append]
            rfl
  -- a fixed point reached by iterating from the same start is unique
  have fix_uniq : ∀ (f : Nat → Nat) (c s s' : Nat), f (f^[s] c) = f^[s] c → f (f^[s'] c) = f^[s'] c →
      f^[s] c = f^[s'] c := by
    intro f c s s' h h'
    rcases Nat.le_total s s' with hle | hle
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [Nat.add_comm s d, Function.iterate_add_apply, Function.iterate_fixed h]
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [Nat.add_comm s' d, Function.iterate_add_apply, Function.iterate_fixed h']
  -- analysis 18.4 returns at most one bound per task
  have rb_of_prefix : ∀ k, (∀ hp hp', analysis_prefix_18_4 task_cost task_period ts default_task num_cpus k hp →
      analysis_prefix_18_4 task_cost task_period ts default_task num_cpus k hp' → hp = hp') →
      ∀ R R', returned_bound_by_18_4 task_cost task_period ts default_task num_cpus k R →
        returned_bound_by_18_4 task_cost task_period ts default_task num_cpus k R' → R = R' := by
    intro k hpu R R' h h'
    cases h with
    | ReturnedBound18_4 _ hp s _ hpre hR hfix =>
      cases h' with
      | ReturnedBound18_4 _ hp' s' _ hpre' hR' hfix' =>
        obtain rfl := hpu hp hp' hpre hpre'
        subst hR; subst hR'
        exact fix_uniq _ _ s s' hfix hfix'
  have uniq : ∀ k, (∀ hp hp', analysis_prefix_18_4 task_cost task_period ts default_task num_cpus k hp →
      analysis_prefix_18_4 task_cost task_period ts default_task num_cpus k hp' → hp = hp') ∧
      (∀ R R', returned_bound_by_18_4 task_cost task_period ts default_task num_cpus k R →
        returned_bound_by_18_4 task_cost task_period ts default_task num_cpus k R' → R = R') := by
    intro k
    induction k with
    | zero =>
        have hp0 : ∀ hp hp', analysis_prefix_18_4 task_cost task_period ts default_task num_cpus 0 hp →
            analysis_prefix_18_4 task_cost task_period ts default_task num_cpus 0 hp' → hp = hp' := by
          intro hp hp' h h'; cases h; cases h'; rfl
        exact ⟨hp0, rb_of_prefix 0 hp0⟩
    | succ k ih =>
        have hpk : ∀ hp hp', analysis_prefix_18_4 task_cost task_period ts default_task num_cpus (k + 1) hp →
            analysis_prefix_18_4 task_cost task_period ts default_task num_cpus (k + 1) hp' → hp = hp' := by
          intro hp hp' h h'
          cases h with
          | AnalysisPrefix18_4_rcons _ a R ha hr =>
            cases h' with
            | AnalysisPrefix18_4_rcons _ a' R' ha' hr' =>
              rw [ih.1 a a' ha ha', ih.2 R R' hr hr']
        exact ⟨hpk, rb_of_prefix _ hpk⟩
  -- a returned bound is at least the task's cost
  have rb_ge_cost : ∀ i R, returned_bound_by_18_4 task_cost task_period ts default_task num_cpus i R →
      task_cost (task_at ts default_task i) ≤ R := by
    intro i R h
    cases h with
    | ReturnedBound18_4 _ hp s _ _ hR _ =>
      subst hR
      unfold iterate_18_4
      cases s with
      | zero => exact Nat.le_refl _
      | succ s =>
          rw [Function.iterate_succ_apply']
          unfold ftp_rta_recurrence_18_4
          exact Nat.le_add_right _ _
  -- in a prefix, the bound stored for a higher-priority task is the bound returned for it
  have lookup_prefix : ∀ k hp, analysis_prefix_18_4 task_cost task_period ts default_task num_cpus k hp →
      k ≤ ts.val.length → ∀ i, i < k → ∃ R, returned_bound_by_18_4 task_cost task_period ts default_task num_cpus i R ∧
        response_bound_of task_cost hp (task_at ts default_task i) = R := by
    intro k
    induction k with
    | zero => intro hp h hk i hi; omega
    | succ k ih =>
        intro hp h hk i hi
        cases h with
        | AnalysisPrefix18_4_rcons _ hp0 Rk h0 hr =>
          rw [lookup_append]
          by_cases hik : i < k
          · have hmem : task_at ts default_task i ∈ hp0.map Prod.fst := by
              rw [keys k hp0 h0]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hik, rfl⟩
            rw [if_pos hmem]
            exact ih hp0 h0 (by omega) i hik
          · have hik' : i = k := by omega
            subst hik'
            have hnot : task_at ts default_task i ∉ hp0.map Prod.fst := by
              rw [keys _ hp0 h0]
              intro hm
              obtain ⟨j, hj, hji⟩ := List.mem_map.mp hm
              rw [List.mem_range] at hj
              have := tinj j i (by omega) (by omega) hji
              omega
            rw [if_neg hnot, if_pos rfl]
            exact ⟨Rk, hr, rfl⟩
  -- the workload term `(y / T) e + min e (y % T)` is monotone in `y`
  have mono : ∀ (C T a b : Nat), a ≤ b → (a / T) * C + min C (a % T) ≤ (b / T) * C + min C (b % T) := by
    intro C T a b hab
    have hq : a / T ≤ b / T := Nat.div_le_div_right hab
    rcases Nat.eq_or_lt_of_le hq with hq | hq
    · have ha := Nat.div_add_mod a T
      have hb := Nat.div_add_mod b T
      rw [hq] at ha
      have hr : a % T ≤ b % T := by omega
      rw [hq]
      have := min_le_min_left C hr
      omega
    · have h1 : (a / T) * C + C ≤ (b / T) * C := by
        have := Nat.mul_le_mul_right C (Nat.succ_le_of_lt hq)
        rwa [Nat.succ_mul] at this
      have h2 := min_le_left C (a % T)
      omega
  -- summing the `c` largest elements loses nothing when at most `c` elements are positive
  have top_sum : ∀ (xs : List Nat) (c : Nat), xs.countP (fun x => decide (0 < x)) ≤ c →
      sumSeq ((xs.mergeSort (fun x y => decide (y ≤ x))).take c) (fun d => d) = sumSeq xs (fun d => d) := by
    intro xs c hc
    have hperm : (xs.mergeSort (fun x y => decide (y ≤ x))).Perm xs := List.mergeSort_perm xs _
    have hsorted := List.pairwise_mergeSort (le := fun x y : Nat => decide (y ≤ x))
      (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) xs
    generalize xs.mergeSort (fun x y => decide (y ≤ x)) = s at hperm hsorted
    have hcount : s.countP (fun x => decide (0 < x)) ≤ c := by rw [hperm.countP_eq]; exact hc
    have hdrop : ∀ y ∈ s.drop c, y = 0 := by
      intro y hy
      by_contra hy0
      have hlen : c < s.length := by
        by_contra hle
        rw [List.drop_eq_nil_of_le (by omega)] at hy
        simp at hy
      have hsplit := List.take_append_drop c s
      have hpw := hsorted
      rw [← hsplit, List.pairwise_append] at hpw
      have hall : ∀ a ∈ s.take c, 0 < a := by
        intro a ha
        have := hpw.2.2 a ha y hy
        simp only [decide_eq_true_eq] at this
        omega
      have htake : (s.take c).countP (fun x => decide (0 < x)) = (s.take c).length :=
        List.countP_eq_length.mpr (by intro a ha; simpa using hall a ha)
      have hdrop1 : 0 < (s.drop c).countP (fun x => decide (0 < x)) :=
        List.countP_pos_iff.mpr ⟨y, hy, by simp only [decide_eq_true_eq]; omega⟩
      have hsum := congrArg (List.countP (fun x => decide (0 < x))) hsplit
      rw [List.countP_append] at hsum
      have hlt : (s.take c).length = c := by rw [List.length_take]; omega
      omega
    have hz : ((s.drop c).map fun d => d).sum = 0 := by
      rw [List.sum_eq_zero_iff]
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hdrop y hy
    unfold sumSeq
    calc ((s.take c).map fun d => d).sum
        = ((s.take c).map fun d => d).sum + ((s.drop c).map fun d => d).sum := by rw [hz, Nat.add_zero]
      _ = (s.map fun d => d).sum := by rw [← List.sum_append, ← List.map_append, List.take_append_drop]
      _ = (xs.map fun d => d).sum := (hperm.map _).sum_eq
  -- the members of `take k ts` are the tasks of index `< k`
  have mem_hp : ∀ k x, x ∈ higher_priority_tasks_of ts k →
      ∃ i, i < k ∧ i < ts.val.length ∧ x = task_at ts default_task i := by
    intro k x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
    exact ⟨j, by omega, by omega, (tget j (by omega)).symm⟩
  -- Key step: under the facts on the stored bounds, the recurrences of 18.4 and 18.5 coincide.
  have key : ∀ (hp : hp_response_bounds sporadic_task) (k : Nat), k < ts.val.length →
      (∀ i, i < k → task_cost (task_at ts default_task i) ≤
        response_bound_of task_cost hp (task_at ts default_task i)) →
      (∀ i, i < k → i < num_cpus →
        response_bound_of task_cost hp (task_at ts default_task i) = task_cost (task_at ts default_task i)) →
      ∀ L, ftp_rta_recurrence_18_5 task_cost task_period ts default_task num_cpus hp k L =
        ftp_rta_recurrence_18_4 task_cost task_period ts default_task num_cpus hp k L := by
    intro hp k hk hge hcost L
    set tsk := task_at ts default_task k with htsk
    set hs := higher_priority_tasks_of ts k with hhs
    let CI := fun x => carry_in_workload_17_7 task_cost task_period hp x tsk L
    let NC := fun x => non_carry_in_workload_17_8 task_cost task_period x tsk L
    let D := fun x => carry_in_difference_17_9 task_cost task_period hp x tsk L
    have hNC : ∀ x ∈ hs, NC x ≤ CI x := by
      intro x hx
      obtain ⟨i, hik, hin, rfl⟩ := mem_hp k x hx
      have hR := hge i hik
      simp only [CI, NC, carry_in_workload_17_7, non_carry_in_workload_17_8, generic_workload_bound_17_3]
      have := mono (task_cost (task_at ts default_task i)) (task_period (task_at ts default_task i)) L
        (L + response_bound_of task_cost hp (task_at ts default_task i) - task_cost (task_at ts default_task i))
        (Nat.le_sub_of_add_le (Nat.add_le_add_left hR L))
      exact min_le_min_right _ this
    have hD0 : ∀ x ∈ (ts.val.take (min num_cpus k)), D x = 0 := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
      have hjm : j < num_cpus := by omega
      have hjk : j < k := by omega
      rw [← tget j (by omega)]
      simp only [D, carry_in_difference_17_9, carry_in_workload_17_7, non_carry_in_workload_17_8,
        generic_workload_bound_17_3, hcost j hjk hjm, Nat.add_sub_cancel, Nat.sub_self]
    -- at most `m - 1` positive differences
    have hcount : (hs.map D).countP (fun x => decide (0 < x)) ≤ num_cpus - 1 := by
      rw [List.countP_map]
      have hsplit : hs = ts.val.take (min num_cpus k) ++ (hs.drop (min num_cpus k)) := by
        conv_lhs => rw [← List.take_append_drop (min num_cpus k) hs]
        rw [hhs, higher_priority_tasks_of, List.take_take, Nat.min_eq_left (Nat.min_le_right num_cpus k)]
      rw [hsplit, List.countP_append]
      have h1 : (ts.val.take (min num_cpus k)).countP ((fun x => decide (0 < x)) ∘ D) = 0 := by
        rw [List.countP_eq_zero]
        intro x hx
        simp [hD0 x hx]
      have h2 := List.countP_le_length (p := (fun x => decide (0 < x)) ∘ D) (l := hs.drop (min num_cpus k))
      have h3 : (hs.drop (min num_cpus k)).length = k - min num_cpus k := by
        rw [List.length_drop, hhs, higher_priority_tasks_of, List.length_take]; omega
      omega
    have hsumD : sumSeq (largest_carry_in_differences task_cost task_period ts default_task num_cpus hp k L)
        (fun delta => delta) = sumSeq hs D := by
      unfold largest_carry_in_differences
      simp only
      rw [top_sum _ _ hcount]
      simp [sumSeq, List.map_map]
      rfl
    have hsplitsum : sumSeq hs CI = sumSeq hs NC + sumSeq hs D := by
      unfold sumSeq
      rw [← List.sum_map_add]
      congr 1
      apply List.map_congr_left
      intro x hx
      have := hNC x hx
      simp only [CI, NC, D, carry_in_difference_17_9] at this ⊢
      omega
    unfold ftp_rta_recurrence_18_5 ftp_rta_recurrence_18_4
    simp only
    rw [hsumD]
    have : sumSeq hs NC + sumSeq hs D = sumSeq hs CI := hsplitsum.symm
    simp only [CI, NC, carry_in_workload_17_7] at this
    rw [this]
  -- Theorem: by induction along the priority order, both analyses have the same prefixes and bounds.
  have rb_equiv : ∀ k, k < ts.val.length →
      (∀ hp, analysis_prefix_18_4 task_cost task_period ts default_task num_cpus k hp ↔
        analysis_prefix_18_5 task_cost task_period ts default_task num_cpus k hp) →
      ∀ R, returned_bound_by_18_4 task_cost task_period ts default_task num_cpus k R ↔
        returned_bound_by_18_5 task_cost task_period ts default_task num_cpus k R := by
    intro k hk hpre R
    -- facts on the stored bounds of any prefix of analysis 18.4
    have feq : ∀ hp, analysis_prefix_18_4 task_cost task_period ts default_task num_cpus k hp →
        ftp_rta_recurrence_18_5 task_cost task_period ts default_task num_cpus hp k =
          ftp_rta_recurrence_18_4 task_cost task_period ts default_task num_cpus hp k := by
      intro hp h
      funext L
      apply key hp k hk
      · intro i hi
        obtain ⟨Ri, hri, hl⟩ := lookup_prefix k hp h (by omega) i hi
        rw [hl]; exact rb_ge_cost i Ri hri
      · intro i hi him
        obtain ⟨Ri, hri, hl⟩ := lookup_prefix k hp h (by omega) i hi
        rw [hl]
        exact (uniq i).2 Ri _ hri (Lemma18_1 i (by omega)).1
    constructor
    · intro h
      cases h with
      | ReturnedBound18_4 _ hp s _ hp4 hR hfix =>
        have e := feq hp hp4
        refine returned_bound_by_18_5.ReturnedBound18_5 k hp s _ ((hpre hp).mp hp4) ?_ ?_
        · rw [hR]; unfold iterate_18_5 iterate_18_4; rw [e]
        · rw [e]; exact hfix
    · intro h
      cases h with
      | ReturnedBound18_5 _ hp s _ hp5 hR hfix =>
        have hp4 := (hpre hp).mpr hp5
        have e := feq hp hp4
        refine returned_bound_by_18_4.ReturnedBound18_4 k hp s _ hp4 ?_ ?_
        · rw [hR]; unfold iterate_18_5 iterate_18_4; rw [e]
        · rw [← e]; exact hfix
  have pre_equiv : ∀ k, k ≤ ts.val.length → ∀ hp,
      analysis_prefix_18_4 task_cost task_period ts default_task num_cpus k hp ↔
        analysis_prefix_18_5 task_cost task_period ts default_task num_cpus k hp := by
    intro k
    induction k with
    | zero =>
        intro _ hp
        constructor
        · intro h; cases h; exact analysis_prefix_18_5.AnalysisPrefix18_5_nil
        · intro h; cases h; exact analysis_prefix_18_4.AnalysisPrefix18_4_nil
    | succ k ih =>
        intro hk hp
        have ihk := ih (by omega)
        have rbk := rb_equiv k (by omega) ihk
        constructor
        · intro h
          cases h with
          | AnalysisPrefix18_4_rcons _ hp0 R h0 hr =>
            exact analysis_prefix_18_5.AnalysisPrefix18_5_rcons k hp0 R ((ihk hp0).mp h0) ((rbk R).mp hr)
        · intro h
          cases h with
          | AnalysisPrefix18_5_rcons _ hp0 R h0 hr =>
            exact analysis_prefix_18_4.AnalysisPrefix18_4_rcons k hp0 R ((ihk hp0).mpr h0) ((rbk R).mpr hr)
  intro k R hk
  exact rb_equiv k hk (pre_equiv k (by omega)) R

end CaseStudies.BOOK2015.Theorem18_6
