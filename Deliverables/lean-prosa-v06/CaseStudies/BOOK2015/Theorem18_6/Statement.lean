-- Case study 2015-book-Theorem18_6: Baruah, Bertogna, Buttazzo — Multiprocessor Scheduling for Real-Time Systems (book, 2015), Theorem 18.6.
-- Original Rocq statement: RTS_Papers/2015-book-Theorem18_6/Theorem18_6.v.
-- Benchmark file: read-only.  Prove `CaseStudies.BOOK2015.Theorem18_6.Theorem18_6_statement` in `Solution.lean` (this folder).
import Prosa.Util.Sum
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task

/-!
Theorem 18.6 of Baruah, Bertogna & Buttazzo, *Multiprocessor Scheduling for Real-Time Systems*
(2015), as stated by the case study `2015-book-Theorem18_6` (Rocq section `Theorem18_6_Model`): for
a task set of at most `2m` tasks, indexed by decreasing fixed priority, the fixed-priority
response-time analyses of Theorem 18.4 (recurrence `ftp_rta_recurrence_18_4`) and Theorem 18.5
(`ftp_rta_recurrence_18_5`, which adds only the `m - 1` largest carry-in differences) return the
same upper bound for every task. The bounds returned by each analysis are modelled by the mutually
inductive `returned_bound_by_18_x` / `analysis_prefix_18_x`: an analysis prefix stores the bounds
already returned for the higher-priority tasks, and a returned bound is a fixed point reached by
iterating the recurrence from the task's cost. Lemma 18.1 (the `m` highest-priority tasks get their
cost as bound under both analyses) is a hypothesis.

Representation notes: `minn` is `min`; `x %/ y` is `x / y` and `x %% y` is `x % y`; `\sum_(x <- s) F
x` is `sumSeq s F`; `nth default_task ts k` is `ts.val.getD k default_task`; `take k ts` is
`ts.val.take k`; `size ts` is `ts.val.length`; `n.-1` is `n - 1`; `n.*2` is `2 * n`; `iter n f x` is
`f^[n] x`; `sort geq s` is `s.mergeSort (fun x y => decide (y ≤ x))`; `rcons s x` is `s ++ [x]`;
`tsk == tsk'` is `decide (tsk = tsk')`; Boolean-valued definitions (`ftp_bcl_test_18_2`,
`ftp_rta_interference_test_18_3`, `at_most_two_m_tasks`) are `Bool`s and are `= true` in proposition
position.
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

/-- The statement of the case study's theorem `Theorem18_6`. -/
def Theorem18_6_statement : Prop :=
  ∀ {sporadic_task : Type u} [DecidableEq sporadic_task]
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
          (task_cost (task_at ts default_task k))),
    at_most_two_m_tasks ts num_cpus = true →
      theorems_18_4_and_18_5_are_equivalent task_cost task_period ts default_task num_cpus

end CaseStudies.BOOK2015.Theorem18_6
