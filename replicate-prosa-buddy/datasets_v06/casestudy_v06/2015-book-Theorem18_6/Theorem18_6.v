Require Import prosa.classic.util.all.
Require Import prosa.classic.model.time.
Require Import prosa.classic.model.arrival.basic.task.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq bigop div path.

Import Time SporadicTask SporadicTaskset.

Section Theorem18_6_Model.

  Context {sporadic_task : eqType}.

  (* Chapter 18 studies 3-parameter sporadic tasks with WCET, period, and deadline. *)
  Variable task_cost : sporadic_task -> time.
  Variable task_period : sporadic_task -> time.
  Variable task_deadline : sporadic_task -> time.

  (* The task list is indexed by decreasing FTP priority, as assumed in Chapter 18. *)
  Variable ts : taskset_of sporadic_task.

  (* We use a default task to refer to the k-th task by list index. *)
  Variable default_task : sporadic_task.

  (* The platform has m identical processors. *)
  Variable num_cpus : nat.

  (* Positive processor supply is required by the floor-division recurrences. *)
  Hypothesis H_num_cpus_positive : num_cpus > 0.

  (* The chapter assumes a valid sporadic task set. *)
  Hypothesis H_valid_taskset :
    valid_sporadic_taskset task_cost task_period task_deadline ts.

  (* Chapter 18 specializes the constrained-deadline setting. *)
  Hypothesis H_constrained_deadlines :
    forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

  (* To speak about Eq. (18.1), we model the per-task interference quantity I_{i,k}.
     The exact arithmetic interference term used in the paper is captured here as a
     paper-level function over higher-priority and analyzed tasks. *)
  Variable ftp_interference : sporadic_task -> sporadic_task -> time -> time.

  Definition task_at (k : nat) : sporadic_task := nth default_task ts k.

  Definition higher_priority_tasks_of (k : nat) : seq sporadic_task := take k ts.

  (* Observation 18.1: lower-priority tasks do not interfere under FTP. *)
  Definition lower_priority_tasks_do_not_interfere :=
    forall i k R,
      k < size ts -> i < size ts -> k < i ->
      ftp_interference (task_at i) (task_at k) R = 0.

  (* Theorem 18.1: total interference is the sum of higher-priority interference
     terms divided by the number of processors. *)
  Definition ftp_total_interference_18_1 (k R : time) :=
    (\sum_(hp_tsk <- higher_priority_tasks_of k)
       ftp_interference hp_tsk (task_at k) R) %/ num_cpus.

  (* Equation (17.3): generic workload bound W'_i(L), parameterized by a
     response-time upper bound supplied for the interfering task. *)
  Definition generic_workload_bound_17_3 (tsk : sporadic_task) (Rub_i L : time) :=
    let C := task_cost tsk in
    let T := task_period tsk in
      ((L + Rub_i - C) %/ T) * C + minn C ((L + Rub_i - C) %% T).

  (* Equation (18.2): FTP-specific workload bound used by the [bcl] test. *)
  Definition ftp_bcl_workload_bound_18_2 (hp_tsk tsk : sporadic_task) :=
    let C := task_cost hp_tsk in
    let T := task_period hp_tsk in
    let D := task_deadline hp_tsk in
    let Dk := task_deadline tsk in
      ((Dk + D - C) %/ T) * C + minn C ((Dk + D - C) %% T).

  (* Theorem 18.2: the FTP [bcl] schedulability inequality. *)
  Definition ftp_bcl_test_18_2 (k : nat) :=
    let tsk := task_at k in
      \sum_(hp_tsk <- higher_priority_tasks_of k)
        minn (task_deadline tsk - task_cost tsk)
             (ftp_bcl_workload_bound_18_2 hp_tsk tsk)
      < num_cpus * (task_deadline tsk - task_cost tsk).

  (* Theorem 18.3: FTP specialization of the generic interference condition. *)
  Definition ftp_rta_interference_test_18_3 (k : nat) (Rub_k : time) :=
    let tsk := task_at k in
      \sum_(hp_tsk <- higher_priority_tasks_of k)
        minn (ftp_interference hp_tsk tsk Rub_k) (Rub_k - task_cost tsk + 1)
      < num_cpus * (Rub_k - task_cost tsk + 1).

  (* A sequence of higher-priority response-time upper bounds is the input used
     by the fixed-point iteration of Theorem 18.4 and 18.5. *)
  Definition hp_response_bounds := seq (sporadic_task * time).

  (* The paper computes W'_i by using already-derived upper bounds Rub_i for the
     interfering higher-priority tasks. *)
  Fixpoint response_bound_of (hp_bounds : hp_response_bounds) (tsk : sporadic_task) :=
    if hp_bounds is (tsk', R) :: hp_bounds' then
      if tsk == tsk' then R else response_bound_of hp_bounds' tsk
    else task_cost tsk.

  (* Theorem 18.4: the original FTP [rta] recurrence body. *)
  Definition ftp_rta_recurrence_18_4 (hp_bounds : hp_response_bounds) (k : nat) (Rub_k : time) :=
    let tsk := task_at k in
      task_cost tsk +
      (\sum_(hp_tsk <- higher_priority_tasks_of k)
         minn (generic_workload_bound_17_3 hp_tsk (response_bound_of hp_bounds hp_tsk) Rub_k)
              (Rub_k - task_cost tsk + 1)) %/ num_cpus.

  (* Fixed-point iteration of Theorem 18.4, starting from Rub_k = C_k. *)
  Definition iterate_18_4 (hp_bounds : hp_response_bounds) (k steps : nat) :=
    iter steps (ftp_rta_recurrence_18_4 hp_bounds k) (task_cost (task_at k)).

  (* Equations (17.7), (17.8), and (17.9) reused in Theorem 18.5.
     For FTP, only higher-priority tasks contribute. *)
  Definition carry_in_workload_17_7
             (hp_bounds : hp_response_bounds) (hp_tsk tsk : sporadic_task) (L : time) :=
    minn (generic_workload_bound_17_3 hp_tsk (response_bound_of hp_bounds hp_tsk) L)
         (L - task_cost tsk + 1).

  Definition non_carry_in_workload_17_8 (hp_tsk tsk : sporadic_task) (L : time) :=
    let C := task_cost hp_tsk in
    let T := task_period hp_tsk in
      minn (((L %/ T) * C) + minn C (L %% T)) (L - task_cost tsk + 1).

  Definition carry_in_difference_17_9
             (hp_bounds : hp_response_bounds) (hp_tsk tsk : sporadic_task) (L : time) :=
    carry_in_workload_17_7 hp_bounds hp_tsk tsk L -
    non_carry_in_workload_17_8 hp_tsk tsk L.

  Definition largest_carry_in_differences (hp_bounds : hp_response_bounds) (k : nat) (L : time) :=
    let tsk := task_at k in
    let deltas :=
      [seq carry_in_difference_17_9 hp_bounds hp_tsk tsk L | hp_tsk <- higher_priority_tasks_of k] in
      take (num_cpus.-1) (sort geq deltas).

  (* Theorem 18.5: the improved FTP [rta] recurrence body. *)
  Definition ftp_rta_recurrence_18_5 (hp_bounds : hp_response_bounds) (k : nat) (Rub_k : time) :=
    let tsk := task_at k in
      task_cost tsk +
      ((\sum_(hp_tsk <- higher_priority_tasks_of k)
          non_carry_in_workload_17_8 hp_tsk tsk Rub_k)
       + (\sum_(delta <- largest_carry_in_differences hp_bounds k Rub_k) delta)) %/ num_cpus.

  (* Fixed-point iteration of Theorem 18.5, starting from Rub_k = C_k. *)
  Definition iterate_18_5 (hp_bounds : hp_response_bounds) (k steps : nat) :=
    iter steps (ftp_rta_recurrence_18_5 hp_bounds k) (task_cost (task_at k)).

  (* Analysis prefixes are built in priority order and store the already-returned
     higher-priority bounds required by Theorems 18.4 and 18.5. *)
  Inductive returned_bound_by_18_4 : nat -> time -> Prop :=
  | ReturnedBound18_4 :
      forall k hp_bounds steps Rub_k,
        analysis_prefix_18_4 k hp_bounds ->
        Rub_k = iterate_18_4 hp_bounds k steps ->
        ftp_rta_recurrence_18_4 hp_bounds k Rub_k = Rub_k ->
        returned_bound_by_18_4 k Rub_k
  with analysis_prefix_18_4 : nat -> hp_response_bounds -> Prop :=
  | AnalysisPrefix18_4_nil :
      analysis_prefix_18_4 0 [::]
  | AnalysisPrefix18_4_rcons :
      forall k hp_bounds Rub_k,
        analysis_prefix_18_4 k hp_bounds ->
        returned_bound_by_18_4 k Rub_k ->
        analysis_prefix_18_4 k.+1 (rcons hp_bounds (task_at k, Rub_k)).

  (* Theorem 18.5 uses the same priority-ordered higher-priority bounds, but with
     the improved carry-in-aware recurrence. *)
  Inductive returned_bound_by_18_5 : nat -> time -> Prop :=
  | ReturnedBound18_5 :
      forall k hp_bounds steps Rub_k,
        analysis_prefix_18_5 k hp_bounds ->
        Rub_k = iterate_18_5 hp_bounds k steps ->
        ftp_rta_recurrence_18_5 hp_bounds k Rub_k = Rub_k ->
        returned_bound_by_18_5 k Rub_k
  with analysis_prefix_18_5 : nat -> hp_response_bounds -> Prop :=
  | AnalysisPrefix18_5_nil :
      analysis_prefix_18_5 0 [::]
  | AnalysisPrefix18_5_rcons :
      forall k hp_bounds Rub_k,
        analysis_prefix_18_5 k hp_bounds ->
        returned_bound_by_18_5 k Rub_k ->
        analysis_prefix_18_5 k.+1 (rcons hp_bounds (task_at k, Rub_k)).

  (* Lemma 18.1: among the first m highest-priority tasks, both analyses return
     the WCET as the computed upper bound. *)
  Hypothesis Lemma18_1 :
    forall k,
      k < minn num_cpus (size ts) ->
      returned_bound_by_18_4 k (task_cost (task_at k)) /\
      returned_bound_by_18_5 k (task_cost (task_at k)).
  

  (* The paper compares the two analyses on task sets with n <= 2m. *)
  Definition at_most_two_m_tasks := size ts <= num_cpus.*2.

  (* Theorem 18.6: when n <= 2m, Theorems 18.4 and 18.5 return the same bounds. *)
  Definition theorems_18_4_and_18_5_are_equivalent :=
    forall k Rub_k,
      k < size ts ->
      (returned_bound_by_18_4 k Rub_k <-> returned_bound_by_18_5 k Rub_k).

  Theorem Theorem18_6 :
    at_most_two_m_tasks ->
    theorems_18_4_and_18_5_are_equivalent.
  Proof.
  Admitted.

End Theorem18_6_Model.
