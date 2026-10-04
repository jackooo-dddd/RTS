"""Lean translations of the definition variants shared by the 2009/2014/2015-BOOK case studies.
Each key is a variant id of contracts/variants.json (`name#X`); the text is the Lean declaration.
Conventions: classic-prosa representation addendum (minn = min, \\sum_(x <- s) F = sumSeq s F,
sort r s = s.mergeSort (decide-relation), take = List.take, n.-1 = n - 1, [seq x <- s | P] = s.filter P)."""

TASK = "{sporadic_task : Type u} [DecidableEq sporadic_task]"

S = {}

S["max_jobs#A"] = f"""def max_jobs {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time) : Nat :=
  div_floor (delta - task_cost tsk) (task_period tsk)"""

S["W#A"] = f"""def W {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_tsk delta : time) : Nat :=
  let e_k := task_cost tsk
  let p_k := task_period tsk
  min (e_k - 1) (delta + R_tsk - e_k - max_jobs task_cost task_period tsk delta * p_k - p_k) +
    max_jobs task_cost task_period tsk delta * e_k + e_k"""

S["W_NC#A"] = f"""def W_NC {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time) : Nat :=
  let e_i := task_cost tsk
  let p_i := task_period tsk
  div_floor delta p_i * e_i + min e_i (delta % p_i)"""

S["interference_bound_generic#A"] = f"""def interference_bound_generic {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time)
    (tsk_R : sporadic_task × time) : Nat :=
  let tsk_other := tsk_R.1
  let R_other := tsk_R.2
  min (W task_cost task_period tsk_other R_other delta) (delta - task_cost tsk + 1)"""

S["interference_bound_nc#A"] = f"""def interference_bound_nc {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time)
    (tsk_R : sporadic_task × time) : Nat :=
  let tsk_other := tsk_R.1
  min (W_NC task_cost task_period tsk_other delta) (delta - task_cost tsk + 1)"""

S["interference_bound_delta#A"] = f"""def interference_bound_delta {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time)
    (tsk_R : sporadic_task × time) : Nat :=
  interference_bound_generic task_cost task_period tsk delta tsk_R -
    interference_bound_nc task_cost task_period tsk delta tsk_R"""

S["sum_largest#A"] = """def sum_largest (n : Nat) (xs : List Nat) : Nat :=
  sumSeq ((xs.mergeSort (fun x y => decide (y ≤ x))).take n) (fun x => x)"""

S["total_interference_bound_fp#A"] = f"""def total_interference_bound_fp {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (delta : time) : Nat :=
  sumSeq R_prev (fun (tsk_other, R_other) =>
    interference_bound_generic task_cost task_period tsk delta (tsk_other, R_other))"""

S["CI_taskset#A"] = f"""def CI_taskset {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus : Nat) :
    List (sporadic_task × time) :=
  (R_prev.mergeSort (fun p q =>
    decide (interference_bound_delta task_cost task_period tsk delta q ≤
      interference_bound_delta task_cost task_period tsk delta p))).take (num_cpus - 1)"""

S["NC_taskset#A"] = f"""def NC_taskset {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus : Nat) :
    List (sporadic_task × time) :=
  R_prev.filter (fun p => !decide (p ∈ CI_taskset task_cost task_period tsk R_prev delta num_cpus))"""

S["total_interference_bound_ci#A"] = f"""def total_interference_bound_ci {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus : Nat) : Nat :=
  sumSeq (CI_taskset task_cost task_period tsk R_prev delta num_cpus)
    (fun p => interference_bound_generic task_cost task_period tsk delta p)"""

S["total_interference_bound_nc#A"] = f"""def total_interference_bound_nc {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus : Nat) : Nat :=
  sumSeq (NC_taskset task_cost task_period tsk R_prev delta num_cpus)
    (fun p => interference_bound_nc task_cost task_period tsk delta p)"""

S["total_interference_bound_gn#A"] = f"""def total_interference_bound_gn {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus : Nat) : Nat :=
  sumSeq (NC_taskset task_cost task_period tsk R_prev delta num_cpus)
      (fun p => interference_bound_nc task_cost task_period tsk delta p) +
    sumSeq (CI_taskset task_cost task_period tsk R_prev delta num_cpus)
      (fun p => interference_bound_generic task_cost task_period tsk delta p)"""

JT = "{sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task] [DecidableEq Job]"

S["hp_busy#A"] = f"""def hp_busy {JT}
    (job_task : Job → sporadic_task) (ts : taskset_of sporadic_task) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task)
    (tsk : sporadic_task) (t : time) : Prop :=
  ts.val.countP (fun tsk_other =>
    task_is_scheduled job_task sched tsk_other t &&
      higher_priority_task higher_eq_priority tsk tsk_other) = num_cpus"""

S["is_carry_in_job#A"] = f"""def is_carry_in_job {JT}
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) (num_cpus : Nat) (sched : schedule Job num_cpus)
    (higher_eq_priority : FP_policy sporadic_task) (tsk : sporadic_task) (j : Job)
    (t0 : schedule Job num_cpus → Job → time) (j0 : Job) : Prop :=
  arrives_in arr_seq j0 ∧
    higher_priority_task higher_eq_priority tsk (job_task j0) = true ∧
    job_arrival j0 < t0 sched j ∧
    (!completed job_cost sched j0 (t0 sched j)) = true"""

S["task_has_carry_in_job#A"] = f"""def task_has_carry_in_job {JT}
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) (num_cpus : Nat) (sched : schedule Job num_cpus)
    (higher_eq_priority : FP_policy sporadic_task) (tsk : sporadic_task) (j : Job)
    (t0 : schedule Job num_cpus → Job → time) (tsk_other : sporadic_task) : Prop :=
  ∃ j0 : Job, job_task j0 = tsk_other ∧
    is_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk j t0 j0"""
