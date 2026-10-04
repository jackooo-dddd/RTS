"""Definition variants of the 2014-RTCSA case studies."""
from snippets_base import TASK, JT
S = {}
S["x_p#A"] = f"""def x_p {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_tsk : time) : Nat :=
  let e_i := task_cost tsk
  let p_i := task_period tsk
  e_i - 1 + div_ceil (R_tsk - e_i) (p_i - e_i) * p_i - R_tsk"""
S["x_delta#A"] = f"""def x_delta {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_tsk delta : time) : Nat :=
  let e_i := task_cost tsk
  let p_i := task_period tsk
  min delta (div_ceil (R_tsk - e_i) (p_i - e_i) * e_i - 1)"""
S["W_CI#B"] = f"""def W_CI {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_tsk delta : time) : Nat :=
  let e_i := task_cost tsk
  let p_i := task_period tsk
  div_floor (delta - x_p task_cost task_period tsk R_tsk) p_i * e_i +
    min e_i ((delta - x_p task_cost task_period tsk R_tsk) % p_i) +
    x_delta task_cost task_period tsk R_tsk delta"""
JC = """(job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task) (tsk : sporadic_task)"""
S["is_carry_in_job#C"] = f"""def is_carry_in_job {JT}
    (job_arrival : Job → time) {JC} (j0 : Job) (t : time) : Prop :=
  arrives_in arr_seq j0 ∧
    higher_priority_task higher_eq_priority tsk (job_task j0) = true ∧
    job_arrival j0 < t ∧
    (!completed job_cost sched j0 t) = true"""
S["carry_in_jobs_of#A"] = f"""def carry_in_jobs_of {JT}
    {JC} (tsk_other : sporadic_task) (t : time) : List Job :=
  (jobs_arrived_before arr_seq t).filter (fun j0 =>
    (decide (job_task j0 = tsk_other) && higher_priority_task higher_eq_priority tsk (job_task j0)) &&
      !completed job_cost sched j0 t)"""
S["number_of_carry_in_jobs#A"] = f"""def number_of_carry_in_jobs {JT}
    {JC} (tsk_other : sporadic_task) (t : time) : Nat :=
  (carry_in_jobs_of job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other t).length"""
S["task_has_carry_in_job#C"] = f"""def task_has_carry_in_job {JT}
    (job_arrival : Job → time) {JC} (tsk_other : sporadic_task) (t : time) : Prop :=
  ∃ j0 : Job, job_task j0 = tsk_other ∧
    is_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk j0 t"""
S["no_carry_in_workload_of_task#B"] = f"""def no_carry_in_workload_of_task {JT}
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (hp_tsk : sporadic_task) (t : time) : Prop :=
  ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = hp_tsk → job_arrival j0 < t →
    completed job_cost sched j0 t = true"""
S["carry_in_job_workload#A"] = """def carry_in_job_workload {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (j0 : Job) (t : time) : Nat :=
  job_cost j0 - service sched j0 t"""
S["carry_in_workload#B"] = f"""def carry_in_workload {JT}
    {JC} (tsk_other : sporadic_task) (t : time) : Nat :=
  sumSeq (carry_in_jobs_of job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other t)
    (fun j0 => carry_in_job_workload job_cost num_cpus sched j0 t)"""
TT = "(task_cost task_period : sporadic_task → time) (tsk : sporadic_task)"
S["interference_bound_arbitrary_ci#B"] = f"""def interference_bound_arbitrary_ci {TASK}
    {TT} (delta : time) (tsk_R : sporadic_task × time) : Nat :=
  let tsk_other := tsk_R.1
  let R_other := tsk_R.2
  min (W_CI task_cost task_period tsk_other R_other delta) (delta - task_cost tsk + 1)"""
S["interference_bound_arbitrary_nc#B"] = f"""def interference_bound_arbitrary_nc {TASK}
    {TT} (delta : time) (tsk_R : sporadic_task × time) : Nat :=
  let tsk_other := tsk_R.1
  min (W_NC task_cost task_period tsk_other delta) (delta - task_cost tsk + 1)"""
S["total_interference_bound_CI#A"] = f"""def total_interference_bound_CI {TASK}
    {TT} (R_carryin : List (sporadic_task × time)) (delta : time) : Nat :=
  sumSeq R_carryin (fun (tsk_other, R_other) =>
    interference_bound_arbitrary_ci task_cost task_period tsk delta (tsk_other, R_other))"""
S["total_interference_bound_NC#A"] = f"""def total_interference_bound_NC {TASK}
    {TT} (R_noncarryin : List (sporadic_task × time)) (delta : time) : Nat :=
  sumSeq R_noncarryin (fun (tsk_other, R_other) =>
    interference_bound_arbitrary_nc task_cost task_period tsk delta (tsk_other, R_other))"""
S["total_interference_bound_rtcsa14#A"] = f"""def total_interference_bound_rtcsa14 {TASK}
    {TT} (R_carryin R_noncarryin : List (sporadic_task × time)) (delta : time) : Nat :=
  total_interference_bound_CI task_cost task_period tsk R_carryin delta +
    total_interference_bound_NC task_cost task_period tsk R_noncarryin delta"""
RR = """(task_cost task_period : sporadic_task → time) (num_cpus : Nat) (tsk : sporadic_task) (R : time)"""
S["response_time_recurrence#A"] = f"""def response_time_recurrence {TASK}
    {RR} (CI_taskset NC_taskset : List (sporadic_task × time)) : Prop :=
  R = task_cost tsk +
    div_floor (total_interference_bound_rtcsa14 task_cost task_period tsk CI_taskset NC_taskset R) num_cpus"""
S["R_is_minimal_solution#A"] = f"""def R_is_minimal_solution {TASK}
    {RR} (CI_taskset1 NC_taskset1 : List (sporadic_task × time)) : Prop :=
  ∀ x : time, x = task_cost tsk +
      div_floor (total_interference_bound_rtcsa14 task_cost task_period tsk CI_taskset1 NC_taskset1 x) num_cpus →
    R ≤ x"""
S["valid_CI_taskset#A"] = f"""def valid_CI_taskset {JT}
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (hp_bounds : List (sporadic_task × time))
    (critical_instant : time) (CI_taskset : List (sporadic_task × time)) : Prop :=
  (∀ p, p ∈ CI_taskset → p ∈ hp_bounds) ∧
    CI_taskset.Nodup ∧
    CI_taskset.length < num_cpus ∧
    ∀ (tsk_other : sporadic_task) (R_other : time), (tsk_other, R_other) ∈ CI_taskset →
      ∃ j0 : Job, arrives_in arr_seq j0 ∧ job_task j0 = tsk_other ∧ job_arrival j0 < critical_instant ∧
        (!completed job_cost sched j0 critical_instant) = true"""
