"""Carry-in definition variants (2009 Lemma1_2, Lemma2-1, Lemma2-2)."""
from snippets_base import TASK, JT
S = {}

S["carry_in_workload#A"] = """def carry_in_workload {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (j : Job) (t0 : schedule Job num_cpus → Job → time) (j0 : Job) : Nat :=
  job_cost j0 - service sched j0 (t0 sched j)"""

S["no_carry_in_workload_of_task#A"] = f"""def no_carry_in_workload_of_task {JT}
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (j : Job) (t0 : schedule Job num_cpus → Job → time)
    (hp_tsk : sporadic_task) : Prop :=
  ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = hp_tsk → job_arrival j0 < t0 sched j →
    completed job_cost sched j0 (t0 sched j) = true"""

S["W_CI#A"] = f"""def W_CI {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_tsk delta : time) : Nat :=
  let e_k := task_cost tsk
  let p_k := task_period tsk
  min (e_k - 1) (delta + R_tsk - e_k - max_jobs task_cost task_period tsk delta * p_k - p_k) +
    max_jobs task_cost task_period tsk delta * e_k + e_k"""

S["interference_bound_generic#B"] = f"""def interference_bound_generic {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (delta : time)
    (tsk_R : sporadic_task × time) : Nat :=
  let tsk_other := tsk_R.1
  let R_other := tsk_R.2
  min (W_CI task_cost task_period tsk_other R_other delta) (delta - task_cost tsk + 1)"""

S["hp_busy#B"] = f"""def hp_busy {JT}
    (job_task : Job → sporadic_task) (ts : taskset_of sporadic_task) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (tsk : sporadic_task) (higher_eq_priority : FP_policy sporadic_task)
    (t : time) : Prop :=
  ts.val.countP (fun tsk_other =>
    task_is_scheduled job_task sched tsk_other t &&
      higher_priority_task higher_eq_priority tsk tsk_other) = num_cpus"""

S["is_carry_in_job#B"] = f"""def is_carry_in_job {JT}
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) (num_cpus : Nat) (sched : schedule Job num_cpus)
    (tsk : sporadic_task) (higher_eq_priority : FP_policy sporadic_task) (j : Job)
    (t0 : schedule Job num_cpus → Job → time) (j0 : Job) : Prop :=
  arrives_in arr_seq j0 ∧
    higher_priority_task higher_eq_priority tsk (job_task j0) = true ∧
    job_arrival j0 < t0 sched j ∧
    (!completed job_cost sched j0 (t0 sched j)) = true"""

S["task_has_carry_in_job#B"] = f"""def task_has_carry_in_job {JT}
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) (num_cpus : Nat) (sched : schedule Job num_cpus)
    (tsk : sporadic_task) (higher_eq_priority : FP_policy sporadic_task) (j : Job)
    (t0 : schedule Job num_cpus → Job → time) (tsk_other : sporadic_task) : Prop :=
  ∃ j0 : Job, job_task j0 = tsk_other ∧
    is_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched tsk higher_eq_priority j t0 j0"""

S["Non_CI#A"] = f"""def Non_CI {JT}
    (job_arrival job_deadline : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (j : Job) (t0 : schedule Job num_cpus → Job → time)
    (tsk : sporadic_task) : Prop :=
  ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk → job_arrival j0 < t0 sched j →
    job_deadline j0 ≤ t0 sched j"""
