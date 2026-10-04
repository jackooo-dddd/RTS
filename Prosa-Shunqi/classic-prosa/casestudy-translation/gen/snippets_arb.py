"""Arbitrary-deadline (h-job) definition variants of 2009 Lemma5 and Theorem2."""
from snippets_base import TASK, JT
S = {}
TT = "(task_cost task_period : sporadic_task → time) (tsk : sporadic_task)"
S["interference_bound_arbitrary_ci#A"] = f"""def interference_bound_arbitrary_ci {TASK}
    {TT} (delta : time) (tsk_R : sporadic_task × time) (h : Nat) : Nat :=
  let tsk_other := tsk_R.1
  let R_other := tsk_R.2
  min (W task_cost task_period tsk_other R_other delta) (delta - h * task_cost tsk + 1)"""
S["interference_bound_arbitrary_nc#A"] = f"""def interference_bound_arbitrary_nc {TASK}
    {TT} (delta : time) (tsk_R : sporadic_task × time) (h : Nat) : Nat :=
  let tsk_other := tsk_R.1
  min (W_NC task_cost task_period tsk_other delta) (delta - h * task_cost tsk + 1)"""
S["interference_bound_delta#B"] = f"""def interference_bound_delta {TASK}
    {TT} (delta : time) (tsk_R : sporadic_task × time) (h : Nat) : Nat :=
  interference_bound_arbitrary_ci task_cost task_period tsk delta tsk_R h -
    interference_bound_arbitrary_nc task_cost task_period tsk delta tsk_R h"""
S["total_interference_bound_fp#B"] = f"""def total_interference_bound_fp {TASK}
    {TT} (R_prev : List (sporadic_task × time)) (delta : time) (h : Nat) : Nat :=
  sumSeq R_prev (fun (tsk_other, R_other) =>
    interference_bound_arbitrary_ci task_cost task_period tsk delta (tsk_other, R_other) h)"""
S["CI_taskset#B"] = f"""def CI_taskset {TASK}
    {TT} (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus h : Nat) :
    List (sporadic_task × time) :=
  (R_prev.mergeSort (fun p q =>
    decide (interference_bound_delta task_cost task_period tsk delta q h ≤
      interference_bound_delta task_cost task_period tsk delta p h))).take (num_cpus - 1)"""
S["NC_taskset#B"] = f"""def NC_taskset {TASK}
    {TT} (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus h : Nat) :
    List (sporadic_task × time) :=
  R_prev.filter (fun p => !decide (p ∈ CI_taskset task_cost task_period tsk R_prev delta num_cpus h))"""
S["total_interference_bound_ci#B"] = f"""def total_interference_bound_ci {TASK}
    {TT} (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus h : Nat) : Nat :=
  sumSeq (CI_taskset task_cost task_period tsk R_prev delta num_cpus h)
    (fun p => interference_bound_arbitrary_ci task_cost task_period tsk delta p h)"""
S["total_interference_bound_nc#B"] = f"""def total_interference_bound_nc {TASK}
    {TT} (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus h : Nat) : Nat :=
  sumSeq (NC_taskset task_cost task_period tsk R_prev delta num_cpus h)
    (fun p => interference_bound_arbitrary_nc task_cost task_period tsk delta p h)"""
S["total_interference_bound_gn_arbitrary#A"] = f"""def total_interference_bound_gn_arbitrary {TASK}
    {TT} (R_prev : List (sporadic_task × time)) (delta : time) (num_cpus h : Nat) : Nat :=
  sumSeq (NC_taskset task_cost task_period tsk R_prev delta num_cpus h)
      (fun p => interference_bound_arbitrary_nc task_cost task_period tsk delta p h) +
    sumSeq (CI_taskset task_cost task_period tsk R_prev delta num_cpus h)
      (fun p => interference_bound_arbitrary_ci task_cost task_period tsk delta p h)"""
FC = """(task_cost task_period : sporadic_task → time) (num_cpus : Nat) (tsk : sporadic_task)
    (hp_bounds : List (sporadic_task × time)) (h : Nat) (chi : time)"""
S["f_chi#A"] = f"""def f_chi {TASK}
    {FC} : Nat :=
  h * task_cost tsk +
    div_floor (total_interference_bound_gn_arbitrary task_cost task_period tsk hp_bounds chi num_cpus h) num_cpus"""
# Theorem2's source passes `h` and `num_cpus` to `total_interference_bound_gn_arbitrary` in swapped positions;
# translated as written.
S["f_chi#B"] = f"""def f_chi {TASK}
    {FC} : Nat :=
  h * task_cost tsk +
    div_floor (total_interference_bound_gn_arbitrary task_cost task_period tsk hp_bounds chi h num_cpus) num_cpus"""
S["chi_is_least_solution#A"] = f"""def chi_is_least_solution {TASK}
    {FC} : Prop :=
  chi = f_chi task_cost task_period num_cpus tsk hp_bounds h chi ∧
    ∀ x : time, x = f_chi task_cost task_period num_cpus tsk hp_bounds h x → chi ≤ x"""
PH = "(task_period : sporadic_task → time) (tsk : sporadic_task) (chi_min : Nat → time) (phi : time)"
S["H_phi_satisfy#A"] = f"""def H_phi_satisfy {TASK}
    {PH} (h : Nat) : Bool :=
  decide (chi_min h ≤ h * task_period tsk + phi)"""
S["R_phi_term#A"] = f"""def R_phi_term {TASK}
    {PH} (h : Nat) : time :=
  chi_min h - ((h - 1) * task_period tsk + phi)"""
MRP = f"""def max_R_phi_term {TASK}
    {PH} : Nat → time
  | 0 => 0
  | h' + 1 => max (max_R_phi_term task_period tsk chi_min phi h') (R_phi_term task_period tsk chi_min phi (h' + 1))"""
S["max_R_phi_term#A"] = MRP      # `maxn` in the source
S["max_R_phi_term#B"] = MRP      # `max` (= `Nat.max`) in the source; both are `max` on `Nat`
JA = "(job_arrival job_task)"
S["jobs_of_tsk_between#A"] = f"""def jobs_of_tsk_between {JT}
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (tsk : sporadic_task) (t1 t2 : time) :
    List Job :=
  arrivals_of_task_between job_task arr_seq tsk t1 t2"""
S["first_h_jobs_through#A"] = f"""def first_h_jobs_through {JT}
    (job_arrival : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (tsk : sporadic_task) (j j_h : Job) : List Job :=
  jobs_of_tsk_between job_task arr_seq tsk (job_arrival j) (job_arrival j_h + 1)"""
S["job_finishes_at#A"] = """def job_finishes_at {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (num_cpus : Nat)
    (sched : schedule Job num_cpus) (j_h : Job) (f_h : time) : Bool :=
  (!completed job_cost sched j_h (f_h - 1)) && completed job_cost sched j_h f_h"""
TPJ = f"""{TASK}
    (task_period : sporadic_task → time) {{Job : Type v}} [DecidableEq Job]"""
HTH = "job_is_hth_after_j task_period job_arrival job_task arr_seq tsk j"
S["job_is_hth_after_j#A"] = f"""def job_is_hth_after_j {TPJ}
    (job_arrival : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (tsk : sporadic_task) (j : Job) (h : Nat) (j_h : Job) : Prop :=
  1 ≤ h ∧
    arrives_in arr_seq j_h ∧
    job_task j_h = tsk ∧
    job_arrival j_h = job_arrival j + (h - 1) * task_period tsk ∧
    (first_h_jobs_through job_arrival job_task arr_seq tsk j j_h).length = h ∧
    j_h ∈ first_h_jobs_through job_arrival job_task arr_seq tsk j j_h"""
S["preceding_jobs_are_completed_before_first_job#A"] = f"""def preceding_jobs_are_completed_before_first_job {JT}
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (tsk : sporadic_task) (j : Job) : Prop :=
  ∀ j_prev : Job, arrives_in arr_seq j_prev → job_task j_prev = tsk → job_arrival j_prev < job_arrival j →
    completed job_cost sched j_prev (job_arrival j) = true"""
S["consecutive_jobs_exist_through#A"] = f"""def consecutive_jobs_exist_through {TPJ}
    (job_arrival : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (tsk : sporadic_task) (j : Job) (h_last : Nat) : Prop :=
  ∀ h : Nat, 1 ≤ h → h ≤ h_last → ∃ j_h : Job, {HTH} h j_h"""
S["consecutive_jobs_are_tight_through#A"] = f"""def consecutive_jobs_are_tight_through {TPJ}
    (job_arrival : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (tsk : sporadic_task) (j : Job) (h_last : Nat) : Prop :=
  ∀ (h : Nat) (j_h j_next : Job), 1 ≤ h → h < h_last → {HTH} h j_h → {HTH} (h + 1) j_next →
    job_arrival j_next = job_arrival j_h + task_period tsk"""
CJC = """(job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (tsk : sporadic_task)"""
S["consecutive_jobs_overlap_through#A"] = f"""def consecutive_jobs_overlap_through {TPJ}
    {CJC} (j : Job) (h_last : Nat) : Prop :=
  ∀ (h : Nat) (j_h j_next : Job), 1 ≤ h → h < h_last → {HTH} h j_h → {HTH} (h + 1) j_next →
    (!completed job_cost sched j_h (job_arrival j_next)) = true"""
S["tight_chain_ending_at#A"] = f"""def tight_chain_ending_at {TPJ}
    {CJC} (j : Job) (h_last : Nat) (j_last : Job) : Prop :=
  {HTH} h_last j_last ∧
    preceding_jobs_are_completed_before_first_job job_arrival job_cost job_task arr_seq num_cpus sched tsk j ∧
    consecutive_jobs_exist_through task_period job_arrival job_task arr_seq tsk j h_last ∧
    consecutive_jobs_are_tight_through task_period job_arrival job_task arr_seq tsk j h_last ∧
    consecutive_jobs_overlap_through task_period job_arrival job_cost job_task arr_seq num_cpus sched tsk j h_last"""
S["job_has_worstcase_response_time#A"] = f"""def job_has_worstcase_response_time {JT}
    {CJC} (j_worst : Job) : Prop :=
  ∀ (j0 : Job) (x : Nat), arrives_in arr_seq j0 → job_task j0 = tsk →
    completed job_cost sched j_worst (job_arrival j_worst + x) = true →
    completed job_cost sched j0 (job_arrival j0 + x) = true"""
S["worstcase_job_selected_from_tight_chain#A"] = f"""def worstcase_job_selected_from_tight_chain {TPJ}
    {CJC} (j : Job) (h_last h_worst : Nat) (j_worst : Job) (f_worst : time) : Prop :=
  h_worst ≤ h_last ∧
    {HTH} h_worst j_worst ∧
    job_finishes_at job_cost num_cpus sched j_worst f_worst = true ∧
    job_arrival j_worst < f_worst ∧
    job_has_worstcase_response_time job_arrival job_cost job_task arr_seq num_cpus sched tsk j_worst"""
TC = "(task_period : sporadic_task → time) (tsk : sporadic_task) (chi_min : Nat → time)"
S["Term#A"] = f"""def Term {TASK}
    {TC} (h : Nat) : Bool :=
  decide (chi_min h ≤ h * task_period tsk)"""
S["Miss#A"] = f"""def Miss {TASK}
    (task_period task_deadline : sporadic_task → time) (tsk : sporadic_task) (chi_min : Nat → time) (h : Nat) :
    Bool :=
  decide ((h - 1) * task_period tsk + task_deadline tsk < chi_min h)"""
S["H_satisfy#A"] = f"""def H_satisfy {TASK}
    {TC} (h : Nat) : Bool :=
  Term task_period tsk chi_min h"""
S["R_term#A"] = f"""def R_term {TASK}
    {TC} (h : Nat) : time :=
  chi_min h - (h - 1) * task_period tsk"""
S["max_R_term#A"] = f"""def max_R_term {TASK}
    {TC} : Nat → time
  | 0 => 0
  | h' + 1 => max (max_R_term task_period tsk chi_min h') (R_term task_period tsk chi_min (h' + 1))"""
