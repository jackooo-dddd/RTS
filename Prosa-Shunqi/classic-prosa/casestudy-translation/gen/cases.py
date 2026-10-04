"""Per-case-study specification: Lean path, namespace, documentation and the hand-written theorem."""
CASES = {}

# hypotheses shared verbatim by the FP response-time sections (written once; each theorem lists the ones its
# contract abstracts, in the contract's order)
TASKS = """{sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)"""
H_SPOR = """(H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)"""
H_VALIDJOB = """(H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)"""
H_TS = """(ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)"""
H_CONSTR = """(H_constrained_deadlines : ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)"""
H_FROMTS = """(H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)"""
H_SCHED = """(num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)"""
H_PRIO = """(higher_eq_priority : FP_policy sporadic_task)
    (H_priority_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_antisymmetric : FP_is_antisymmetric_over_task_set higher_eq_priority ts.val)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)"""
H_SEQTASKS = """(H_sequential_tasks : ∀ (j1 j2 : Job) (t : time) (cpu : processor num_cpus),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_task j1 = job_task j2 →
      job_arrival j1 < job_arrival j2 → scheduled_on sched j2 cpu t = true →
      completed job_cost sched j1 t = true)"""
H_TSK = """(tsk : sporadic_task) (task_in_ts : tsk ∈ ts)"""
H_J = """(j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)"""
H_WORST = """(j_has_worstcase_responsetime : ∀ (j0 : Job) (x : Nat), arrives_in arr_seq j0 → job_task j0 = tsk →
      completed job_cost sched j (job_arrival j + x) = true →
      completed job_cost sched j0 (job_arrival j0 + x) = true)"""
HPB = "hp_busy job_task ts num_cpus sched higher_eq_priority tsk"
H_T0 = f"""(t0 : schedule Job num_cpus → Job → time)
    (t0_leq_arrival_time : t0 sched j ≤ job_arrival j)
    (cpu_busy_during_t0_rk : ∀ t : Nat, (decide (t0 sched j ≤ t) && decide (t < job_arrival j)) = true →
      {HPB} t)
    (t0_left_boundary : t0 sched j = 0 ∨ ¬ {HPB} (t0 sched j - 1))"""
CIJ = "is_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk j t0"
THCI = "task_has_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk j t0"
H_CIUNIQ = f"""(carry_in_job_unique : ∀ (tsk_other : sporadic_task) (j1 j2 : Job),
      job_task j1 = tsk_other → {CIJ} j1 →
      job_task j2 = tsk_other → {CIJ} j2 → j1 = j2)"""

def binders(*parts):
    return "\n    ".join(parts)

CASES["2009-RTSS-Lemma1"] = dict(
    path="RTSS2009/Lemma1.lean", namespace="CaseStudies.RTSS2009.Lemma1.ResponseTimeAnalysisFP",
    theorem_name="Lemma1_09",
    doc="""Lemma 1 of Guan et al., RTSS 2009 ("New Response Time Bounds for Fixed Priority Multiprocessor
Scheduling") as stated by the case study `2009-RTSS-Lemma1` (Rocq module `ResponseTimeAnalysisFP`): at the
start `t0` of the level-`tsk` busy period of `j`, at most `m - 1` higher-priority tasks have a carry-in job.""",
    theorem=f"""theorem Lemma1_09 {binders(TASKS, H_SPOR, H_VALIDJOB, H_TS, H_CONSTR, H_FROMTS, H_SCHED, H_PRIO, H_SEQTASKS, H_TSK)}
    (hp_bounds : List (sporadic_task × time))
    {binders(H_J, H_WORST, H_T0, H_CIUNIQ)}
    (has_carry_in_b : sporadic_task → Bool)
    (has_carry_in_P : ∀ tsk0 : sporadic_task, has_carry_in_b tsk0 = true ↔ {THCI} tsk0) :
    sumSeq ts.val (fun tsk0 => (has_carry_in_b tsk0).toNat) ≤ num_cpus - 1 := by
  sorry""")

H_PRIO_NOTRANS = """(higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)"""
RTB = "is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched"
HPT = "higher_priority_task higher_eq_priority tsk"
H_HPB = f"""(hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → {RTB} hp_tsk R)
    (H_hp_bounds_has_interfering_tasks : ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
      {HPT} hp_tsk = true → ∃ R : time, (hp_tsk, R) ∈ hp_bounds)"""
H_HPB_ONLY = f"""(H_hp_bounds_only_interfering_tasks : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → hp_tsk ∈ ts ∧ {HPT} hp_tsk = true)
    (H_hp_bounds_uniq_tasks : (hp_bounds.map (fun p => p.1)).Nodup)"""
H_HPB_COST = """(H_response_time_bounds_ge_cost : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → task_cost hp_tsk ≤ R)
    (H_interfering_tasks_miss_no_deadlines : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)"""
CI = "CI_taskset task_cost task_period tsk hp_bounds R num_cpus"
NC = "NC_taskset task_cost task_period tsk hp_bounds R num_cpus"
TI = "task_interference job_arrival job_cost job_task sched j"
RC = "(R - task_cost tsk + 1)"
EXCEEDS = f"""(∃ (tsk_k : sporadic_task) (R_k : time), (tsk_k, R_k) ∈ {CI} ∧
          min (W task_cost task_period tsk_k R_k R) {RC} <
            min ({TI} tsk_k (job_arrival j) (job_arrival j + R)) {RC}) ∨
        (∃ (tsk_k : sporadic_task) (R_k : time), (tsk_k, R_k) ∈ {NC} ∧
          min (W_NC task_cost task_period tsk_k R) {RC} <
            min ({TI} tsk_k (job_arrival j) (job_arrival j + R)) {RC})"""
MISSED = """∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      (!completed job_cost sched j (job_arrival j + R)) = true →
      (∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk → job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) →"""
IB_CI = f"""(interference_bound_ci : ∀ (j : Job) (tsk_other : sporadic_task) (R_other : time),
      (tsk_other, R_other) ∈ {CI} →
      {TI} tsk_other (job_arrival j) (job_arrival j + R) ≤ W task_cost task_period tsk_other R_other R)
    (interference_bound_nc : ∀ (j : Job) (tsk_other : sporadic_task) (R_other : time),
      (tsk_other, R_other) ∈ {NC} →
      {TI} tsk_other (job_arrival j) (job_arrival j + R) ≤ W_NC task_cost task_period tsk_other R)"""

CASES["2009-RTSS-Method1"] = dict(
    path="RTSS2009/Method1.lean", namespace="CaseStudies.RTSS2009.Method1.ResponseTimeAnalysisFP",
    theorem_name="gn_method1",
    doc="""Response-time bound of Guan et al., RTSS 2009, as stated by the case study `2009-RTSS-Method1` (Rocq module
`ResponseTimeAnalysisFP`, theorem `gn_method1`): a solution `R ≤ d_tsk` of the response-time recurrence with the
carry-in/no-carry-in total interference bound `total_interference_bound_gn` is a response-time bound, given (as
hypotheses) that a deadline miss implies some task exceeds its per-task bound and the per-task interference
bounds themselves.""",
    theorem=f"""theorem gn_method1 {binders(TASKS, H_SPOR, H_VALIDJOB, H_TS, H_CONSTR, H_FROMTS, H_SCHED, H_PRIO_NOTRANS, H_TSK, H_HPB, H_HPB_ONLY, H_HPB_COST)}
    (R : time)
    (H_response_time_recurrence_holds : R = task_cost tsk +
      div_floor (total_interference_bound_gn task_cost task_period tsk hp_bounds R num_cpus) num_cpus)
    (Huniq_hp_bounds : hp_bounds.Nodup)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (Method1_10_09 : {MISSED}
        {EXCEEDS})
    {IB_CI} :
    {RTB} tsk R := by
  sorry""")

H_REC_GN = """(R : time)
    (H_response_time_recurrence_holds : R = task_cost tsk +
      div_floor (total_interference_bound_gn task_cost task_period tsk hp_bounds R num_cpus) num_cpus)
    (Huniq_hp_bounds : hp_bounds.Nodup)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)"""
H_JMISS = """(H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true)
    (H_previous_jobs_of_tsk_completed : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
      job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j0 + R) = true)"""

CASES["2009-RTSS-Extend1_10"] = dict(
    path="RTSS2009/Extend1_10.lean", namespace="CaseStudies.RTSS2009.Extend1_10.ResponseTimeAnalysisFP",
    theorem_name="Method1_10_09",
    doc="""Auxiliary step of the response-time bound of Guan et al., RTSS 2009, as stated by the case study
`2009-RTSS-Extend1_10` (Rocq module `ResponseTimeAnalysisFP`, lemma `Method1_10_09`): if the truncated
interferences of the higher-priority tasks on a job `j` of `tsk` that misses `R` exceed the carry-in/no-carry-in
bound `total_interference_bound_gn`, then some task in the carry-in set exceeds its `W` bound or some task in the
no-carry-in set exceeds its `W_NC` bound.""",
    theorem=f"""theorem Method1_10_09 {binders(TASKS, H_SPOR, H_VALIDJOB, H_TS, H_CONSTR, H_FROMTS, H_SCHED, H_PRIO_NOTRANS, H_TSK, H_HPB, H_HPB_ONLY, H_HPB_COST, H_REC_GN, H_J, H_JMISS)}
    (tsk_other : sporadic_task) (R_other : time)
    (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ hp_bounds)
    (Method1_9 : total_interference_bound_gn task_cost task_period tsk hp_bounds R num_cpus <
      sumSeq hp_bounds (fun (tsk_k, _) =>
        min ({TI} tsk_k (job_arrival j) (job_arrival j + R)) {RC})) :
    {EXCEEDS} := by
  sorry""")

H_SCHED0 = """(num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)"""
H_SCHED1 = """(H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)"""
GN = "total_interference_bound_gn task_cost task_period tsk hp_bounds"
H_REC = f"""(R : time)
    (H_response_time_recurrence_holds : R = task_cost tsk + div_floor ({GN} R num_cpus) num_cpus)
    (Huniq_hp_bounds : hp_bounds.Nodup)"""
H_RLED = """(H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)"""
H_T0B = f"""(t0_leq_arrival_time : t0 sched j ≤ job_arrival j)
    (cpu_busy_during_t0_rk : ∀ t : Nat, (decide (t0 sched j ≤ t) && decide (t < job_arrival j)) = true →
      {HPB} t)
    (t0_left_boundary : t0 sched j = 0 ∨ ¬ {HPB} (t0 sched j - 1))"""
H_PREV = """(H_previous_jobs_of_tsk_completed : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
      job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j0 + R) = true)"""
H_CHI = f"""(chi : time)
    (chi_is_least_solution : ∀ x : time, x = task_cost tsk + div_floor ({GN} x num_cpus) num_cpus → chi ≤ x)"""
H_F = """(f : time)
    (f_is_finish_time : ((!completed job_cost sched j (f - 1)) && completed job_cost sched j f) = true)
    (arrival_before_finish : job_arrival j < f)"""
H_CHISOL = f"""(chi_is_solution : chi = task_cost tsk + div_floor ({GN} chi num_cpus) num_cpus)
    (phi_le_chi : job_arrival j - t0 sched j ≤ chi)"""
LEMMA3_STMT = f"""∀ t : Nat, t < f - t0 sched j → task_cost tsk ≤ t →
      t - task_cost tsk < div_floor ({GN} t num_cpus) num_cpus"""
H_LEMMA2 = """(H_Lemma2_1 : ∀ (tsk_other : sporadic_task) (R_other t1 delta : time),
      (tsk_other, R_other) ∈ NC_taskset task_cost task_period tsk hp_bounds delta num_cpus →
      workload job_task sched tsk_other t1 (t1 + delta) ≤ W_NC task_cost task_period tsk_other delta)
    (H_Lemma2_2 : ∀ (tsk_other : sporadic_task) (R_other t1 delta : time),
      (tsk_other, R_other) ∈ CI_taskset task_cost task_period tsk hp_bounds delta num_cpus →
      workload job_task sched tsk_other t1 (t1 + delta) ≤ W task_cost task_period tsk_other R_other delta)"""
HPB_BASE = binders(TASKS, H_SPOR, H_VALIDJOB, H_TS, H_CONSTR, H_FROMTS)

CASES["2009-RTSS-Theorem1"] = dict(
    path="RTSS2009/Theorem1.lean", namespace="CaseStudies.RTSS2009.Theorem1.ResponseTimeAnalysisFP",
    theorem_name="Theorem1_09",
    doc="""Theorem 1 of Guan et al., RTSS 2009, as stated by the case study `2009-RTSS-Theorem1` (Rocq module
`ResponseTimeAnalysisFP`): a solution `R` of the carry-in/no-carry-in response-time recurrence is a response-time
bound of `tsk`; Lemmas 3 and 4 of the paper (for the job `j` with the worst-case response time, the busy-period
start `t0`, the least solution `chi` and the finish time `f`) are hypotheses `Lemma3` and `Lemma4`.""",
    theorem=f"""theorem Theorem1_09 {binders(HPB_BASE, H_SCHED, H_PRIO_NOTRANS, H_SEQTASKS, H_TSK, H_HPB, H_HPB_COST, H_REC, H_J, H_WORST)}
    (t0 : schedule Job num_cpus → Job → time)
    {binders(H_T0B, H_RLED, H_CHI, H_F, H_CHISOL)}
    (Lemma3 : {LEMMA3_STMT})
    (Lemma4 : {RTB} tsk (chi - (job_arrival j - t0 sched j))) :
    {RTB} tsk R := by
  sorry""")

CASES["2009-RTSS-Lemma3"] = dict(
    path="RTSS2009/Lemma3.lean", namespace="CaseStudies.RTSS2009.Lemma3.ResponseTimeAnalysisFP",
    theorem_name="Lemma3_09",
    doc="""Lemma 3 of Guan et al., RTSS 2009, as stated by the case study `2009-RTSS-Lemma3` (Rocq module
`ResponseTimeAnalysisFP`): for every `t` with `e_tsk ≤ t < f - t0`, where `f` is the finish time of the job `j`
with the worst-case response time and `t0` the start of its level-`tsk` busy period, the carry-in/no-carry-in
interference bound exceeds `t - e_tsk` (`⌊Ω(t)/m⌋ > t - e_tsk`).  Lemma 2 of the paper (the workload bounds
`W_NC` and `W` for no-carry-in and carry-in tasks) is assumed as hypotheses `H_Lemma2_1` and `H_Lemma2_2`.""",
    theorem=f"""theorem Lemma3_09 {binders(HPB_BASE, H_SCHED0, H_SEQTASKS, H_SCHED1, H_PRIO_NOTRANS, H_TSK, H_HPB, H_HPB_COST, H_REC, H_RLED)}
    (j : Job) (t0 : schedule Job num_cpus → Job → time)
    (t0_leq_arrival_time : t0 sched j ≤ job_arrival j)
    (H_j_of_tsk : job_task j = tsk)
    (cpu_busy_during_t0_rk : ∀ t : Nat, (decide (t0 sched j ≤ t) && decide (t < job_arrival j)) = true →
      {HPB} t)
    (t0_left_boundary : t0 sched j = 0 ∨ ¬ {HPB} (t0 sched j - 1))
    {binders(H_WORST)}
    (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    {binders(H_PREV, H_LEMMA2, H_F)} :
    {LEMMA3_STMT} := by
  sorry""")

CASES["2009-RTSS-Lemma4"] = dict(
    path="RTSS2009/Lemma4.lean", namespace="CaseStudies.RTSS2009.Lemma4.ResponseTimeAnalysisFP",
    theorem_name="Lemma4_09",
    doc="""Lemma 4 of Guan et al., RTSS 2009, as stated by the case study `2009-RTSS-Lemma4` (Rocq module
`ResponseTimeAnalysisFP`): for the job `j` with the worst-case response time, `chi - (a_j - t0)` is a
response-time bound of `tsk`, where `chi` is the least solution of the carry-in/no-carry-in recurrence and `t0`
the start of the busy period; Lemma 3 of the paper is the hypothesis `Lemma3`.""",
    theorem=f"""theorem Lemma4_09 {binders(HPB_BASE, H_SCHED, H_PRIO_NOTRANS, H_TSK, H_HPB, H_HPB_COST, H_REC, H_RLED)}
    (j : Job) (t0 : schedule Job num_cpus → Job → time)
    {binders(H_T0B)}
    (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    {binders(H_PREV, H_WORST, H_CHI, H_F, H_CHISOL)}
    (Lemma3 : {LEMMA3_STMT}) :
    {RTB} tsk (chi - (job_arrival j - t0 sched j)) := by
  sorry""")

H_ARRCONS = """(H_arrival_times_are_consistent : ∀ (j : Job) (t : time), arrives_at arr_seq j t = true → job_arrival j = t)
    (H_no_duplicate_arrivals : ∀ t : time, (jobs_arriving_at arr_seq t).Nodup)"""
H_PRIOFP = """(higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (H_priority_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_antisymmetric : FP_is_antisymmetric_over_task_set higher_eq_priority ts.val)"""
HPB_B = "hp_busy job_task ts num_cpus sched tsk higher_eq_priority"
CIJ_B = "is_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched tsk higher_eq_priority j t0"
THCI_B = "task_has_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched tsk higher_eq_priority j t0"
H_T0_B = f"""(t0 : schedule Job num_cpus → Job → time)
    (t0_leq_arrival_time : t0 sched j ≤ job_arrival j)
    (cpu_busy_during_t0_rk : ∀ t : Nat, (decide (t0 sched j ≤ t) && decide (t < job_arrival j)) = true →
      {HPB_B} t)
    (t0_left_boundary : t0 sched j = 0 ∨ ¬ {HPB_B} (t0 sched j - 1))"""
H_CIUNIQ_B = f"""(carry_in_job_unique : ∀ (tsk_other : sporadic_task) (j1 j2 : Job),
      job_task j1 = tsk_other → {CIJ_B} j1 →
      job_task j2 = tsk_other → {CIJ_B} j2 → j1 = j2)"""
LEMMA1_2_STMT = f"""∀ (tsk_other : sporadic_task) (j0 : Job), job_task j0 = tsk_other → {CIJ} j0 →
      carry_in_workload job_cost num_cpus sched j t0 j0 ≤ task_cost tsk_other - 1"""
LEMMA1_2_STMT_B = LEMMA1_2_STMT.replace(CIJ, CIJ_B)

CASES["2009-RTSS-Lemma1_2"] = dict(
    path="RTSS2009/Lemma1_2.lean", namespace="CaseStudies.RTSS2009.Lemma1_2.ResponseTimeAnalysisFP",
    theorem_name="Lemma1_09", snippet_modules=["snippets_ci"],
    doc="""Lemma 1 (second part) of Guan et al., RTSS 2009, as stated by the case study `2009-RTSS-Lemma1_2` (Rocq
module `ResponseTimeAnalysisFP`): the remaining workload at the busy-period start `t0` of every carry-in job is at
most `e_k - 1`.""",
    theorem=f"""theorem Lemma1_09 {binders(TASKS, H_SPOR, H_VALIDJOB, H_TS, H_CONSTR, H_FROMTS, H_SCHED, H_PRIO, H_SEQTASKS, H_TSK)}
    (hp_bounds : List (sporadic_task × time))
    {binders(H_J, H_WORST, H_T0, H_CIUNIQ)} :
    {LEMMA1_2_STMT} := by
  sorry""")

CASES["2009-RTSS-Lemma2-1"] = dict(
    path="RTSS2009/Lemma2_1.lean", namespace="CaseStudies.RTSS2009.Lemma2_1.ResponseTimeAnalysisFP",
    theorem_name="Lemma2_09", snippet_modules=["snippets_ci"],
    doc="""Lemma 2 (no-carry-in case) of Guan et al., RTSS 2009, as stated by the case study `2009-RTSS-Lemma2-1`
(Rocq module `ResponseTimeAnalysisFP`): the workload of a higher-priority task without carry-in job in
`[t0, t0 + t)` is at most `W_NC t`.""",
    theorem=f"""theorem Lemma2_09 {binders(TASKS, H_SPOR, H_VALIDJOB, H_TS, H_CONSTR, H_FROMTS, H_ARRCONS, H_SCHED0, H_SCHED1.replace(chr(10)+'    (H_at_least_one_cpu : 0 < num_cpus)', ''), H_SEQTASKS)}
    (H_at_least_one_cpu : 0 < num_cpus)
    {binders(H_PRIOFP, H_TSK)}
    (hp_bounds : List (sporadic_task × time))
    {binders(H_J, H_WORST, H_T0, H_CIUNIQ)}
    (H_response_time_bound : ∀ (j0 : Job) (tsk_other : sporadic_task) (R_other : time),
      (tsk_other, R_other) ∈ hp_bounds → arrives_in arr_seq j0 → job_task j0 = tsk_other →
      completed job_cost sched j0 (job_arrival j0 + R_other) = true)
    (H_no_deadline_miss : ∀ (tsk_other : sporadic_task) (R_other : time),
      (tsk_other, R_other) ∈ hp_bounds → R_other ≤ task_deadline tsk_other) :
    ∀ (tsk_other : sporadic_task) (R_other : time) (t : Nat),
      no_carry_in_workload_of_task job_arrival job_cost job_task arr_seq num_cpus sched j t0 tsk_other →
      (tsk_other, R_other) ∈ hp_bounds →
      workload job_task sched tsk_other (t0 sched j) (t0 sched j + t) ≤ W_NC task_cost task_period tsk_other t := by
  sorry""")

CASES["2009-RTSS-Lemma2-2"] = dict(
    path="RTSS2009/Lemma2_2.lean", namespace="CaseStudies.RTSS2009.Lemma2_2.ResponseTimeAnalysisFP",
    theorem_name="Lemma2_09", snippet_modules=["snippets_ci"],
    doc="""Lemma 2 (carry-in case) of Guan et al., RTSS 2009, as stated by the case study `2009-RTSS-Lemma2-2` (Rocq
module `ResponseTimeAnalysisFP`): the workload of a higher-priority task with a carry-in job in `[t0, t0 + t)` is
at most `W_CI R_k t`; Lemma 1 of the paper (carry-in workload at most `e_k - 1`) is the hypothesis `Lemma1_09`.""",
    theorem=f"""theorem Lemma2_09 {binders(TASKS, H_SPOR, H_VALIDJOB, H_TS, H_CONSTR, H_FROMTS, H_SCHED0, H_ARRCONS, H_SCHED1.replace(chr(10)+'    (H_at_least_one_cpu : 0 < num_cpus)', ''), H_TSK)}
    (H_at_least_one_cpu : 0 < num_cpus)
    {binders(H_PRIOFP, H_SEQTASKS)}
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known : ∀ (tsk_other : sporadic_task) (R_other : time),
      (tsk_other, R_other) ∈ hp_bounds → {RTB} tsk_other R_other)
    {binders(H_J, H_WORST, H_T0_B, H_CIUNIQ_B)}
    (H_response_time_ge_cost : ∀ (tsk_other : sporadic_task) (R_other : time),
      (tsk_other, R_other) ∈ hp_bounds → task_cost tsk_other ≤ R_other)
    (H_no_deadline_miss : ∀ (tsk_other : sporadic_task) (R_other : time),
      (tsk_other, R_other) ∈ hp_bounds → R_other ≤ task_deadline tsk_other)
    (Lemma1_09 : {LEMMA1_2_STMT_B}) :
    ∀ (tsk_other : sporadic_task) (R_other : time) (t : Nat),
      {THCI_B} tsk_other →
      (tsk_other, R_other) ∈ hp_bounds →
      workload job_task sched tsk_other (t0 sched j) (t0 sched j + t) ≤
        W_CI task_cost task_period tsk_other R_other t := by
  sorry""")

FP = "total_interference_bound_fp task_cost task_period tsk hp_bounds"
CASES["2015-BOOK-Lemma18.1"] = dict(
    path="BOOK2015/Lemma18_1.lean", namespace="CaseStudies.BOOK2015.Lemma18_1.ResponseTimeAnalysisFP",
    theorem_name="Lemma18_1_15", snippet_modules=["snippets_book"],
    doc="""Lemma 18.1 of Baruah, Bertogna & Buttazzo, *Multiprocessor Scheduling for Real-Time Systems* (2015), as
stated by the case study `2015-BOOK-Lemma18.1` (Rocq module `ResponseTimeAnalysisFP`): if fewer than `m` tasks have
higher priority, the least solutions `R1` of the carry-in/no-carry-in recurrence and `R2` of the Bertogna–Cirinei
recurrence are both the task's cost.  This case study defines `max_jobs` and `W` with the response-time bound
(`div_floor (delta + R_tsk - e) p`), unlike the other 2009 case studies.""",
    theorem=f"""theorem Lemma18_1_15 {binders(TASKS, H_SPOR, H_VALIDJOB, H_TS, H_CONSTR, H_FROMTS, H_SCHED, H_PRIO_NOTRANS, H_TSK, H_HPB, H_HPB_COST)}
    (num_higher_priority_tsk : sumSeq hp_bounds (fun (_, _) => 1) < num_cpus)
    (R1 R2 : time)
    (H_response_time_recurrence_holds_gn : R1 = task_cost tsk + div_floor ({GN} R1 num_cpus) num_cpus)
    (H_response_time_recurrence_holds_bertogna : R2 = task_cost tsk + div_floor ({FP} R2) num_cpus)
    (R1_is_least_solution : ∀ x : time, x = task_cost tsk + div_floor ({GN} x num_cpus) num_cpus → R1 ≤ x)
    (R2_is_least_solution : ∀ x : time, x = task_cost tsk + div_floor ({FP} x) num_cpus → R2 ≤ x) :
    sumSeq hp_bounds (fun (_, _) => 1) < num_cpus → R1 = task_cost tsk ∧ R2 = task_cost tsk := by
  sorry""")

H_ARR_LEMMA5 = """(H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)"""
H_PRIOFP2 = """(higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (H_priority_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_antisymmetric : FP_is_antisymmetric_over_task_set higher_eq_priority ts.val)"""
H_HPB_K = f"""(hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → {RTB} hp_tsk R)
    (H_hp_bounds_has_interfering_tasks : ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
      {HPT} hp_tsk = true → ∃ R : time, (hp_tsk, R) ∈ hp_bounds)"""
CHI = "chi_is_least_solution task_cost task_period num_cpus tsk hp_bounds"
H_JLEMMA5 = f"""(j : Job) (t0 : schedule Job num_cpus → Job → time)
    (t0_leq_arrival_time : t0 sched j ≤ job_arrival j)
    (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
      job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j) = true)
    (cpu_busy_during_t0_rk : ∀ t : Nat, (decide (t0 sched j ≤ t) && decide (t < job_arrival j)) = true →
      {HPB} t)
    (t0_left_boundary : t0 sched j = 0 ∨ ¬ {HPB} (t0 sched j - 1))
    (phi : time) (phi_is_defined : phi = job_arrival j - t0 sched j)
    (H_phi : Nat)
    (H_phi_is_minimal : 0 < H_phi ∧ H_phi_satisfy task_period tsk chi_min phi H_phi = true ∧
      ∀ x : Nat, 0 < x → H_phi_satisfy task_period tsk chi_min phi x = true → H_phi ≤ x)"""
HTHL = "job_is_hth_after_j task_period job_arrival job_task arr_seq tsk j"
MRPT = "max_R_phi_term task_period tsk chi_min phi H_phi"

CASES["2009-RTSS-Lemma5"] = dict(
    path="RTSS2009/Lemma5.lean", namespace="CaseStudies.RTSS2009.Lemma5.ResponseTimeAnalysisFP",
    theorem_name="Lemma5_09", snippet_modules=["snippets_arb"],
    doc="""Lemma 5 of Guan et al., RTSS 2009 (arbitrary deadlines), as stated by the case study `2009-RTSS-Lemma5`
(Rocq module `ResponseTimeAnalysisFP`): with `chi_min h` the least solution of the `h`-job recurrence and `H_phi`
the least `h ≥ 1` with `chi_min h ≤ h p + phi`, `max_{1≤h≤H_phi} (chi_min h - ((h-1) p + phi))` is a response-time
bound of `tsk`.  Lemma 2 of the paper and the selection of a worst-case job from a tight chain are hypotheses.""",
    theorem=f"""theorem Lemma5_09 {binders(TASKS, H_SPOR, H_ARR_LEMMA5, H_VALIDJOB, H_TS, H_FROMTS, H_SCHED, H_PRIOFP2, H_SEQTASKS, H_TSK, H_HPB_K, H_HPB_COST)}
    (chi_min : Nat → time)
    (chi_min_spec : ∀ h : Nat, {CHI} h (chi_min h))
    (Huniq_hp_bounds : hp_bounds.Nodup)
    {H_JLEMMA5}
    (H_Lemma2_1 : ∀ (tsk_other : sporadic_task) (R_other t1 : time) (h : Nat) (delta : time),
      (tsk_other, R_other) ∈ NC_taskset task_cost task_period tsk hp_bounds delta num_cpus h →
      workload job_task sched tsk_other t1 (t1 + delta) ≤ W_NC task_cost task_period tsk_other delta)
    (H_Lemma2_2 : ∀ (tsk_other : sporadic_task) (R_other t1 : time) (h : Nat) (delta : time),
      (tsk_other, R_other) ∈ CI_taskset task_cost task_period tsk hp_bounds delta num_cpus h →
      workload job_task sched tsk_other t1 (t1 + delta) ≤ W task_cost task_period tsk_other R_other delta)
    (H_jobs_before_H_phi_do_not_complete_by_next_release : ∀ (h : Nat) (j_h : Job), h < H_phi →
      {HTHL} h j_h → (!completed job_cost sched j_h (job_arrival j_h + task_period tsk)) = true)
    (H_current_chain_reaches_H_phi : ∃ j_H_phi : Job, {HTHL} H_phi j_H_phi)
    (H_Lemma1_selects_worstcase_job_from_tight_chain : ∀ (h_last : Nat) (j_last : Job),
      tight_chain_ending_at task_period job_arrival job_cost job_task arr_seq num_cpus sched tsk j h_last j_last →
      ∃ (h_worst : Nat) (j_worst : Job) (f_worst : time),
        worstcase_job_selected_from_tight_chain task_period job_arrival job_cost job_task arr_seq num_cpus sched
          tsk j h_last h_worst j_worst f_worst) :
    {RTB} tsk ({MRPT}) := by
  sorry""")

CASES["2009-RTSS-Theorem2"] = dict(
    path="RTSS2009/Theorem2.lean", namespace="CaseStudies.RTSS2009.Theorem2.ResponseTimeAnalysisFP",
    theorem_name="Theorem2", snippet_modules=["snippets_arb"],
    doc="""Theorem 2 of Guan et al., RTSS 2009 (arbitrary deadlines), as stated by the case study `2009-RTSS-Theorem2`
(Rocq module `ResponseTimeAnalysisFP`): with `H` the least `h ≥ 1` with `chi_min h ≤ h p`,
`max_{1≤h≤H} (chi_min h - (h-1) p)` is a response-time bound of `tsk`; Lemma 5 is the hypothesis `Lemma5`.  In this
case study `f_chi` passes `h` and `num_cpus` to `total_interference_bound_gn_arbitrary` in swapped positions (the
definition takes `… num_cpus h`); translated as written.""",
    theorem=f"""theorem Theorem2 {binders(TASKS, H_SPOR, H_VALIDJOB, H_TS, H_FROMTS, H_SCHED, H_PRIO_NOTRANS, H_TSK, H_HPB_K, H_HPB_COST)}
    (chi_min : Nat → time)
    (chi_min_spec : ∀ h : Nat, 0 < h → {CHI} h (chi_min h))
    (Huniq_hp_bounds : hp_bounds.Nodup)
    {H_JLEMMA5}
    (H : Nat)
    (H_is_minimal : 0 < H ∧ H_satisfy task_period tsk chi_min H = true ∧
      ∀ x : Nat, 0 < x → H_satisfy task_period tsk chi_min x = true → H ≤ x)
    (Lemma5 : {RTB} tsk ({MRPT})) :
    {RTB} tsk (max_R_term task_period tsk chi_min H) := by
  sorry""")

H_VALIDTS14 = """(ts : taskset_of sporadic_task)
    (H_valid_task_parameters : ∀ tsk : sporadic_task, tsk ∈ ts →
      0 < task_cost tsk ∧ 0 < task_period tsk ∧ 0 < task_deadline tsk ∧
        task_cost tsk ≤ task_deadline tsk ∧ task_cost tsk < task_period tsk)"""
H_SCHED14 = """(num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (previous_job_must_finished : ∀ (j1 j2 : Job) (t : time), scheduled sched j1 t = true →
      job_task j1 = job_task j2 → job_arrival j2 < job_arrival j1 → completed job_cost sched j2 t = true)"""
NCJ = "number_of_carry_in_jobs job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk"
THCI14 = "task_has_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk"
def boundary(to, ro, xi, jx):
    return f"""((arrives_in arr_seq {jx} ∧ job_task {jx} = {to} ∧ critical_instant ≤ job_arrival {jx}) ∧
          (0 < {xi} ∧
            ((jobs_arrived_before arr_seq (job_arrival {jx})).filter (fun j0 =>
              decide (job_task j0 = {to}) && decide (critical_instant ≤ job_arrival j0))).length = {xi} - 1) ∧
          job_arrival {jx} = critical_instant +
            (task_cost {to} - 1 + ({NCJ} {to} critical_instant + ({xi} - 1)) * task_period {to} - {ro}) ∧
          arrives_in arr_seq {jx} ∧ job_task {jx} = {to} ∧
          (∀ j1 : Job, arrives_in arr_seq j1 → job_task j1 = {to} → job_arrival j1 < job_arrival {jx} →
            completed job_cost sched j1 (job_arrival {jx}) = true))"""
def minimal(to, ro, xi):
    return f"""(let k := {NCJ} {to} critical_instant + ({xi} - 1);
          0 < k ∧ {ro} + (k * task_cost {to} - 1) ≤ task_cost {to} - 1 + k * task_period {to} ∧
            ∀ k0 : Nat, 0 < k0 → {ro} + (k0 * task_cost {to} - 1) ≤ task_cost {to} - 1 + k0 * task_period {to} →
              k ≤ k0)"""

CASES["2014-RTCSA-Lemma4"] = dict(
    path="RTCSA2014/Lemma4.lean", namespace="CaseStudies.RTCSA2014.Lemma4.ResponseTimeAnalysisFP",
    theorem_name="Lemma4_14", snippet_modules=["snippets_ci", "snippets_2014"],
    doc="""Lemma 4 of the RTCSA 2014 paper ("Improving the Response Time Analysis of Global Fixed-Priority
Multiprocessor Scheduling") as stated by the case study `2014-RTCSA-Lemma4` (Rocq module `ResponseTimeAnalysisFP`):
the workload of a higher-priority task with a carry-in job in `[critical_instant, critical_instant + t)` is at most
the improved carry-in bound `W_CI R_k t`.  The carry-in workload bound (`Lemma1_09`), the no-carry-in workload bound
(`Lemma2`) and the existence of a tight release chain (`Lemma1_14`) are hypotheses; the section-local chain
predicates are unfolded as in the Rocq contract.  The conclusion quantifies its own `tsk_other` and `R_other`
(shadowing the section variables of the same names, which only the chain hypotheses mention).""",
    theorem=f"""theorem Lemma4_14 {binders(TASKS, H_SPOR, H_VALIDJOB, H_VALIDTS14, H_FROMTS, H_SCHED14, H_PRIOFP, H_SEQTASKS, H_TSK, H_HPB_K, H_HPB_COST)}
    (H_hp_bounds_uniq : hp_bounds.Nodup)
    (critical_instant : time)
    (critical_instant_left_boundary : critical_instant = 0 ∨ ¬ {HPB} (critical_instant - 1))
    (critical_instant_is_busy : ts.val.countP (fun tsk_other =>
      task_is_scheduled job_task sched tsk_other critical_instant &&
        higher_priority_task higher_eq_priority tsk tsk_other) = num_cpus)
    (Lemma1_09 : ∀ (tsk_other : sporadic_task) (t : time), {THCI14} tsk_other t →
      carry_in_workload job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk tsk_other t ≤
        {NCJ} tsk_other t * task_cost tsk_other - 1)
    (Lemma2 : ∀ (tsk_other : sporadic_task) (R_other t : time) (delta : Nat),
      no_carry_in_workload_of_task job_arrival job_cost job_task arr_seq num_cpus sched tsk_other t →
      (tsk_other, R_other) ∈ hp_bounds →
      workload job_task sched tsk_other t (t + delta) ≤ W_NC task_cost task_period tsk_other delta)
    (Lemma1_14 : ∀ (tsk_other : sporadic_task) (R_other : time), {THCI14} tsk_other critical_instant →
      (tsk_other, R_other) ∈ hp_bounds → task_cost tsk_other < R_other →
      ∃ (xi : time) (j_xi : Job),
        {boundary('tsk_other', 'R_other', 'xi', 'j_xi')} ∧
        {minimal('tsk_other', 'R_other', 'xi')})
    (tsk_other : sporadic_task) (R_other delta xi : time) (j_xi : Job)
    (H_tight_chain_boundary_job : {boundary('tsk_other', 'R_other', 'xi', 'j_xi')})
    (H_tight_chain_prefix_job_count_is_minimal : {minimal('tsk_other', 'R_other', 'xi')}) :
    ∀ (tsk_other0 : sporadic_task) (R_other0 : time) (t : Nat), {THCI14} tsk_other0 critical_instant →
      (tsk_other0, R_other0) ∈ hp_bounds →
      workload job_task sched tsk_other0 critical_instant (critical_instant + t) ≤
        W_CI task_cost task_period tsk_other0 R_other0 t := by
  sorry""")

H_PRIO14 = """(higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)"""
H_HPB14 = f"""(hp_bounds : List (sporadic_task × time))
    (task_in_hpbound_in_ts : ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds →
      hp_tsk ∈ ts ∧ {HPT} hp_tsk = true)
    (H_response_time_of_interfering_tasks_is_known : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → {RTB} hp_tsk R)
    (H_hp_bounds_has_interfering_tasks : ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
      {HPT} hp_tsk = true → ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    {H_HPB_COST}
    (H_hp_bounds_uniq : hp_bounds.Nodup)
    (critical_instant : time)
    (critical_instant_left_boundary : critical_instant = 0 ∨ ¬ {HPB} (critical_instant - 1))
    (critical_instant_is_busy : ts.val.countP (fun tsk_other =>
      task_is_scheduled job_task sched tsk_other critical_instant &&
        higher_priority_task higher_eq_priority tsk tsk_other) = num_cpus)"""
RTCSA = "total_interference_bound_rtcsa14 task_cost task_period tsk"

CASES["2014-RTCSA-Lemma5"] = dict(
    path="RTCSA2014/Lemma5.lean", namespace="CaseStudies.RTCSA2014.Lemma5.ResponseTimeAnalysisFP",
    theorem_name="Lemma5_14", snippet_modules=["snippets_2014"],
    doc="""Lemma 5 of the RTCSA 2014 paper as stated by the case study `2014-RTCSA-Lemma5` (Rocq module
`ResponseTimeAnalysisFP`): given a split of the higher-priority tasks into a carry-in set `CI_taskset`
(fewer than `m` tasks, each with a pending job at the critical instant) and a no-carry-in set `NC_taskset`, with the
corresponding workload bounds as hypotheses (`lemma2`, `lemma4`), the least solution `R ≤ d_tsk` of the recurrence
with the bound `total_interference_bound_rtcsa14` is a response-time bound of `tsk`.""",
    theorem=f"""theorem Lemma5_14 {binders(TASKS, H_SPOR, H_VALIDJOB, H_VALIDTS14, H_CONSTR, H_FROMTS, H_SCHED14, H_PRIO14, H_TSK, H_HPB14)}
    (CI_taskset NC_taskset : List (sporadic_task × time))
    (H_CI_taskset_sub_hp_bounds : ∀ p, p ∈ CI_taskset → p ∈ hp_bounds)
    (has_carry_in_job : ∀ (tsk_other : sporadic_task) (R_other : time), (tsk_other, R_other) ∈ CI_taskset →
      ∃ j0 : Job, arrives_in arr_seq j0 ∧ job_task j0 = tsk_other ∧ job_arrival j0 < critical_instant ∧
        (!completed job_cost sched j0 critical_instant) = true)
    (H_CI_taskset_size : CI_taskset.length ≤ num_cpus - 1)
    (H_NC_taskset_sub_hp_bounds : ∀ p, p ∈ NC_taskset → p ∈ hp_bounds)
    (non_carry_in_job : ∀ (tsk_other : sporadic_task) (R_other : time), (tsk_other, R_other) ∈ NC_taskset →
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk_other → job_arrival j0 < critical_instant →
        completed job_cost sched j0 critical_instant = true)
    (H_hp_covered_by_CI_or_NC : ∀ x : sporadic_task × time, x ∈ hp_bounds →
      (decide (x ∈ CI_taskset) || decide (x ∈ NC_taskset)) = true)
    (H_CI_NC_disjoint : ∀ x : sporadic_task × time, x ∈ CI_taskset → (!decide (x ∈ NC_taskset)) = true)
    (H_CI_taskset_uniq : CI_taskset.Nodup) (H_NC_taskset_uniq : NC_taskset.Nodup)
    (lemma2 : ∀ (tsk_other : sporadic_task) (R_other t1 : time) (delta : Nat),
      (tsk_other, R_other) ∈ NC_taskset → (tsk_other, R_other) ∈ hp_bounds →
      workload job_task sched tsk_other t1 (t1 + delta) ≤ W_NC task_cost task_period tsk_other delta)
    (lemma4 : ∀ (tsk_other : sporadic_task) (R_other t1 : time) (delta : Nat),
      (tsk_other, R_other) ∈ CI_taskset → (tsk_other, R_other) ∈ hp_bounds →
      workload job_task sched tsk_other t1 (t1 + delta) ≤ W_CI task_cost task_period tsk_other R_other delta) :
    ∀ R : Nat, R ≤ task_deadline tsk →
      response_time_recurrence task_cost task_period num_cpus tsk R CI_taskset NC_taskset →
      R_is_minimal_solution task_cost task_period num_cpus tsk R CI_taskset NC_taskset →
      {RTB} tsk R := by
  sorry""")

VCI = "valid_CI_taskset job_arrival job_cost job_task arr_seq num_cpus sched hp_bounds critical_instant"
CASES["2014-RTCSA-Theorem3"] = dict(
    path="RTCSA2014/Theorem3.lean", namespace="CaseStudies.RTCSA2014.Theorem3.ResponseTimeAnalysisFP",
    theorem_name="Theorem3_14", snippet_modules=["snippets_2014"],
    doc="""Theorem 3 of the RTCSA 2014 paper as stated by the case study `2014-RTCSA-Theorem3` (Rocq module
`ResponseTimeAnalysisFP`): the least upper bound `R_global` of the solutions `R_of_CI CI` over all valid carry-in
sets `CI` is a response-time bound of `tsk`; Lemma 5 (for every carry-in set) is the hypothesis `lemma5`.""",
    theorem=f"""theorem Theorem3_14 {binders(TASKS, H_SPOR, H_VALIDJOB, H_TS, H_CONSTR, H_FROMTS, H_SCHED14, H_PRIO14, H_TSK, H_HPB14)}
    (exist_j_released_at_criticalinstant : ∃ j : Job,
      arrives_in arr_seq j ∧ job_task j = tsk → job_arrival j = critical_instant)
    (R_of_CI : List (sporadic_task × time) → time)
    (H_response_time_recurrence_holds : ∀ CI_taskset : List (sporadic_task × time), {VCI} CI_taskset →
      let NC_taskset := hp_bounds.filter (fun x => !decide (x ∈ CI_taskset));
      let R := R_of_CI CI_taskset;
      R = task_cost tsk + div_floor ({RTCSA} CI_taskset NC_taskset R) num_cpus)
    (R_is_minimal_solution : ∀ CI_taskset : List (sporadic_task × time), {VCI} CI_taskset →
      let NC_taskset := hp_bounds.filter (fun x => !decide (x ∈ CI_taskset));
      let R := R_of_CI CI_taskset;
      ∀ x : time, x = task_cost tsk + div_floor ({RTCSA} CI_taskset NC_taskset x) num_cpus → R ≤ x)
    (H_response_time_no_larger_than_deadline : ∀ CI_taskset : List (sporadic_task × time), {VCI} CI_taskset →
      R_of_CI CI_taskset ≤ task_deadline tsk)
    (R_global : time)
    (H_R_global_upper : ∀ CI_taskset : List (sporadic_task × time), {VCI} CI_taskset →
      R_of_CI CI_taskset ≤ R_global)
    (H_R_global_least : ∀ R' : Nat,
      (∀ CI_taskset : List (sporadic_task × time), {VCI} CI_taskset → R_of_CI CI_taskset ≤ R') → R_global ≤ R')
    (lemma5 : ∀ CI_taskset : List (sporadic_task × time), {RTB} tsk (R_of_CI CI_taskset)) :
    {RTB} tsk R_global := by
  sorry""")
