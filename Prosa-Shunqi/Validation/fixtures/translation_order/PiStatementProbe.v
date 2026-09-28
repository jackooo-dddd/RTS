Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BusyIntervalPiSemanticSource.
Import BusyIntervalPiSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.lower_priority_job_scheduled_implies_no_preemption_time". Abort.
Print statement_lower_priority_job_scheduled_implies_no_preemption_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.lower_priority_job_scheduled_implies_no_preemption_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.lower_priority_job_continuously_scheduled". Abort.
Print statement_lower_priority_job_continuously_scheduled.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.lower_priority_job_continuously_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.low_priority_job_arrives_before_busy_interval_prefix". Abort.
Print statement_low_priority_job_arrives_before_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.low_priority_job_arrives_before_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.low_priority_job_scheduled_before_busy_interval_prefix". Abort.
Print statement_low_priority_job_scheduled_before_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.low_priority_job_scheduled_before_busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.lp_job_should_arrive_early_for_pi". Abort.
Print statement_lp_job_should_arrive_early_for_pi.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.lp_job_should_arrive_early_for_pi". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.lower_priority_jobs_never_scheduled_if_no_inversion". Abort.
Print statement_lower_priority_jobs_never_scheduled_if_no_inversion.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.lower_priority_jobs_never_scheduled_if_no_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.no_preemption_time_before_pi". Abort.
Print statement_no_preemption_time_before_pi.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.no_preemption_time_before_pi". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.pi_job_remains_scheduled". Abort.
Print statement_pi_job_remains_scheduled.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.pi_job_remains_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.pi_continuous". Abort.
Print statement_pi_continuous.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.pi_continuous". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.only_one_pi_job". Abort.
Print statement_only_one_pi_job.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.only_one_pi_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.busy_interval_pi_cases". Abort.
Print statement_busy_interval_pi_cases.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.busy_interval_pi_cases". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.max_lp_nonpreemptive_segment". Abort.
Check @max_lp_nonpreemptive_segment.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.max_lp_nonpreemptive_segment". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.max_np_job_segment_bounded_by_max_np_task_segment". Abort.
Print statement_max_np_job_segment_bounded_by_max_np_task_segment.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.max_np_job_segment_bounded_by_max_np_task_segment". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.hp_job_not_scheduled_before_quiet_time". Abort.
Print statement_hp_job_not_scheduled_before_quiet_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.hp_job_not_scheduled_before_quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case1". Abort.
Print statement_preemption_time_exists_case1.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case2". Abort.
Print statement_preemption_time_exists_case2.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.no_intermediate_preemption_point". Abort.
Print statement_no_intermediate_preemption_point.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.no_intermediate_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.continuously_scheduled_between_preemption_points". Abort.
Print statement_continuously_scheduled_between_preemption_points.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.continuously_scheduled_between_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.first_preemption_time". Abort.
Print statement_first_preemption_time.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.first_preemption_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.preemption_time_le_max_len_of_np_segment". Abort.
Print statement_preemption_time_le_max_len_of_np_segment.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.preemption_time_le_max_len_of_np_segment". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case3". Abort.
Print statement_preemption_time_exists_case3.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.preemption_time_exists_case3". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.preemption_time_exists". Abort.
Print statement_preemption_time_exists.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.preemption_time_exists". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.no_priority_inversion_after_preemption_point". Abort.
Print statement_no_priority_inversion_after_preemption_point.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.no_priority_inversion_after_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.pi.priority_inversion_occurs_only_till_preemption_point". Abort.
Print statement_priority_inversion_occurs_only_till_preemption_point.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.pi.priority_inversion_occurs_only_till_preemption_point". Abort.
