Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.HepAtPtSemanticSource.
Import HepAtPtSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.instant_t_is_not_idle". Abort.
Print statement_instant_t_is_not_idle.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.instant_t_is_not_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority_lt". Abort.
Print statement_scheduled_at_preemption_time_implies_higher_or_equal_priority_lt.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority_lt". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority_eq". Abort.
Print statement_scheduled_at_preemption_time_implies_higher_or_equal_priority_eq.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority_eq". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority". Abort.
Print statement_scheduled_at_preemption_time_implies_higher_or_equal_priority.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_higher_or_equal_priority". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_arrived_between_within_busy_interval". Abort.
Print statement_scheduled_at_preemption_time_implies_arrived_between_within_busy_interval.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_arrived_between_within_busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job_at_preemption_point". Abort.
Print statement_not_quiet_implies_exists_scheduled_hp_job_at_preemption_point.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job_at_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job_after_preemption_point". Abort.
Print statement_not_quiet_implies_exists_scheduled_hp_job_after_preemption_point.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job_after_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job". Abort.
Print statement_not_quiet_implies_exists_scheduled_hp_job.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.hep_at_pt.not_quiet_implies_exists_scheduled_hp_job". Abort.
