Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsTaskScheduleSemanticSource.
Import FactsTaskScheduleSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
Require Import prosa.behavior.all prosa.model.processor.platform_properties prosa.model.processor.supply prosa.model.schedule.scheduled prosa.model.task.concept prosa.analysis.definitions.task_schedule.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.task_served_task_scheduled". Abort.
Print statement_task_served_task_scheduled.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.task_served_task_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.task_served_eq_task_scheduled". Abort.
Print statement_task_served_eq_task_scheduled.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.task_served_eq_task_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.no_task_scheduled_when_idle". Abort.
Print statement_no_task_scheduled_when_idle.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.no_task_scheduled_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.no_task_served_when_idle". Abort.
Print statement_no_task_served_when_idle.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.no_task_served_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.job_of_scheduled_task". Abort.
Print statement_job_of_scheduled_task.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.job_of_scheduled_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.job_of_task_scheduled". Abort.
Print statement_job_of_task_scheduled.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.job_of_task_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.job_of_other_task_scheduled". Abort.
Print statement_job_of_other_task_scheduled.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.job_of_other_task_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.job_of_other_task_scheduled'". Abort.
Print statement_job_of_other_task_scheduled'.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.job_of_other_task_scheduled'". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.job_of_task_not_served". Abort.
Print statement_job_of_task_not_served.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.job_of_task_not_served". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.task_schedule.task_served_at_eq_job_of_task". Abort.
Print statement_task_served_at_eq_job_of_task.
Goal True. idtac "END|prosa.analysis.facts.model.task_schedule.task_served_at_eq_job_of_task". Abort.
