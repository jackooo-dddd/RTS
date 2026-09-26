Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.IdealScheduleSemanticSource.
Import IdealScheduleSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
Require Import prosa.behavior.all prosa.model.processor.platform_properties prosa.model.processor.supply prosa.model.processor.ideal prosa.model.schedule.scheduled.
(* display-only: the official elaborated-type evidence was printed with another
   [processor_state] in scope, so the ideal one is displayed as [ideal.processor_state] *)
Module IdealScheduleProbeDisplay. Definition processor_state := tt. End IdealScheduleProbeDisplay.
Import IdealScheduleProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_is_a_uniprocessor_model". Abort.
Print statement_ideal_proc_model_is_a_uniprocessor_model.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_is_a_uniprocessor_model". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.service_in_service_on". Abort.
Print statement_service_in_service_on.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.service_in_service_on". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.service_in_def". Abort.
Print statement_service_in_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.service_in_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_ensures_ideal_progress". Abort.
Print statement_ideal_proc_model_ensures_ideal_progress.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_ensures_ideal_progress". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_provides_unit_service". Abort.
Print statement_ideal_proc_model_provides_unit_service.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_provides_unit_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_provides_unit_supply". Abort.
Print statement_ideal_proc_model_provides_unit_supply.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_provides_unit_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.scheduled_in_def". Abort.
Print statement_scheduled_in_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.scheduled_in_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.scheduled_at_def". Abort.
Print statement_scheduled_at_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.scheduled_at_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.service_on_def". Abort.
Print statement_service_on_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.service_on_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.service_at_def". Abort.
Print statement_service_at_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.service_at_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.service_in_is_scheduled_in". Abort.
Print statement_service_in_is_scheduled_in.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.service_in_is_scheduled_in". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.service_at_is_scheduled_at". Abort.
Print statement_service_at_is_scheduled_at.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.service_at_is_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_fully_consuming". Abort.
Print statement_ideal_proc_model_fully_consuming.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_fully_consuming". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_has_supply". Abort.
Print statement_ideal_proc_has_supply.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_has_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_sched_case_analysis". Abort.
Print statement_ideal_proc_model_sched_case_analysis.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_proc_model_sched_case_analysis". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_sched_implies_not_idle". Abort.
Print statement_ideal_sched_implies_not_idle.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_sched_implies_not_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.ideal_not_idle_implies_sched". Abort.
Print statement_ideal_not_idle_implies_sched.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.ideal_not_idle_implies_sched". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.scheduled_job_at_def". Abort.
Print statement_scheduled_job_at_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.scheduled_job_at_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.schedule.is_idle_def". Abort.
Print statement_is_idle_def.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.schedule.is_idle_def". Abort.
