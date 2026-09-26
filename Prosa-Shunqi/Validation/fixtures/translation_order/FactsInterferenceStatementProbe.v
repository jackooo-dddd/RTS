Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsInterferenceSemanticSource.
Import FactsInterferenceSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
Require Import prosa.behavior.all prosa.model.processor.platform_properties prosa.model.processor.supply prosa.model.schedule.scheduled.
Require Import prosa.model.priority.classes prosa.analysis.definitions.priority.classes prosa.model.aggregate.service_of_jobs prosa.analysis.definitions.service.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.another_task_hep_job_split_hp_ep". Abort.
Print statement_another_task_hep_job_split_hp_ep.
Goal True. idtac "END|prosa.analysis.facts.interference.another_task_hep_job_split_hp_ep". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.hep_interference_another_task_split". Abort.
Print statement_hep_interference_another_task_split.
Goal True. idtac "END|prosa.analysis.facts.interference.hep_interference_another_task_split". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.cumulative_hep_interference_split_tasks_new". Abort.
Print statement_cumulative_hep_interference_split_tasks_new.
Goal True. idtac "END|prosa.analysis.facts.interference.cumulative_hep_interference_split_tasks_new". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_hep_job_interference_without_supply". Abort.
Print statement_no_hep_job_interference_without_supply.
Goal True. idtac "END|prosa.analysis.facts.interference.no_hep_job_interference_without_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_hep_task_interference_without_supply". Abort.
Print statement_no_hep_task_interference_without_supply.
Goal True. idtac "END|prosa.analysis.facts.interference.no_hep_task_interference_without_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_hep_job_interference_when_idle". Abort.
Print statement_no_hep_job_interference_when_idle.
Goal True. idtac "END|prosa.analysis.facts.interference.no_hep_job_interference_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_hep_task_interference_when_idle". Abort.
Print statement_no_hep_task_interference_when_idle.
Goal True. idtac "END|prosa.analysis.facts.interference.no_hep_task_interference_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.interference_ahep_def". Abort.
Print statement_interference_ahep_def.
Goal True. idtac "END|prosa.analysis.facts.interference.interference_ahep_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.interference_athep_def". Abort.
Print statement_interference_athep_def.
Goal True. idtac "END|prosa.analysis.facts.interference.interference_athep_def". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_ahep_interference_when_scheduled". Abort.
Print statement_no_ahep_interference_when_scheduled.
Goal True. idtac "END|prosa.analysis.facts.interference.no_ahep_interference_when_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_ahep_interference_when_served". Abort.
Print statement_no_ahep_interference_when_served.
Goal True. idtac "END|prosa.analysis.facts.interference.no_ahep_interference_when_served". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_athep_interference_when_scheduled". Abort.
Print statement_no_athep_interference_when_scheduled.
Goal True. idtac "END|prosa.analysis.facts.interference.no_athep_interference_when_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.athep_interference_iff". Abort.
Print statement_athep_interference_iff.
Goal True. idtac "END|prosa.analysis.facts.interference.athep_interference_iff". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.athep_interference_if". Abort.
Print statement_athep_interference_if.
Goal True. idtac "END|prosa.analysis.facts.interference.athep_interference_if". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.no_ahep_interference_when_scheduled_lp". Abort.
Print statement_no_ahep_interference_when_scheduled_lp.
Goal True. idtac "END|prosa.analysis.facts.interference.no_ahep_interference_when_scheduled_lp". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.cumulative_i_ohep_eq_service_of_ohep". Abort.
Print statement_cumulative_i_ohep_eq_service_of_ohep.
Goal True. idtac "END|prosa.analysis.facts.interference.cumulative_i_ohep_eq_service_of_ohep". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.interference.cumulative_i_thep_eq_service_of_othep". Abort.
Print statement_cumulative_i_thep_eq_service_of_othep.
Goal True. idtac "END|prosa.analysis.facts.interference.cumulative_i_thep_eq_service_of_othep". Abort.
