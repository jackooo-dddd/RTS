Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BusyIntervalServiceInversionSemanticSource.
Import BusyIntervalServiceInversionSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.supply prosa.analysis.definitions.service.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.blackout_implies_no_service_inversion". Abort.
Print statement_blackout_implies_no_service_inversion.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.blackout_implies_no_service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.idle_implies_no_service_inversion". Abort.
Print statement_idle_implies_no_service_inversion.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.idle_implies_no_service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.receives_service_implies_no_service_inversion". Abort.
Print statement_receives_service_implies_no_service_inversion.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.receives_service_implies_no_service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_cat". Abort.
Print statement_service_inversion_cat.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_cat". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_widen". Abort.
Print statement_service_inversion_widen.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_widen". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_supply_sched". Abort.
Print statement_service_inversion_supply_sched.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_supply_sched". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.service_inv_implies_priority_inv". Abort.
Print statement_service_inv_implies_priority_inv.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.service_inv_implies_priority_inv". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.cumul_service_inv_le_cumul_priority_inv". Abort.
Print statement_cumul_service_inv_le_cumul_priority_inv.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.cumul_service_inv_le_cumul_priority_inv". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.cumulative_service_inversion_from_one_job". Abort.
Print statement_cumulative_service_inversion_from_one_job.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.cumulative_service_inversion_from_one_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.lp_job_bounded_service". Abort.
Print statement_lp_job_bounded_service.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.lp_job_bounded_service". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.lp_job_bounded_service_max". Abort.
Print statement_lp_job_bounded_service_max.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.lp_job_bounded_service_max". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_is_bounded". Abort.
Print statement_service_inversion_is_bounded.
Goal True. idtac "END|prosa.analysis.facts.busy_interval.service_inversion.service_inversion_is_bounded". Abort.
