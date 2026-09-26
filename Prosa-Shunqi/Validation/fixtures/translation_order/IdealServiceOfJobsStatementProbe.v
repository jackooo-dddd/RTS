Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.IdealServiceOfJobsSemanticSource.
Import IdealServiceOfJobsSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
Require Import prosa.behavior.all prosa.model.processor.platform_properties prosa.model.processor.supply prosa.model.schedule.scheduled.
Require Import prosa.model.aggregate.service_of_jobs.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.service_of_jobs.low_service_implies_existence_of_idle_time_rs". Abort.
Print statement_low_service_implies_existence_of_idle_time_rs.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.service_of_jobs.low_service_implies_existence_of_idle_time_rs". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.ideal.service_of_jobs.low_service_implies_existence_of_idle_time". Abort.
Print statement_low_service_implies_existence_of_idle_time.
Goal True. idtac "END|prosa.analysis.facts.model.ideal.service_of_jobs.low_service_implies_existence_of_idle_time". Abort.
