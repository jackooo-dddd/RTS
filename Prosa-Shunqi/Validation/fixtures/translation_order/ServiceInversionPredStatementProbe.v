Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.ServiceInversionPredSemanticSource.
Import ServiceInversionPredSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.model.priority.classes.
Require Import prosa.analysis.definitions.service.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.pred.service_inversion". Abort.
Check @service_inversion.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.pred.service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.pred.cumulative_service_inversion". Abort.
Check @cumulative_service_inversion.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.pred.cumulative_service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_of_job_is_bounded_by". Abort.
Check @pred_service_inversion_of_job_is_bounded_by.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_of_job_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_is_bounded_by". Abort.
Check @pred_service_inversion_is_bounded_by.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_is_bounded_by". Abort.
