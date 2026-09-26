Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BusyPrefixSemanticSource.
Import BusyPrefixSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.analysis.abstract.definitions.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.busy_prefix.service_inversion_of_job_is_bounded_by". Abort.
Check @service_inversion_of_job_is_bounded_by.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.busy_prefix.service_inversion_of_job_is_bounded_by". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.busy_prefix.service_inversion_is_bounded_by". Abort.
Check @service_inversion_is_bounded_by.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.busy_prefix.service_inversion_is_bounded_by". Abort.
