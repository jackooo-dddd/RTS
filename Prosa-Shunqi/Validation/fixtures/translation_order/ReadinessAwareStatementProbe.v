Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.ReadinessAwareSemanticSource.
Import ReadinessAwareSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion". Abort.
Check @service_inversion.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.readiness_aware.cumulative_service_inversion". Abort.
Check @cumulative_service_inversion.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.readiness_aware.cumulative_service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion_is_bounded". Abort.
Check @service_inversion_is_bounded.
Goal True. idtac "END|prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion_is_bounded". Abort.
