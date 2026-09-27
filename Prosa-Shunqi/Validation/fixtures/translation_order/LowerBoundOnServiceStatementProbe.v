Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.LowerBoundOnServiceSemanticSource.
Import LowerBoundOnServiceSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.analysis.abstract.definitions.
(* display-only: the official elaborated-type evidence was printed with the classical
   busy-interval notions in scope, so the abstract ones are displayed qualified as
   [definitions.busy_interval_prefix] etc. *)
Module LowerBoundOnServiceProbeDisplay.
  Definition busy_interval_prefix := tt. Definition busy_interval := tt.
  Definition quiet_time := tt. Definition work_conserving := tt.
End LowerBoundOnServiceProbeDisplay.
Import LowerBoundOnServiceProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.lower_bound_on_service.interference_is_complement_to_schedule". Abort.
Print statement_interference_is_complement_to_schedule.
Goal True. idtac "END|prosa.analysis.abstract.lower_bound_on_service.interference_is_complement_to_schedule". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.lower_bound_on_service.service_and_interference_bounded". Abort.
Print statement_service_and_interference_bounded.
Goal True. idtac "END|prosa.analysis.abstract.lower_bound_on_service.service_and_interference_bounded". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.lower_bound_on_service.j_receives_enough_service". Abort.
Print statement_j_receives_enough_service.
Goal True. idtac "END|prosa.analysis.abstract.lower_bound_on_service.j_receives_enough_service". Abort.
