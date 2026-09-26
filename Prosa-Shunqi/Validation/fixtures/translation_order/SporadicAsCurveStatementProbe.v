Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.SporadicAsCurveSemanticSource.
Import SporadicAsCurveSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
Require Import prosa.FactsSporadicArrivalBoundSemanticSource.
Import FactsSporadicArrivalBoundSemanticSource.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic_as_curve.MaxArrivalsSporadic". Abort.
Check @MaxArrivalsSporadic.
Goal True. idtac "END|prosa.model.task.arrival.sporadic_as_curve.MaxArrivalsSporadic". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_valid". Abort.
Print statement_sporadic_arrival_curve_valid.
Goal True. idtac "END|prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_valid". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_arrival_curve_valid". Abort.
Print statement_sporadic_task_sets_arrival_curve_valid.
Goal True. idtac "END|prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_arrival_curve_valid". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_respects_max_arrivals". Abort.
Print statement_sporadic_arrival_curve_respects_max_arrivals.
Goal True. idtac "END|prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_respects_max_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_respects_max_arrivals". Abort.
Print statement_sporadic_task_sets_respects_max_arrivals.
Goal True. idtac "END|prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_respects_max_arrivals". Abort.
