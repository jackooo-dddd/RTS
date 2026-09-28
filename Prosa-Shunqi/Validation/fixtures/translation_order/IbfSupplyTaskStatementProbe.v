Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.IbfSupplyTaskSemanticSource.
Import IbfSupplyTaskSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.model.processor.supply prosa.analysis.abstract.definitions.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.supply_task.nonself_intra". Abort.
Check @nonself_intra.
Goal True. idtac "END|prosa.analysis.abstract.IBF.supply_task.nonself_intra". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.supply_task.task_intra_interference". Abort.
Check @task_intra_interference.
Goal True. idtac "END|prosa.analysis.abstract.IBF.supply_task.task_intra_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.IBF.supply_task.task_intra_interference_is_bounded_by". Abort.
Check @task_intra_interference_is_bounded_by.
Goal True. idtac "END|prosa.analysis.abstract.IBF.supply_task.task_intra_interference_is_bounded_by". Abort.
