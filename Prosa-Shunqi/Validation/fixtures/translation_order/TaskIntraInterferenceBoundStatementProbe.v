Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.TaskIntraInterferenceBoundSemanticSource.
Import TaskIntraInterferenceBoundSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: the imports of the source *)
Require Import prosa.analysis.abstract.definitions prosa.model.aggregate.workload prosa.model.job.properties.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.task_intra_IBF". Abort.
Check @task_intra_IBF.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.task_intra_IBF". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.instantiated_task_intra_interference_is_bounded". Abort.
Print statement_instantiated_task_intra_interference_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.task_intra_interference_bound.instantiated_task_intra_interference_is_bounded". Abort.
