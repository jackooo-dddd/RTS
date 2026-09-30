Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.TaskIbfReadinessSemanticSource.
Import TaskIbfReadinessSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.task_ibf_readiness.instantiated_task_intra_interference_is_bounded". Abort.
Print statement_instantiated_task_intra_interference_is_bounded.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.task_ibf_readiness.instantiated_task_intra_interference_is_bounded". Abort.
(* display-only: the official environment prints this file's task_intra_IBF with its own module qualifier
   `task_ibf_readiness.` (another task_intra_IBF is in scope there); reproduce exactly that display *)
Module task_ibf_readiness := TaskIbfReadinessSemanticSource.TaskIbfReadinessSemanticSource.
Module tibfr_display_shadow. Definition task_intra_IBF := tt. End tibfr_display_shadow.
Import tibfr_display_shadow.
Goal True. idtac "BEGIN|prosa.analysis.abstract.restricted_supply.task_ibf_readiness.task_intra_IBF". Abort.
Check @task_ibf_readiness.task_intra_IBF.
Goal True. idtac "END|prosa.analysis.abstract.restricted_supply.task_ibf_readiness.task_intra_IBF". Abort.
