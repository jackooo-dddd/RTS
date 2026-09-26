Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.TardinessSemanticSource.
Import TardinessSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all.
Require Import prosa.model.task.concept.
Goal True. idtac "BEGIN|prosa.analysis.definitions.tardiness.task_tardiness_is_bounded". Abort.
Check @task_tardiness_is_bounded.
Goal True. idtac "END|prosa.analysis.definitions.tardiness.task_tardiness_is_bounded". Abort.
