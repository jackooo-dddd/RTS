Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.TaskOffsetSemanticSource.
Import TaskOffsetSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.task.concept prosa.model.task.arrivals.
Goal True. idtac "BEGIN|prosa.model.task.offset.TaskOffset". Abort.
Check @TaskOffset.
Goal True. idtac "END|prosa.model.task.offset.TaskOffset". Abort.
Goal True. idtac "BEGIN|prosa.model.task.offset.no_jobs_before_offset". Abort.
Check @no_jobs_before_offset.
Goal True. idtac "END|prosa.model.task.offset.no_jobs_before_offset". Abort.
Goal True. idtac "BEGIN|prosa.model.task.offset.job_released_at_offset". Abort.
Check @job_released_at_offset.
Goal True. idtac "END|prosa.model.task.offset.job_released_at_offset". Abort.
Goal True. idtac "BEGIN|prosa.model.task.offset.valid_offset". Abort.
Check @valid_offset.
Goal True. idtac "END|prosa.model.task.offset.valid_offset". Abort.
Goal True. idtac "BEGIN|prosa.model.task.offset.valid_offsets". Abort.
Check @valid_offsets.
Goal True. idtac "END|prosa.model.task.offset.valid_offsets". Abort.
Goal True. idtac "BEGIN|prosa.model.task.offset.task_offsets". Abort.
Check @task_offsets.
Goal True. idtac "END|prosa.model.task.offset.task_offsets". Abort.
Goal True. idtac "BEGIN|prosa.model.task.offset.max_task_offset". Abort.
Check @max_task_offset.
Goal True. idtac "END|prosa.model.task.offset.max_task_offset". Abort.
