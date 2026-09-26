Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.TaskLimitedPreemptiveSemanticSource.
Import TaskLimitedPreemptiveSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
Require Import prosa.TaskPreemptionParametersSemanticSource.
Import TaskPreemptionParametersSemanticSource.
Require Import prosa.LimitedPreemptiveSemanticSource.
Import LimitedPreemptiveSemanticSource.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.task_beginning_of_execution_in_preemption_points". Abort.
Check @task_beginning_of_execution_in_preemption_points.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.task_beginning_of_execution_in_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.task_end_of_execution_in_preemption_points". Abort.
Check @task_end_of_execution_in_preemption_points.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.task_end_of_execution_in_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.nondecreasing_task_preemption_points". Abort.
Check @nondecreasing_task_preemption_points.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.nondecreasing_task_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.consistent_job_segment_count". Abort.
Check @consistent_job_segment_count.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.consistent_job_segment_count". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.job_respects_segment_lengths". Abort.
Check @job_respects_segment_lengths.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.job_respects_segment_lengths". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.task_segments_are_nonempty". Abort.
Check @task_segments_are_nonempty.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.task_segments_are_nonempty". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.valid_fixed_preemption_points_task_model". Abort.
Check @valid_fixed_preemption_points_task_model.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.valid_fixed_preemption_points_task_model". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.limited_preemptive.valid_fixed_preemption_points_model". Abort.
Check @valid_fixed_preemption_points_model.
Goal True. idtac "END|prosa.model.task.preemption.limited_preemptive.valid_fixed_preemption_points_model". Abort.
