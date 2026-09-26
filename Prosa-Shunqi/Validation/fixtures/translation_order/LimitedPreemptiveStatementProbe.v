Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.LimitedPreemptiveSemanticSource.
Import LimitedPreemptiveSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
Require Import prosa.PreemptionParameterSemanticSource.
Import PreemptionParameterSemanticSource.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.util.list.
Import ListSemanticSource.
Require Import prosa.GeneratedNondecreasingSource.
Import GeneratedNondecreasingSource.
Goal True. idtac "BEGIN|prosa.model.preemption.limited_preemptive.JobPreemptionPoints". Abort.
Check @JobPreemptionPoints.
Goal True. idtac "END|prosa.model.preemption.limited_preemptive.JobPreemptionPoints". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.limited_preemptive.beginning_of_execution_in_preemption_points". Abort.
Check @beginning_of_execution_in_preemption_points.
Goal True. idtac "END|prosa.model.preemption.limited_preemptive.beginning_of_execution_in_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.limited_preemptive.end_of_execution_in_preemption_points". Abort.
Check @end_of_execution_in_preemption_points.
Goal True. idtac "END|prosa.model.preemption.limited_preemptive.end_of_execution_in_preemption_points". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.limited_preemptive.preemption_points_is_nondecreasing_sequence". Abort.
Check @preemption_points_is_nondecreasing_sequence.
Goal True. idtac "END|prosa.model.preemption.limited_preemptive.preemption_points_is_nondecreasing_sequence". Abort.
Goal True. idtac "BEGIN|prosa.model.preemption.limited_preemptive.valid_limited_preemptions_job_model". Abort.
Check @valid_limited_preemptions_job_model.
Goal True. idtac "END|prosa.model.preemption.limited_preemptive.valid_limited_preemptions_job_model". Abort.
