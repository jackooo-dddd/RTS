Require Export prosa.model.task.arrivals.
Require Export prosa.util.all.
From mathcomp Require Import path.
Require Import prosa.util.notation prosa.util.list prosa.FactsArrivalsSemanticSource.
Import ListSemanticSource FactsArrivalsSemanticSource.

Module FactsTaskArrivalsSemanticSource.

Section SourceContext_0.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.

Definition statement_num_arrivals_of_task_cat : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job) (tsk : Task) (t t1 t2 : nat), t1 <= t <= t2 -> number_of_task_arrivals arr_seq tsk t1 t2 = number_of_task_arrivals arr_seq tsk t1 t + number_of_task_arrivals arr_seq tsk t t2).

End SourceContext_0.

Section SourceContext_1.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.

Definition statement_task_arrivals_between_cat : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t t2 : nat), t1 <= t -> t <= t2 -> task_arrivals_between arr_seq tsk t1 t2 = task_arrivals_between arr_seq tsk t1 t ++ task_arrivals_between arr_seq tsk t t2).

End SourceContext_1.

Section SourceContext_2.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.

Definition statement_task_arrivals_up_to_prefix_cat : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job) (j1 j2 : Job), arrives_in arr_seq j1 -> arrives_in arr_seq j2 -> job_task j1 = job_task j2 -> job_arrival j1 <= job_arrival j2 -> prefix_of (task_arrivals_up_to_job_arrival arr_seq j1) (task_arrivals_up_to_job_arrival arr_seq j2)).

End SourceContext_2.

Section SourceContext_3.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_arrives_in_task_arrivals_up_to : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall j : Job, arrives_in arr_seq j -> j \in task_arrivals_up_to_job_arrival arr_seq j).

End SourceContext_3.

Section SourceContext_4.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_arrives_in_task_arrivals_at : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall j : Job, arrives_in arr_seq j -> j \in task_arrivals_at_job_arrival arr_seq j).

End SourceContext_4.

Section SourceContext_5.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_task_arrivals_cat : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job) (tsk : Task) (t_m t : nat), t_m <= t -> task_arrivals_up_to arr_seq tsk t = task_arrivals_up_to arr_seq tsk t_m ++ task_arrivals_between arr_seq tsk t_m.+1 t.+1).

End SourceContext_5.

Section SourceContext_6.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_task_arrivals_up_to_cat : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job) (j : Job), arrives_in arr_seq j -> task_arrivals_up_to_job_arrival arr_seq j = task_arrivals_before_job_arrival arr_seq j ++ task_arrivals_at_job_arrival arr_seq j).

End SourceContext_6.

Section SourceContext_7.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_job_in_task_arrivals_between : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (tsk : Task) (j : Job) (t1 t2 : nat), arrives_in arr_seq j -> job_task j = tsk -> t1 <= job_arrival j < t2 -> j \in task_arrivals_between arr_seq tsk t1 t2).

End SourceContext_7.

Section SourceContext_8.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_task_arrivals_between_subset : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : instant) (j : Job), j \in task_arrivals_between arr_seq tsk t1 t2 -> j \in arrivals_between arr_seq t1 t2).

End SourceContext_8.

Section SourceContext_9.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_arrives_in_task_arrivals_implies_arrived : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : instant) (j : Job), j \in task_arrivals_between arr_seq tsk t1 t2 -> arrives_in arr_seq j).

End SourceContext_9.

Section SourceContext_10.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_arrives_in_task_arrivals_before_implies_arrives_before : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (tsk : Task) (j : Job) (t : instant), j \in task_arrivals_before arr_seq tsk t -> job_arrival j < t).

End SourceContext_10.

Section SourceContext_11.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_arrives_in_task_arrivals_implies_job_task : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job) (tsk : Task) (j : Job) (t : instant), j \in task_arrivals_before arr_seq tsk t -> job_task j == tsk).

End SourceContext_11.

Section SourceContext_12.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_in_task_arrivals_between_implies_job_of_task : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : instant) (j : Job), j \in task_arrivals_between arr_seq tsk t1 t2 -> job_task j = tsk).

End SourceContext_12.

Section SourceContext_13.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_task_arrivals_nonempty : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : instant) (j : Job), j \in task_arrivals_between arr_seq tsk t1 t2 -> t1 < t2).

End SourceContext_13.

Section SourceContext_14.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_number_of_task_arrivals_nonzero : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : instant), 0 < number_of_task_arrivals arr_seq tsk t1 t2 -> t1 < t2).

End SourceContext_14.

Section SourceContext_15.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_uniq_task_arrivals : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (tsk : Task) (t : instant), arrival_sequence_uniq arr_seq -> uniq (task_arrivals_up_to arr_seq tsk t)).

End SourceContext_15.

Section SourceContext_16.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_task_arrivals_between_uniq : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (tsk : Task) (t1 t2 : instant), arrival_sequence_uniq arr_seq -> uniq (task_arrivals_between arr_seq tsk t1 t2)).

End SourceContext_16.

Section SourceContext_17.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_job_notin_task_arrivals_before : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j : Job) (t : nat), arrives_in arr_seq j -> t < job_arrival j -> j \notin task_arrivals_up_to arr_seq (job_task j) t).

End SourceContext_17.

Section SourceContext_18.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_arrival_lt_implies_strict_prefix : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (tsk : Task) (j1 j2 : Job), job_task j1 = tsk -> job_task j2 = tsk -> arrives_in arr_seq j1 -> arrives_in arr_seq j2 -> job_arrival j1 < job_arrival j2 -> strict_prefix_of (task_arrivals_up_to_job_arrival arr_seq j1) (task_arrivals_up_to_job_arrival arr_seq j2)).

End SourceContext_18.

Section SourceContext_19.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_nth_job_of_task_arrivals : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (tsk : Task) (n : nat) (j_def j : Job) (t : nat), arrives_in arr_seq j -> job_task j = tsk -> job_index arr_seq j = n -> job_arrival j <= t -> nth j_def (task_arrivals_up_to arr_seq tsk t) n = j).

End SourceContext_19.

Section SourceContext_20.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_task_arrivals_between_is_cat_of_task_arrivals_at : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : instant), task_arrivals_between arr_seq tsk t1 t2 = \cat_(t1<=t<t2)task_arrivals_at arr_seq tsk t).

End SourceContext_20.

Section SourceContext_21.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_size_of_task_arrivals_between : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : instant), size (task_arrivals_between arr_seq tsk t1 t2) = \sum_(t1 <= t < t2) size (task_arrivals_at arr_seq tsk t)).

End SourceContext_21.

Section SourceContext_22.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_consistent_arrivals : consistent_arrival_times arr_seq.
  Variable tsk : Task.

Definition statement_task_arrivals_between_sorted : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (tsk : Task) (t1 t2 : instant), sorted by_arrival_times (task_arrivals_between arr_seq tsk t1 t2)).

End SourceContext_22.

End FactsTaskArrivalsSemanticSource.
