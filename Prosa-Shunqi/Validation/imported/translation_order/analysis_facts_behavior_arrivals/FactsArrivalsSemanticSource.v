Require Export prosa.behavior.all.
Require Export prosa.util.all.
Require Export prosa.model.task.arrivals.
From mathcomp Require Import path.
Require Import prosa.util.notation.

Module FactsArrivalsSemanticSource.

Section SourceContext_0.
  Context {Job : JobType} `{JobArrival Job}.

Definition statement_arrived_between_before : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (j : Job) (t1 t2 : instant), arrived_between j t1 t2 -> arrived_before j t2).

End SourceContext_0.

Section SourceContext_1.
  Context {Job : JobType} `{JobArrival Job}.

Definition statement_arrived_before_has_arrived : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (j : Job) (t : instant), arrived_before j t -> has_arrived j t).

End SourceContext_1.

Section SourceContext_2.
  Context {Job : JobType} `{JobArrival Job}.

Definition statement_consistent_times_valid_arrival : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> consistent_arrival_times arr_seq).

End SourceContext_2.

Section SourceContext_3.
  Context {Job : JobType} `{JobArrival Job}.

Definition statement_uniq_valid_arrival : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> arrival_sequence_uniq arr_seq).

End SourceContext_3.

Section SourceContext_4.
  Context {Job : JobType} {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context {jr : JobReady Job PState}.

Definition statement_any_ready_job_is_pending : Prop :=
  (forall (Job : JobType) (PState : ProcessorState Job) (sched : schedule PState) (H : JobCost Job) (H0 : JobArrival Job) (jr : JobReady Job PState) (j : Job) (t : instant), job_ready sched j t -> pending sched j t).

End SourceContext_4.

Section SourceContext_5.
  Context {Job : JobType} {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context {jr : JobReady Job PState}.

Definition statement_ready_implies_arrived : Prop :=
  (forall (Job : JobType) (PState : ProcessorState Job) (sched : schedule PState) (H : JobCost Job) (H0 : JobArrival Job) (jr : JobReady Job PState) (j : Job) (t : instant), job_ready sched j t -> has_arrived j t).

End SourceContext_5.

Section SourceContext_6.
  Context {Job : JobType} {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context {jr : JobReady Job PState}.

Definition statement_jobs_must_arrive_to_be_ready : Prop :=
  (forall (Job : JobType) (PState : ProcessorState Job) (sched : schedule PState) (H : JobCost Job) (H0 : JobArrival Job) (jr : JobReady Job PState), jobs_must_be_ready_to_execute sched -> jobs_must_arrive_to_execute sched).

End SourceContext_6.

Section SourceContext_7.
  Context {Job : JobType} {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context {jr : JobReady Job PState}.

Definition statement_valid_schedule_implies_jobs_must_arrive_to_execute : Prop :=
  (forall (Job : JobType) (PState : ProcessorState Job) (sched : schedule PState) (H : JobCost Job) (H0 : JobArrival Job) (jr : JobReady Job PState) (arr_seq : arrival_sequence Job), valid_schedule sched arr_seq -> jobs_must_arrive_to_execute sched).

End SourceContext_7.

Section SourceContext_8.
  Context {Job : JobType} {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context {jr : JobReady Job PState}.

Definition statement_backlogged_implies_arrived : Prop :=
  (forall (Job : JobType) (PState : ProcessorState Job) (sched : schedule PState) (H : JobCost Job) (H0 : JobArrival Job) (jr : JobReady Job PState) (j : Job) (t : instant), backlogged sched j t -> has_arrived j t).

End SourceContext_8.

Section SourceContext_9.
  Context {Job : JobType} {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context {jr : JobReady Job PState}.

Definition statement_backlogged_implies_incomplete : Prop :=
  (forall (Job : JobType) (PState : ProcessorState Job) (sched : schedule PState) (H : JobCost Job) (H0 : JobArrival Job) (jr : JobReady Job PState) (j : Job) (t : instant), backlogged sched j t -> ~~ completed_by sched j t).

End SourceContext_9.

Section SourceContext_10.
  Context {Job : JobType} {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context {jr : JobReady Job PState}.

Definition statement_job_scheduled_implies_ready : Prop :=
  (forall (Job : JobType) (PState : ProcessorState Job) (sched : schedule PState) (H : JobCost Job) (H0 : JobArrival Job) (jr : JobReady Job PState), jobs_must_be_ready_to_execute sched -> forall (j : Job) (t : instant), scheduled_at sched j t -> job_ready sched j t).

End SourceContext_10.

Section SourceContext_11.
  Context {Job : JobType} {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context {jr : JobReady Job PState}.

Definition statement_valid_schedule_jobs_come_from_arrival_sequence : Prop :=
  (forall (Job : JobType) (PState : ProcessorState Job) (sched : schedule PState) (H : JobCost Job) (H0 : JobArrival Job) (jr : JobReady Job PState) (arr_seq : arrival_sequence Job), valid_schedule sched arr_seq -> jobs_come_from_arrival_sequence sched arr_seq).

End SourceContext_11.

Section SourceContext_12.
  Context {Job : JobType} {PState : ProcessorState Job}.
  Variable sched : schedule PState.
  Context `{JobCost Job}.
  Context `{JobArrival Job}.
  Context {jr : JobReady Job PState}.

Definition statement_valid_schedule_jobs_must_be_ready_to_execute : Prop :=
  (forall (Job : JobType) (PState : ProcessorState Job) (sched : schedule PState) (H : JobCost Job) (H0 : JobArrival Job) (jr : JobReady Job PState) (arr_seq : arrival_sequence Job), valid_schedule sched arr_seq -> jobs_must_be_ready_to_execute sched).

End SourceContext_12.

Section SourceContext_13.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.

Definition statement_arrivals_between_cat : Prop :=
  (forall (Job : JobType) (arr_seq : arrival_sequence Job) (t1 t t2 : nat), t1 <= t -> t <= t2 -> arrivals_between arr_seq t1 t2 = arrivals_between arr_seq t1 t ++ arrivals_between arr_seq t t2).

End SourceContext_13.

Section SourceContext_14.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.

Definition statement_arrivals_P_cat : Prop :=
  (forall (Job : JobType) (arr_seq : arrival_sequence Job) (P : Job -> bool) (t t1 t2 : nat), t1 <= t < t2 -> arrivals_between_P arr_seq P t1 t2 = arrivals_between_P arr_seq P t1 t ++ arrivals_between_P arr_seq P t t2).

End SourceContext_14.

Section SourceContext_15.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.

Definition statement_arrivals_between_mem_cat : Prop :=
  (forall (Job : JobType) (arr_seq : arrival_sequence Job) (j : Job) (t1 t t2 : nat), t1 <= t -> t <= t2 -> (j \in arrivals_between arr_seq t1 t2) = (j \in arrivals_between arr_seq t1 t ++ arrivals_between arr_seq t t2)).

End SourceContext_15.

Section SourceContext_16.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.

Definition statement_arrivals_between_sub : Prop :=
  (forall (Job : JobType) (arr_seq : arrival_sequence Job) (j : Job) (t1 t1' t2 t2' : nat), t1' <= t1 -> t2 <= t2' -> j \in arrivals_between arr_seq t1 t2 -> j \in arrivals_between arr_seq t1' t2').

End SourceContext_16.

Section SourceContext_17.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_job_arrival_arrives_at : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j : Job) (t : instant), arrives_at arr_seq j t -> job_arrival j = t).

End SourceContext_17.

Section SourceContext_18.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_job_arrival_at : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j : Job) (t : instant), j \in arrivals_at arr_seq t -> job_arrival j = t).

End SourceContext_18.

Section SourceContext_19.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_job_in_arrivals_at : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j : Job) (t : instant), arrives_in arr_seq j -> job_arrival j = t -> j \in arrivals_at arr_seq t).

End SourceContext_19.

Section SourceContext_20.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_job_arrival_between : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j : Job) (t1 t2 : instant), j \in arrivals_between arr_seq t1 t2 -> t1 <= job_arrival j < t2).

End SourceContext_20.

Section SourceContext_21.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_job_arrival_between_ge : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j : Job) (t1 t2 : instant), j \in arrivals_between arr_seq t1 t2 -> t1 <= job_arrival j).

End SourceContext_21.

Section SourceContext_22.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_job_arrival_between_lt : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j : Job) (t1 t2 : instant), j \in arrivals_between arr_seq t1 t2 -> job_arrival j < t2).

End SourceContext_22.

Section SourceContext_23.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_arrivals_between_filter_nil : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (t1 : nat) (t2 : instant) (t : nat), t < t1 -> [seq j <- arrivals_between arr_seq t1 t2 | job_arrival j < t] = [::]).

End SourceContext_23.

Section SourceContext_24.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_arrivals_between_filter : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (t1 : instant) (t2 t : nat), t <= t2 -> arrivals_between arr_seq t1 t = [seq j <- arrivals_between arr_seq t1 t2 | job_arrival j < t]).

End SourceContext_24.

Section SourceContext_25.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_in_arrivals_implies_arrived : Prop :=
  (forall (Job : JobType) (arr_seq : arrival_sequence Job) (j : Job) (t1 t2 : instant), j \in arrivals_between arr_seq t1 t2 -> arrives_in arr_seq j).

End SourceContext_25.

Section SourceContext_26.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_in_arrseq_implies_arrives : Prop :=
  (forall (Job : JobType) (arr_seq : arrival_sequence Job) (t : instant) (j : Job), j \in arr_seq t -> arrives_in arr_seq j).

End SourceContext_26.

Section SourceContext_27.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_in_arrivals_implies_arrived_between : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j : Job) (t1 t2 : instant), j \in arrivals_between arr_seq t1 t2 -> arrived_between j t1 t2).

End SourceContext_27.

Section SourceContext_28.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_in_arrivals_implies_arrived_before : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j : Job) (t : instant), j \in arrivals_before arr_seq t -> arrived_before j t).

End SourceContext_28.

Section SourceContext_29.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_arrived_between_implies_in_arrivals : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j : Job) (t1 t2 : instant), arrives_in arr_seq j -> arrived_between j t1 t2 -> j \in arrivals_between arr_seq t1 t2).

End SourceContext_29.

Section SourceContext_30.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_job_arrival_between_P : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j : Job) (P : Job -> bool) (t1 t2 : instant), j \in arrivals_between_P arr_seq P t1 t2 -> t1 <= job_arrival j < t2).

End SourceContext_30.

Section SourceContext_31.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_job_in_arrivals_between : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j : Job) (t1 t2 : nat), arrives_in arr_seq j -> t1 <= job_arrival j -> job_arrival j < t2 -> j \in arrivals_between arr_seq t1 t2).

End SourceContext_31.

Section SourceContext_32.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_arrivals_uniq : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> arrival_sequence_uniq arr_seq -> forall t1 t2 : instant, uniq (arrivals_between arr_seq t1 t2)).

End SourceContext_32.

Section SourceContext_33.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_arrivals_between_geq : Prop :=
  (forall (Job : JobType) (arr_seq : arrival_sequence Job) (t1 t2 : nat), t2 <= t1 -> arrivals_between arr_seq t1 t2 = [::]).

End SourceContext_33.

Section SourceContext_34.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_arrivals_between_nonempty : Prop :=
  (forall (Job : JobType) (arr_seq : arrival_sequence Job) (t1 t2 : instant) (j : Job), j \in arrivals_between arr_seq t1 t2 -> t1 < t2).

End SourceContext_34.

Section SourceContext_35.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_arrival_lt_implies_job_in_arrivals_between_P : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j1 j2 : Job) (P : Job -> bool) (t1 t2 : instant), j1 \in arrivals_between_P arr_seq P t1 t2 -> j2 \in arrivals_between_P arr_seq P t1 t2 -> job_arrival j2 < job_arrival j1 -> j2 \in arrivals_between_P arr_seq P t1 (job_arrival j1)).

End SourceContext_35.

Section SourceContext_36.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_job_arrival_in_bounds : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall (j : Job) (t1 t2 : instant), j \in arrivals_between arr_seq t1 t2 <-> arrives_in arr_seq j /\ t1 <= job_arrival j < t2).

End SourceContext_36.

Section SourceContext_37.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

    Definition by_arrival_times (j1 j2 : Job) : bool := job_arrival j1 <= job_arrival j2.

End SourceContext_37.

Section SourceContext_38.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_arrivals_at_sorted : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall t : instant, sorted by_arrival_times (arrivals_at arr_seq t)).

End SourceContext_38.

Section SourceContext_39.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Hypothesis H_consistent_arrival_times : consistent_arrival_times arr_seq.

Definition statement_arrivals_between_sorted : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall t1 t2 : instant, sorted by_arrival_times (arrivals_between arr_seq t1 t2)).

End SourceContext_39.

Section SourceContext_40.
  Context {Job : JobType}.
  Context {Task : TaskType}.
  Context `{JobArrival Job}.
  Context `{JobTask Job Task}.
  Variable arr_seq : arrival_sequence Job.
    Variable ts : seq Task.
    Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.

Definition statement_arrivals_between_partitioned_by_task : Prop :=
  (forall (Job : JobType) (Task : TaskType) (H0 : JobTask Job Task) (arr_seq : arrival_sequence Job) (ts : seq Task), all_jobs_from_taskset arr_seq ts -> forall (t1 t2 : instant) (j : Job), (j \in arrivals_between arr_seq t1 t2) = (j \in \cat_(tsk<-ts)task_arrivals_between arr_seq tsk t1 t2)).

End SourceContext_40.

Section SourceContext_41.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Variable j : Job.
  Variable t : instant.
  Hypothesis H_scheduled_at : scheduled_at sched j t.

Definition statement_arrives_in_jobs_come_from_arrival_sequence : Prop :=
  (forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job) (sched : schedule PState), jobs_come_from_arrival_sequence sched arr_seq -> forall (j : Job) (t : instant), scheduled_at sched j t -> arrives_in arr_seq j).

End SourceContext_41.

Section SourceContext_42.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Variable j : Job.
  Variable t : instant.
  Hypothesis H_scheduled_at : scheduled_at sched j t.

Definition statement_arrived_between_jobs_must_arrive_to_execute : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (sched : schedule PState), jobs_must_arrive_to_execute sched -> forall (j : Job) (t : instant), scheduled_at sched j t -> has_arrived j t).

End SourceContext_42.

Section SourceContext_43.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Variable j : Job.
  Variable t : instant.
  Hypothesis H_scheduled_at : scheduled_at sched j t.

Definition statement_arrivals_before_scheduled_at : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> forall (j : Job) (t : instant), scheduled_at sched j t -> forall t' : nat, t < t' -> j \in arrivals_before arr_seq t').

End SourceContext_43.

Section SourceContext_44.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
  Variable j : Job.
  Variable t : instant.
  Hypothesis H_scheduled_at : scheduled_at sched j t.

Definition statement_arrivals_up_to_scheduled_at : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), consistent_arrival_times arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> forall (j : Job) (t : instant), scheduled_at sched j t -> forall t' : nat, t <= t' -> j \in arrivals_up_to arr_seq t').

End SourceContext_44.

End FactsArrivalsSemanticSource.
