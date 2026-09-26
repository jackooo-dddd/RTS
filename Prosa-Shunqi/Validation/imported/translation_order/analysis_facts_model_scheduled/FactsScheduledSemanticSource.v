Require Export prosa.model.schedule.scheduled.
Require Export prosa.analysis.definitions.service.
Require Export prosa.model.processor.platform_properties.
Require Export prosa.util.tactics.

Module FactsScheduledSemanticSource.

Section SourceContext_0.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

Definition statement_scheduled_jobs_at_iff : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> forall (j : Job) (t : instant), (j \in scheduled_jobs_at arr_seq sched t) = scheduled_at sched j t).

End SourceContext_0.

Section SourceContext_1.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

Definition statement_scheduled_jobs_at_nil : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> forall t : instant, nilp (scheduled_jobs_at arr_seq sched t) <-> (forall j : Job, ~~ scheduled_at sched j t)).

End SourceContext_1.

Section SourceContext_2.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

Definition statement_not_scheduled_when_idle : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> forall (j : Job) (t : instant), is_idle arr_seq sched t -> ~~ scheduled_at sched j t).

End SourceContext_2.

Section SourceContext_3.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
    Hypothesis H_ideal_progress_model : ideal_progress_proc_model PState.

Definition statement_scheduled_at_implies_in_served_at : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> ideal_progress_proc_model PState -> forall (j : Job) (t : instant), scheduled_at sched j t -> j \in served_jobs_at arr_seq sched t).

End SourceContext_3.

Section SourceContext_4.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
    Hypothesis H_uni : uniprocessor_model PState.

Definition statement_scheduled_jobs_at_seq1 : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> uniprocessor_model PState -> forall t : instant, size (scheduled_jobs_at arr_seq sched t) <= 1).

End SourceContext_4.

Section SourceContext_5.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
    Hypothesis H_uni : uniprocessor_model PState.

Definition statement_scheduled_jobs_at_uni_cases : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> uniprocessor_model PState -> forall t : instant, scheduled_jobs_at arr_seq sched t == [::] \/ (exists j : Job, scheduled_jobs_at arr_seq sched t == [:: j])).

End SourceContext_5.

Section SourceContext_6.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
    Hypothesis H_uni : uniprocessor_model PState.

Definition statement_scheduled_jobs_at_uni : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> uniprocessor_model PState -> forall (j : Job) (t : instant), (scheduled_jobs_at arr_seq sched t == [:: j]) = (scheduled_job_at arr_seq sched t == Some j)).

End SourceContext_6.

Section SourceContext_7.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
    Hypothesis H_uni : uniprocessor_model PState.

Definition statement_scheduled_job_at_scheduled_at : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> uniprocessor_model PState -> forall (j : Job) (t : instant), (scheduled_job_at arr_seq sched t == Some j) = scheduled_at sched j t).

End SourceContext_7.

Section SourceContext_8.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
    Hypothesis H_uni : uniprocessor_model PState.

Definition statement_scheduled_jobs_at_scheduled_at : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> uniprocessor_model PState -> forall (j : Job) (t : instant), (scheduled_jobs_at arr_seq sched t == [:: j]) = scheduled_at sched j t).

End SourceContext_8.

Section SourceContext_9.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
    Hypothesis H_uni : uniprocessor_model PState.

Definition statement_scheduled_job_at_none : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> forall t : instant, scheduled_job_at arr_seq sched t = None <-> (forall j : Job, ~~ scheduled_at sched j t)).

End SourceContext_9.

Section SourceContext_10.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
    Hypothesis H_uni : uniprocessor_model PState.

Definition statement_is_idle_iff : Prop :=
  (forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job) (sched : schedule PState) (t : instant), is_idle arr_seq sched t = (scheduled_job_at arr_seq sched t == None)).

End SourceContext_10.

Section SourceContext_11.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.
    Hypothesis H_uni : uniprocessor_model PState.

Definition statement_is_nonidle_iff : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> uniprocessor_model PState -> forall t : instant, ~~ is_idle arr_seq sched t <-> (exists j : Job, scheduled_at sched j t)).

End SourceContext_11.

Section SourceContext_12.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

Definition statement_scheduled_at_dec : Type :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> forall t : instant, {exists j : Job, scheduled_at sched j t} + {forall j : Job, ~~ scheduled_at sched j t}).

End SourceContext_12.

Section SourceContext_13.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context {PState : ProcessorState Job}.
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrivals : valid_arrival_sequence arr_seq.
  Variable sched : schedule PState.
  Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute sched.

Definition statement_scheduled_at_cases : Prop :=
  (forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq -> forall sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq -> jobs_must_arrive_to_execute sched -> forall t : instant, is_idle arr_seq sched t \/ (exists j : Job, scheduled_at sched j t)).

End SourceContext_13.

End FactsScheduledSemanticSource.
