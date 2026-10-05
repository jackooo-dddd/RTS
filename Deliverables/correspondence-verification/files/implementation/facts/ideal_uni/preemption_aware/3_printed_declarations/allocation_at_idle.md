# `allocation_at_idle`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.ideal_uni.preemption_aware.allocation_at_idle`
- Lean: `Prosa.Implementation.Facts.IdealUni.PreemptionAware.allocation_at_idle`
- Certificate: `allocation_at_idle_correspondence`

## Official Rocq

```coq
allocation_at_idle :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} (arr_seq : arrival_sequence Job)
  {RM : @JobReady Job (processor_state Job) H H0} {H1 : JobPreemptable Job}
  (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)),
(forall (t : instant) (s : seq (Equality.sort Job)), choose_job t s = @None (Equality.sort Job) <-> s = [::]) ->
forall (sched : @schedule Job (processor_state Job)) (t : instant),
@allocation_at Job H H0 arr_seq RM H1 choose_job sched t = @None (Equality.sort Job) ->
@jobs_backlogged_at Job H0 H (processor_state Job) RM arr_seq sched t = [::]

allocation_at_idle is not universe polymorphic
Arguments allocation_at_idle {Job H H0} arr_seq {RM H1} (choose_job H_non_idling)%function_scope sched t _
allocation_at_idle is opaque
Expands to: Constant prosa.implementation.facts.ideal_uni.preemption_aware.allocation_at_idle
Declared in library prosa.implementation.facts.ideal_uni.preemption_aware, line 56, characters 10-28
@allocation_at_idle
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job)
         (RM : @JobReady Job (processor_state Job) H H0) (H1 : JobPreemptable Job)
         (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)),
       (forall (t : instant) (s : seq (Equality.sort Job)),
        choose_job t s = @None (Equality.sort Job) <-> s = [::]) ->
       forall (sched : @schedule Job (processor_state Job)) (t : instant),
       @allocation_at Job H H0 arr_seq RM H1 choose_job sched t = @None (Equality.sort Job) ->
       @jobs_backlogged_at Job H0 H (processor_state Job) RM arr_seq sched t = [::]
```

## Lean

```lean
@Prosa.Implementation.Facts.IdealUni.PreemptionAware.allocation_at_idle : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  [RM : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)]
  [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (choose_job : Prosa.Behavior.Time.instant → List Job → Option Job),
  (∀ (t : Prosa.Behavior.Time.instant) (s : List Job), choose_job t s = none ↔ s = []) →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
      (t : Prosa.Behavior.Time.instant),
      Prosa.Implementation.Definitions.IdealUniScheduler.allocation_at arr_seq choose_job sched t = none →
        Prosa.Model.Schedule.WorkConserving.jobs_backlogged_at arr_seq sched t = []
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_IdealUni_PreemptionAware_allocation_at_idle
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (RM : Prosa_Behavior_Ready_JobReady_inst4 Job
                 inst_3
                 (Prosa_Model_Processor_Ideal_processor_state Job
                    inst_3)
                 inst_6
                 inst_9)
         (inst_20 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (choose_job : Prosa_Behavior_Time_instant -> List Job -> Option Job),
       (forall (t : Prosa_Behavior_Time_instant) (s : List Job),
        Iff (@eq (Option Job) (choose_job t s) (Option_none Job)) (@eq (List Job) s (List_nil Job))) ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (t : Prosa_Behavior_Time_instant),
       @eq (Option Job)
         (Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at Job
            inst_3
            inst_6
            inst_9 arr_seq
            RM inst_20
            choose_job sched t)
         (Option_none Job) ->
       @eq (List Job)
         (Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at_inst4 Job
            inst_3
            inst_9
            inst_6
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            RM arr_seq sched t)
         (List_nil Job)
```
