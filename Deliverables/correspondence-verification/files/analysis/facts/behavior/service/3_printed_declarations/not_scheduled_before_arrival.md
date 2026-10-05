# `not_scheduled_before_arrival`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.not_scheduled_before_arrival`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.not_scheduled_before_arrival`
- Certificate: `not_scheduled_before_arrival_correspondence`

## Official Rocq

```coq
not_scheduled_before_arrival :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) {H : JobArrival Job},
@jobs_must_arrive_to_execute Job H PState sched ->
forall t : nat, is_true (t < @job_arrival Job H j) -> is_true (~~ @scheduled_at Job PState sched j t)

not_scheduled_before_arrival is not universe polymorphic
Arguments not_scheduled_before_arrival {Job PState} sched j {H} H_jobs_must_arrive t%nat_scope _
not_scheduled_before_arrival is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.not_scheduled_before_arrival
Declared in library prosa.analysis.facts.behavior.service, line 509, characters 10-38
@not_scheduled_before_arrival
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (H : JobArrival Job),
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall t : nat, is_true (t < @job_arrival Job H j) -> is_true (~~ @scheduled_at Job PState sched j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.not_scheduled_before_arrival : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) [inst_1 : Prosa.Behavior.Job.JobArrival Job],
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    ∀ t < Prosa.Behavior.Job.job_arrival j, (!Prosa.Behavior.Service.scheduled_at sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_not_scheduled_before_arrival
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job)
         (inst_11 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_11 PState sched ->
       forall t : Nat,
       LT_lt_inst1 Nat instLTNat t
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_11 j) ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_scheduled_at Job
               inst_3 PState sched j t))
         Bool_true
```
