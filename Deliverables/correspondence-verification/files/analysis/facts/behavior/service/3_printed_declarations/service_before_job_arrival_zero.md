# `service_before_job_arrival_zero`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.service_before_job_arrival_zero`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_before_job_arrival_zero`
- Certificate: `service_before_job_arrival_zero_correspondence`

## Official Rocq

```coq
service_before_job_arrival_zero :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) {H : JobArrival Job},
@jobs_must_arrive_to_execute Job H PState sched ->
forall t : nat, is_true (t < @job_arrival Job H j) -> @service_at Job PState sched j t = 0

service_before_job_arrival_zero is not universe polymorphic
Arguments service_before_job_arrival_zero {Job PState} sched j {H} H_jobs_must_arrive t%nat_scope _
service_before_job_arrival_zero is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_before_job_arrival_zero
Declared in library prosa.analysis.facts.behavior.service, line 528, characters 10-41
@service_before_job_arrival_zero
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (H : JobArrival Job),
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall t : nat, is_true (t < @job_arrival Job H j) -> @service_at Job PState sched j t = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_before_job_arrival_zero : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) [inst_1 : Prosa.Behavior.Job.JobArrival Job],
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    ∀ t < Prosa.Behavior.Job.job_arrival j, Prosa.Behavior.Service.service_at sched j t = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_before_job_arrival_zero
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
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j t)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
```
