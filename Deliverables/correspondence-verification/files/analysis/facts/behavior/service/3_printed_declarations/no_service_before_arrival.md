# `no_service_before_arrival`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.service.no_service_before_arrival`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.no_service_before_arrival`
- Certificate: `no_service_before_arrival_correspondence`

## Official Rocq

```coq
no_service_before_arrival :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) {H : JobArrival Job},
@jobs_must_arrive_to_execute Job H PState sched ->
forall t : nat, is_true (t <= @job_arrival Job H j) -> @service Job PState sched j t = 0

no_service_before_arrival is not universe polymorphic
Arguments no_service_before_arrival {Job PState} sched j {H} H_jobs_must_arrive t%nat_scope _
no_service_before_arrival is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.no_service_before_arrival
Declared in library prosa.analysis.facts.behavior.service, line 561, characters 14-39
@no_service_before_arrival
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (H : JobArrival Job),
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall t : nat, is_true (t <= @job_arrival Job H j) -> @service Job PState sched j t = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.no_service_before_arrival : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) [inst_1 : Prosa.Behavior.Job.JobArrival Job],
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    ∀ t ≤ Prosa.Behavior.Job.job_arrival j, Prosa.Behavior.Service.service sched j t = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_no_service_before_arrival
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
       LE_le_inst1 Nat instLENat t
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_11 j) ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
```
