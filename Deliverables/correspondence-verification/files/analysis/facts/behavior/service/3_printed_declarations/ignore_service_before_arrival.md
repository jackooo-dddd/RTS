# `ignore_service_before_arrival`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.ignore_service_before_arrival`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.ignore_service_before_arrival`
- Certificate: `ignore_service_before_arrival_correspondence`

## Official Rocq

```coq
ignore_service_before_arrival :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) {H : JobArrival Job},
@jobs_must_arrive_to_execute Job H PState sched ->
forall t1 t2 : nat,
is_true (t1 <= @job_arrival Job H j) ->
is_true (@job_arrival Job H j <= t2) ->
@service_during Job PState sched j t1 t2 = @service_during Job PState sched j (@job_arrival Job H j) t2

ignore_service_before_arrival is not universe polymorphic
Arguments ignore_service_before_arrival {Job PState} sched j {H} H_jobs_must_arrive (t1 t2)%nat_scope _ _
ignore_service_before_arrival is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.ignore_service_before_arrival
Declared in library prosa.analysis.facts.behavior.service, line 549, characters 10-39
@ignore_service_before_arrival
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (H : JobArrival Job),
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall t1 t2 : nat,
       is_true (t1 <= @job_arrival Job H j) ->
       is_true (@job_arrival Job H j <= t2) ->
       @service_during Job PState sched j t1 t2 =
       @service_during Job PState sched j (@job_arrival Job H j) t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.ignore_service_before_arrival : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) [inst_1 : Prosa.Behavior.Job.JobArrival Job],
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    ∀ (t1 t2 : ℕ),
      t1 ≤ Prosa.Behavior.Job.job_arrival j →
        Prosa.Behavior.Job.job_arrival j ≤ t2 →
          Prosa.Behavior.Service.service_during sched j t1 t2 =
            Prosa.Behavior.Service.service_during sched j (Prosa.Behavior.Job.job_arrival j) t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_ignore_service_before_arrival
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
       forall t1 t2 : Nat,
       LE_le_inst1 Nat instLENat t1
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_11 j) ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_11 j)
         t2 ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t1 t2)
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j
            (Prosa_Behavior_Job_JobArrival_job_arrival Job
               inst_3
               inst_11 j)
            t2)
```
