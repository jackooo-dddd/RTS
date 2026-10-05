# `service_within_busy_interval_ge_job_cost`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.busy_interval.service_within_busy_interval_ge_job_cost`
- Lean: `Prosa.Analysis.Abstract.BusyInterval.service_within_busy_interval_ge_job_cost`
- Certificate: `service_within_busy_interval_ge_job_cost_correspondence`

## Official Rocq

```coq
service_within_busy_interval_ge_job_cost :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job}
  {H3 : Interference Job} {H4 : InterferingWorkload Job} (sched : @schedule Job PState),
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall j : Equality.sort Job,
is_true (@job_cost_positive Job H2 j) ->
forall t1 t2 : instant,
@busy_interval Job H1 H2 PState sched H3 H4 j t1 t2 ->
is_true (@job_cost Job H2 j <= @service_during Job PState sched j t1 t2)

service_within_busy_interval_ge_job_cost is not universe polymorphic
Arguments service_within_busy_interval_ge_job_cost {Job H1 H2 PState H3 H4} sched
  H_jobs_must_arrive_to_execute j H_job_cost_positive t1 t2 H_busy_interval
service_within_busy_interval_ge_job_cost is opaque
Expands to: Constant prosa.analysis.abstract.busy_interval.service_within_busy_interval_ge_job_cost
Declared in library prosa.analysis.abstract.busy_interval, line 143, characters 8-48
@service_within_busy_interval_ge_job_cost
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job)
         (H3 : Interference Job) (H4 : InterferingWorkload Job) (sched : @schedule Job PState),
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall j : Equality.sort Job,
       is_true (@job_cost_positive Job H2 j) ->
       forall t1 t2 : instant,
       @busy_interval Job H1 H2 PState sched H3 H4 j t1 t2 ->
       is_true (@job_cost Job H2 j <= @service_during Job PState sched j t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Abstract.BusyInterval.service_within_busy_interval_ge_job_cost : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [inst_3 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_4 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    ∀ (j : Job),
      Prosa.Model.Job.Properties.job_cost_positive j = true →
        ∀ (t1 t2 : Prosa.Behavior.Time.instant),
          Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
            Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Service.service_during sched j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_BusyInterval_service_within_busy_interval_ge_job_cost
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (inst_14 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (inst_17 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       forall j : Job,
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_9 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_3
         inst_14
         inst_17
         inst_6
         inst_9 PState sched j t1 t2 ->
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_9 j)
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t1 t2)
```
