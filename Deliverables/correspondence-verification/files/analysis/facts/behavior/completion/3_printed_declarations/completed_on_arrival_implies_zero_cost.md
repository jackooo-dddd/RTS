# `completed_on_arrival_implies_zero_cost`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.completed_on_arrival_implies_zero_cost`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.completed_on_arrival_implies_zero_cost`
- Certificate: `completed_on_arrival_implies_zero_cost_correspondence`

## Official Rocq

```coq
completed_on_arrival_implies_zero_cost :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState) (j : Equality.sort Job),
@jobs_must_arrive_to_execute Job H0 PState sched ->
is_true (@completed_by Job PState sched H j (@job_arrival Job H0 j)) -> @job_cost Job H j = 0

completed_on_arrival_implies_zero_cost is not universe polymorphic
Arguments completed_on_arrival_implies_zero_cost {Job H H0 PState} sched j H_jobs_must_arrive_to_execute _
completed_on_arrival_implies_zero_cost is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.completed_on_arrival_implies_zero_cost
Declared in library prosa.analysis.facts.behavior.completion, line 94, characters 8-46
@completed_on_arrival_implies_zero_cost
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState) (j : Equality.sort Job),
       @jobs_must_arrive_to_execute Job H0 PState sched ->
       is_true (@completed_by Job PState sched H j (@job_arrival Job H0 j)) -> @job_cost Job H j = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.completed_on_arrival_implies_zero_cost : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    Prosa.Behavior.Service.completed_by sched j (Prosa.Behavior.Job.job_arrival j) = true →
      Prosa.Behavior.Job.job_cost j = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_completed_on_arrival_implies_zero_cost
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_9 PState sched ->
       @eq Bool
         (Prosa_Behavior_Service_completed_by Job
            inst_3 PState sched
            inst_6 j
            (Prosa_Behavior_Job_JobArrival_job_arrival Job
               inst_3
               inst_9 j))
         Bool_true ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_3
            inst_6 j)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
```
