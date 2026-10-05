# `service_invariant_implies_deadline_met`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.deadlines.service_invariant_implies_deadline_met`
- Lean: `Prosa.Analysis.Facts.Behavior.Deadlines.service_invariant_implies_deadline_met`
- Certificate: `service_invariant_implies_deadline_met_correspondence`

## Official Rocq

```coq
service_invariant_implies_deadline_met :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {PState : ProcessorState Job}
  (sched sched' : @schedule Job PState) (j : Equality.sort Job),
@service Job PState sched j (@job_deadline Job H0 j) = @service Job PState sched' j (@job_deadline Job H0 j) ->
is_true (@job_meets_deadline Job PState sched H H0 j) <->
is_true (@job_meets_deadline Job PState sched' H H0 j)

service_invariant_implies_deadline_met is not universe polymorphic
Arguments service_invariant_implies_deadline_met {Job H H0 PState} sched sched' j _
service_invariant_implies_deadline_met is opaque
Expands to: Constant prosa.analysis.facts.behavior.deadlines.service_invariant_implies_deadline_met
Declared in library prosa.analysis.facts.behavior.deadlines, line 93, characters 10-48
@service_invariant_implies_deadline_met
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (PState : ProcessorState Job)
         (sched sched' : @schedule Job PState) (j : Equality.sort Job),
       @service Job PState sched j (@job_deadline Job H0 j) =
       @service Job PState sched' j (@job_deadline Job H0 j) ->
       is_true (@job_meets_deadline Job PState sched H H0 j) <->
       is_true (@job_meets_deadline Job PState sched' H H0 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Deadlines.service_invariant_implies_deadline_met : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched sched' : Prosa.Behavior.Schedule.schedule PState)
  (j : Job),
  Prosa.Behavior.Service.service sched j (Prosa.Behavior.Job.job_deadline j) =
      Prosa.Behavior.Service.service sched' j (Prosa.Behavior.Job.job_deadline j) →
    (Prosa.Behavior.Service.job_meets_deadline sched j = true ↔
      Prosa.Behavior.Service.job_meets_deadline sched' j = true)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Deadlines_service_invariant_implies_deadline_met
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched
          sched' : Prosa_Behavior_Schedule_schedule Job
                     inst_3 PState)
         (j : Job),
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j
            (Prosa_Behavior_Job_JobDeadline_job_deadline Job
               inst_3
               inst_9 j))
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched' j
            (Prosa_Behavior_Job_JobDeadline_job_deadline Job
               inst_3
               inst_9 j)) ->
       Iff
         (@eq Bool
            (Prosa_Behavior_Service_job_meets_deadline Job
               inst_3 PState sched
               inst_6
               inst_9 j)
            Bool_true)
         (@eq Bool
            (Prosa_Behavior_Service_job_meets_deadline Job
               inst_3 PState sched'
               inst_6
               inst_9 j)
            Bool_true)
```
