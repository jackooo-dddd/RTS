# `suspended_implies_not_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.suspension.suspended_implies_not_scheduled`
- Lean: `Prosa.Analysis.Facts.Suspension.suspended_implies_not_scheduled`
- Certificate: `suspended_implies_not_scheduled_correspondence`

## Official Rocq

```coq
suspended_implies_not_scheduled :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobSuspension Job}
  (arr_seq : arrival_sequence Job) {PState : ProcessorState Job} (sched : @schedule Job PState),
@valid_schedule Job H PState sched H0 (@suspension_ready_instance Job PState H H0 H1) arr_seq ->
forall (j : Equality.sort Job) (t : instant),
is_true (@suspended Job PState H H0 H1 sched j t) -> is_true (~~ @scheduled_at Job PState sched j t)

suspended_implies_not_scheduled is not universe polymorphic
Arguments suspended_implies_not_scheduled {Job H H0 H1} arr_seq {PState} sched H_valid_schedule j t _
suspended_implies_not_scheduled is opaque
Expands to: Constant prosa.analysis.facts.suspension.suspended_implies_not_scheduled
Declared in library prosa.analysis.facts.suspension, line 46, characters 8-39
@suspended_implies_not_scheduled
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobSuspension Job)
         (arr_seq : arrival_sequence Job) (PState : ProcessorState Job) (sched : @schedule Job PState),
       @valid_schedule Job H PState sched H0 (@suspension_ready_instance Job PState H H0 H1) arr_seq ->
       forall (j : Equality.sort Job) (t : instant),
       is_true (@suspended Job PState H H0 H1 sched j t) -> is_true (~~ @scheduled_at Job PState sched j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Suspension.suspended_implies_not_scheduled : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Model.Readiness.Suspension.JobSuspension Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Ready.valid_schedule sched arr_seq →
    ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Model.Readiness.Suspension.suspended sched j t = true →
        (!Prosa.Behavior.Service.scheduled_at sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Suspension_suspended_implies_not_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job inst_3)
         (inst_12 : 
          Prosa_Model_Readiness_Suspension_JobSuspension Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6 PState sched
         inst_9
         (Prosa_Model_Readiness_Suspension_suspension_ready_instance Job
            inst_3 PState
            inst_6
            inst_9
            inst_12)
         arr_seq ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Readiness_Suspension_suspended Job
            inst_3 PState
            inst_6
            inst_9
            inst_12 sched j t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_scheduled_at Job
               inst_3 PState sched j t))
         Bool_true
```
