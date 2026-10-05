# `all_deadlines_met_in_valid_schedule`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.definitions.schedulability.all_deadlines_met_in_valid_schedule`
- Lean: `Prosa.Analysis.Definitions.Schedulability.all_deadlines_met_in_valid_schedule`
- Certificate: `all_deadlines_met_in_valid_schedule_correspondence`

## Official Rocq

```coq
all_deadlines_met_in_valid_schedule :
forall {Job : JobType} {H0 : JobCost Job} {H1 : JobDeadline Job} {PState : ProcessorState Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@all_deadlines_of_arrivals_met Job H0 H1 PState arr_seq sched -> @all_deadlines_met Job H0 H1 PState sched

all_deadlines_met_in_valid_schedule is not universe polymorphic
Arguments all_deadlines_met_in_valid_schedule {Job H0 H1 PState} arr_seq sched _ _ j t _
all_deadlines_met_in_valid_schedule is opaque
Expands to: Constant prosa.analysis.definitions.schedulability.all_deadlines_met_in_valid_schedule
Declared in library prosa.analysis.definitions.schedulability, line 152, characters 8-43
@all_deadlines_met_in_valid_schedule
     : forall (Job : JobType) (H0 : JobCost Job) (H1 : JobDeadline Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @all_deadlines_of_arrivals_met Job H0 H1 PState arr_seq sched ->
       @all_deadlines_met Job H0 H1 PState sched
```

## Lean

```lean
@Prosa.Analysis.Definitions.Schedulability.all_deadlines_met_in_valid_schedule : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
    Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq sched →
      Prosa.Analysis.Definitions.Schedulability.all_deadlines_met sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Schedulability_all_deadlines_met_in_valid_schedule
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
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched arr_seq ->
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met Job
         inst_3
         inst_6
         inst_9 PState arr_seq sched ->
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_met Job
         inst_3
         inst_6
         inst_9 PState sched
```
