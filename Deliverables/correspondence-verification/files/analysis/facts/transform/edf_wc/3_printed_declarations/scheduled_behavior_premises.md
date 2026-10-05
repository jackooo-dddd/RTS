# `scheduled_behavior_premises`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.transform.edf_wc.scheduled_behavior_premises`
- Lean: `Prosa.Analysis.Facts.Transform.EdfWc.scheduled_behavior_premises`
- Certificate: `scheduled_behavior_premises_correspondence`

## Official Rocq

```coq
scheduled_behavior_premises :
forall {Job : JobType},
JobCost Job ->
JobDeadline Job -> JobArrival Job -> arrival_sequence Job -> @schedule Job (processor_state Job) -> Prop

scheduled_behavior_premises is not universe polymorphic
Arguments scheduled_behavior_premises {Job H H0 H1} arr_seq sched
scheduled_behavior_premises is transparent
Expands to: Constant prosa.analysis.facts.transform.edf_wc.scheduled_behavior_premises
Declared in library prosa.analysis.facts.transform.edf_wc, line 322, characters 13-40
@scheduled_behavior_premises
     : forall Job : JobType,
       JobCost Job ->
       JobDeadline Job ->
       JobArrival Job -> arrival_sequence Job -> @schedule Job (processor_state Job) -> Prop
```

Body:

```coq
scheduled_behavior_premises =
fun (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) =>
@jobs_must_arrive_to_execute Job H1 (processor_state Job) sched /\
@completed_jobs_dont_execute Job (processor_state Job) sched H /\
@jobs_come_from_arrival_sequence Job (processor_state Job) sched arr_seq /\
@all_deadlines_met Job H H0 (processor_state Job) sched
     : forall {Job : JobType},
       JobCost Job ->
       JobDeadline Job ->
       JobArrival Job -> arrival_sequence Job -> @schedule Job (processor_state Job) -> Prop

Arguments scheduled_behavior_premises {Job H H0 H1} arr_seq sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfWc.scheduled_behavior_premises : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) → Prop
```

Body:

```lean
def Prosa.Analysis.Facts.Transform.EdfWc.scheduled_behavior_premises.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobDeadline Job]
    [Prosa.Behavior.Job.JobArrival Job] arr_seq sched =>
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched ∧
    Prosa.Behavior.Ready.completed_jobs_dont_execute sched ∧
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq ∧
        Prosa.Analysis.Definitions.Schedulability.all_deadlines_met sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfWc_scheduled_behavior_premises
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       SProp
```

Body:

```coq
Prosa_Analysis_Facts_Transform_EdfWc_scheduled_behavior_premises@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (inst_9 : Prosa_Behavior_Job_JobDeadline
                                                                                Job
                                                                                inst_3)
  (inst_12 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Ideal_processor_state Job
                inst_3)) =>
And
  (Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
     inst_3
     inst_12
     (Prosa_Model_Processor_Ideal_processor_state Job
        inst_3)
     sched)
  (And
     (Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
        inst_3
        (Prosa_Model_Processor_Ideal_processor_state Job
           inst_3)
        sched inst_6)
     (And
        (Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
           inst_3
           (Prosa_Model_Processor_Ideal_processor_state Job
              inst_3)
           sched arr_seq)
        (Prosa_Analysis_Definitions_Schedulability_all_deadlines_met_inst4 Job
           inst_3
           inst_6
           inst_9
           (Prosa_Model_Processor_Ideal_processor_state Job
              inst_3)
           sched)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       SProp

Arguments Prosa_Analysis_Facts_Transform_EdfWc_scheduled_behavior_premises Job
  inst_3
  inst_6
  inst_9
  inst_12 arr_seq 
  sched
```
