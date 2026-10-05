# `edf_transform_prefix`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.edf_trans.edf_transform_prefix`
- Lean: `Prosa.Analysis.Transform.EdfTrans.edf_transform_prefix`
- Certificate: `edf_transform_prefix_correspondence`

## Official Rocq

```coq
edf_transform_prefix :
forall {Job : JobType},
JobDeadline Job ->
JobArrival Job ->
@schedule Job (ideal.processor_state Job) -> instant -> @schedule Job (ideal.processor_state Job)

edf_transform_prefix is not universe polymorphic
Arguments edf_transform_prefix {Job H0 H1} sched horizon _
edf_transform_prefix is transparent
Expands to: Constant prosa.analysis.transform.edf_trans.edf_transform_prefix
Declared in library prosa.analysis.transform.edf_trans, line 58, characters 13-33
@edf_transform_prefix
     : forall Job : JobType,
       JobDeadline Job ->
       JobArrival Job ->
       @schedule Job (ideal.processor_state Job) -> instant -> @schedule Job (ideal.processor_state Job)
```

Body:

```coq
edf_transform_prefix =
fun (Job : JobType) (H0 : JobDeadline Job) (H1 : JobArrival Job) =>
let PState := ideal.processor_state Job in
let SchedType := @schedule Job PState in
fun sched : SchedType => [eta @prefix_map Job PState sched (@make_edf_at Job H0 H1)]
     : forall {Job : JobType},
       JobDeadline Job ->
       JobArrival Job ->
       @schedule Job (ideal.processor_state Job) -> instant -> @schedule Job (ideal.processor_state Job)

Arguments edf_transform_prefix {Job H0 H1} sched horizon _
```

## Lean

```lean
@Prosa.Analysis.Transform.EdfTrans.edf_transform_prefix : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
          Prosa.Behavior.Time.instant →
            Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)
```

Body:

```lean
def Prosa.Analysis.Transform.EdfTrans.edf_transform_prefix.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
          Prosa.Behavior.Time.instant →
            Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobDeadline Job] [Prosa.Behavior.Job.JobArrival Job] sched horizon =>
  Prosa.Analysis.Transform.Prefix.prefix_map sched Prosa.Analysis.Transform.EdfTrans.make_edf_at horizon
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
```

Body:

```coq
Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobDeadline
                                                                              Job
                                                                              inst_3)
  (inst_9 : Prosa_Behavior_Job_JobArrival Job
                                                                              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Ideal_processor_state Job
                inst_3))
  (horizon : Prosa_Behavior_Time_instant) =>
Prosa_Analysis_Transform_Prefix_prefix_map_inst4 Job
  inst_3
  (Prosa_Model_Processor_Ideal_processor_state Job
     inst_3)
  sched
  (Prosa_Analysis_Transform_EdfTrans_make_edf_at Job
     inst_3
     inst_6
     inst_9)
  horizon
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)

Arguments Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix Job
  inst_3
  inst_6
  inst_9 sched t1 
  a____at____internal__hyg0
```
