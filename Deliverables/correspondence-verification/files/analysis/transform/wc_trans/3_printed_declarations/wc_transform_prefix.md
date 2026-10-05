# `wc_transform_prefix`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.wc_trans.wc_transform_prefix`
- Lean: `Prosa.Analysis.Transform.WcTrans.wc_transform_prefix`
- Certificate: `wc_transform_prefix_correspondence`

## Official Rocq

```coq
wc_transform_prefix :
forall {Job : JobType},
JobArrival Job ->
JobDeadline Job ->
arrival_sequence Job -> @schedule Job (processor_state Job) -> instant -> @schedule Job (processor_state Job)

wc_transform_prefix is not universe polymorphic
Arguments wc_transform_prefix {Job H H1} arr_seq sched horizon _
wc_transform_prefix is transparent
Expands to: Constant prosa.analysis.transform.wc_trans.wc_transform_prefix
Declared in library prosa.analysis.transform.wc_trans, line 72, characters 13-32
@wc_transform_prefix
     : forall Job : JobType,
       JobArrival Job ->
       JobDeadline Job ->
       arrival_sequence Job ->
       @schedule Job (processor_state Job) -> instant -> @schedule Job (processor_state Job)
```

Body:

```coq
wc_transform_prefix =
fun (Job : JobType) (H : JobArrival Job) (H1 : JobDeadline Job) =>
let PState := processor_state Job in
fun (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) =>
     : forall {Job : JobType},
       JobArrival Job ->
       JobDeadline Job ->
       arrival_sequence Job ->
       @schedule Job (processor_state Job) -> instant -> @schedule Job (processor_state Job)

Arguments wc_transform_prefix {Job H H1} arr_seq sched horizon _
```

## Lean

```lean
@Prosa.Analysis.Transform.WcTrans.wc_transform_prefix : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
            Prosa.Behavior.Time.instant →
              Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)
```

Body:

```lean
def Prosa.Analysis.Transform.WcTrans.wc_transform_prefix.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
            Prosa.Behavior.Time.instant →
              Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobDeadline Job] arr_seq sched
    horizon =>
  Prosa.Analysis.Transform.Prefix.prefix_map sched (Prosa.Analysis.Transform.WcTrans.make_wc_at arr_seq) horizon
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_WcTrans_wc_transform_prefix
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
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
Prosa_Analysis_Transform_WcTrans_wc_transform_prefix@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                             inst_3)
  (inst_9 : Prosa_Behavior_Job_JobDeadline Job
                                                                             inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
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
  (Prosa_Analysis_Transform_WcTrans_make_wc_at Job
     inst_3
     inst_6
     inst_9 arr_seq)
  horizon
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
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

Arguments Prosa_Analysis_Transform_WcTrans_wc_transform_prefix Job
  inst_3
  inst_6
  inst_9 arr_seq sched 
  t1 a____at____internal__hyg0
```
