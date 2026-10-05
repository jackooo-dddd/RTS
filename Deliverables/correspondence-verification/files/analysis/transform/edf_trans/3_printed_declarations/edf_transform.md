# `edf_transform`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.edf_trans.edf_transform`
- Lean: `Prosa.Analysis.Transform.EdfTrans.edf_transform`
- Certificate: `edf_transform_correspondence`

## Official Rocq

```coq
edf_transform :
forall {Job : JobType},
JobDeadline Job ->
JobArrival Job ->
@schedule Job (ideal.processor_state Job) -> instant -> @State Job (ideal.processor_state Job)

edf_transform is not universe polymorphic
Arguments edf_transform {Job H0 H1} sched t
edf_transform is transparent
Expands to: Constant prosa.analysis.transform.edf_trans.edf_transform
Declared in library prosa.analysis.transform.edf_trans, line 65, characters 13-26
@edf_transform
     : forall Job : JobType,
       JobDeadline Job ->
       JobArrival Job ->
       @schedule Job (ideal.processor_state Job) -> instant -> @State Job (ideal.processor_state Job)
```

Body:

```coq
edf_transform =
fun (Job : JobType) (H0 : JobDeadline Job) (H1 : JobArrival Job) =>
let PState := ideal.processor_state Job in
let SchedType := @schedule Job PState in
fun (sched : SchedType) (t : instant) =>
let edf_prefix := @edf_transform_prefix Job H0 H1 sched t.+1 in edf_prefix t
     : forall {Job : JobType},
       JobDeadline Job ->
       JobArrival Job ->
       @schedule Job (ideal.processor_state Job) -> instant -> @State Job (ideal.processor_state Job)

Arguments edf_transform {Job H0 H1} sched t
```

## Lean

```lean
@Prosa.Analysis.Transform.EdfTrans.edf_transform : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
          Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.ProcessorState.State Job
```

Body:

```lean
def Prosa.Analysis.Transform.EdfTrans.edf_transform.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
          Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.ProcessorState.State Job :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobDeadline Job] [Prosa.Behavior.Job.JobArrival Job] sched t =>
  have edf_prefix := Prosa.Analysis.Transform.EdfTrans.edf_transform_prefix sched (t + 1);
  edf_prefix t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_EdfTrans_edf_transform
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
       Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
```

Body:

```coq
Prosa_Analysis_Transform_EdfTrans_edf_transform@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
  (t : Prosa_Behavior_Time_instant) =>
let edf_prefix :=
  Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix Job
    inst_3
    inst_6
    inst_9 sched
    (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
       (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
       (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
  in
edf_prefix t
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
       Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)

Arguments Prosa_Analysis_Transform_EdfTrans_edf_transform Job
  inst_3
  inst_6
  inst_9 sched t
```
