# `wc_transform`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.wc_trans.wc_transform`
- Lean: `Prosa.Analysis.Transform.WcTrans.wc_transform`
- Certificate: `wc_transform_correspondence`

## Official Rocq

```coq
wc_transform :
forall {Job : JobType},
JobArrival Job ->
JobDeadline Job ->
arrival_sequence Job -> @schedule Job (processor_state Job) -> nat -> @State Job (processor_state Job)

wc_transform is not universe polymorphic
Arguments wc_transform {Job H H1} arr_seq sched t%nat_scope
wc_transform is transparent
Expands to: Constant prosa.analysis.transform.wc_trans.wc_transform
Declared in library prosa.analysis.transform.wc_trans, line 79, characters 13-25
@wc_transform
     : forall Job : JobType,
       JobArrival Job ->
       JobDeadline Job ->
       arrival_sequence Job -> @schedule Job (processor_state Job) -> nat -> @State Job (processor_state Job)
```

Body:

```coq
wc_transform =
fun (Job : JobType) (H : JobArrival Job) (H1 : JobDeadline Job) =>
let PState := processor_state Job in
fun (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) (t : nat) =>
let wc_prefix := @wc_transform_prefix Job H H1 arr_seq sched t.+1 in wc_prefix t
     : forall {Job : JobType},
       JobArrival Job ->
       JobDeadline Job ->
       arrival_sequence Job -> @schedule Job (processor_state Job) -> nat -> @State Job (processor_state Job)

Arguments wc_transform {Job H H1} arr_seq sched t%nat_scope
```

## Lean

```lean
@Prosa.Analysis.Transform.WcTrans.wc_transform : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
            ℕ → Prosa.Behavior.Schedule.ProcessorState.State Job
```

Body:

```lean
def Prosa.Analysis.Transform.WcTrans.wc_transform.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
            ℕ → Prosa.Behavior.Schedule.ProcessorState.State Job :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobDeadline Job] arr_seq sched t =>
  have wc_prefix := Prosa.Analysis.Transform.WcTrans.wc_transform_prefix arr_seq sched (t + 1);
  wc_prefix t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_WcTrans_wc_transform
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Nat ->
       Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
```

Body:

```coq
Prosa_Analysis_Transform_WcTrans_wc_transform@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
  (t : Nat) =>
let wc_prefix :=
  Prosa_Analysis_Transform_WcTrans_wc_transform_prefix Job
    inst_3
    inst_6
    inst_9 arr_seq sched
    (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) t
       (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
  in
wc_prefix t
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Nat ->
       Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)

Arguments Prosa_Analysis_Transform_WcTrans_wc_transform Job
  inst_3
  inst_6
  inst_9 arr_seq sched 
  t%_Nat_scope
```
