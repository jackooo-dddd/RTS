# `make_wc_at`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.wc_trans.make_wc_at`
- Lean: `Prosa.Analysis.Transform.WcTrans.make_wc_at`
- Certificate: `make_wc_at_correspondence`

## Official Rocq

```coq
make_wc_at :
forall {Job : JobType},
JobArrival Job ->
JobDeadline Job ->
arrival_sequence Job ->
(instant -> option (Equality.sort Job)) -> instant -> @schedule Job (processor_state Job)

make_wc_at is not universe polymorphic
Arguments make_wc_at {Job H H1} arr_seq sched%function_scope t1 _
make_wc_at is transparent
Expands to: Constant prosa.analysis.transform.wc_trans.make_wc_at
Declared in library prosa.analysis.transform.wc_trans, line 61, characters 13-23
@make_wc_at
     : forall Job : JobType,
       JobArrival Job ->
       JobDeadline Job ->
       arrival_sequence Job ->
       (instant -> option (Equality.sort Job)) -> instant -> @schedule Job (processor_state Job)
```

Body:

```coq
make_wc_at =
fun (Job : JobType) (H : JobArrival Job) (H1 : JobDeadline Job) =>
let PState := processor_state Job in
fun (arr_seq : arrival_sequence Job) (sched : instant -> option (Equality.sort Job)) (t1 : instant) =>
match sched t1 with
| @Some _ _ => sched
| @None _ =>
    let t2 := @find_swap_candidate Job H H1 arr_seq sched t1 in
    @swapped Job (processor_state Job) sched t1 t2
end
     : forall {Job : JobType},
       JobArrival Job ->
       JobDeadline Job ->
       arrival_sequence Job ->
       (instant -> option (Equality.sort Job)) -> instant -> @schedule Job (processor_state Job)

Arguments make_wc_at {Job H H1} arr_seq sched%function_scope t1 _
```

## Lean

```lean
@Prosa.Analysis.Transform.WcTrans.make_wc_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          (Prosa.Behavior.Time.instant → Option Job) →
            Prosa.Behavior.Time.instant →
              Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)
```

Body:

```lean
def Prosa.Analysis.Transform.WcTrans.make_wc_at.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          (Prosa.Behavior.Time.instant → Option Job) →
            Prosa.Behavior.Time.instant →
              Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobDeadline Job] arr_seq sched t1 =>
  match sched t1 with
  | some val => sched
  | none =>
    have t2 := Prosa.Analysis.Transform.WcTrans.find_swap_candidate arr_seq sched t1;
    Prosa.Analysis.Transform.Swap.swapped sched t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_WcTrans_make_wc_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       (Prosa_Behavior_Time_instant -> Option Job) ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
```

Body:

```coq
Prosa_Analysis_Transform_WcTrans_make_wc_at@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                             inst_3)
  (inst_9 : Prosa_Behavior_Job_JobDeadline Job
                                                                             inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Time_instant -> Option Job) (t1 : Prosa_Behavior_Time_instant) =>
Prosa_Analysis_Transform_WcTrans_make_wc_at_match_1 Job
  (fun _ : Option Job =>
   Prosa_Behavior_Schedule_schedule_inst4 Job
     inst_3
     (Prosa_Model_Processor_Ideal_processor_state Job
        inst_3))
  (sched t1) (fun _ : Job => sched)
  (fun _ : Unit =>
   let t2 :=
     Prosa_Analysis_Transform_WcTrans_find_swap_candidate Job
       inst_3
       inst_6
       inst_9 arr_seq sched t1
     in
   Prosa_Analysis_Transform_Swap_swapped_inst4 Job
     inst_3
     (Prosa_Model_Processor_Ideal_processor_state Job
        inst_3)
     sched t1 t2)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       (Prosa_Behavior_Time_instant -> Option Job) ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)

Arguments Prosa_Analysis_Transform_WcTrans_make_wc_at Job
  inst_3
  inst_6
  inst_9 arr_seq sched%_function_scope 
  t1 a____at____internal__hyg0
```
