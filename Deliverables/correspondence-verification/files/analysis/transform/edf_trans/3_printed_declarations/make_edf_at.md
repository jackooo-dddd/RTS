# `make_edf_at`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.edf_trans.make_edf_at`
- Lean: `Prosa.Analysis.Transform.EdfTrans.make_edf_at`
- Certificate: `make_edf_at_correspondence`

## Official Rocq

```coq
make_edf_at :
forall {Job : JobType},
JobDeadline Job ->
JobArrival Job ->
@schedule Job (ideal.processor_state Job) -> instant -> @schedule Job (ideal.processor_state Job)

make_edf_at is not universe polymorphic
Arguments make_edf_at {Job H0 H1} sched t1 _
make_edf_at is transparent
Expands to: Constant prosa.analysis.transform.edf_trans.make_edf_at
Declared in library prosa.analysis.transform.edf_trans, line 47, characters 13-24
@make_edf_at
     : forall Job : JobType,
       JobDeadline Job ->
       JobArrival Job ->
       @schedule Job (ideal.processor_state Job) -> instant -> @schedule Job (ideal.processor_state Job)
```

Body:

```coq
make_edf_at =
fun (Job : JobType) (H0 : JobDeadline Job) (H1 : JobArrival Job) =>
let PState := ideal.processor_state Job in
let SchedType := @schedule Job PState in
fun (sched : SchedType) (t1 : instant) =>
match sched t1 with
| @Some _ j => let t2 := @find_swap_candidate Job H0 H1 sched t1 j in @swapped Job PState sched t1 t2
| @None _ => sched
end
     : forall {Job : JobType},
       JobDeadline Job ->
       JobArrival Job ->
       @schedule Job (ideal.processor_state Job) -> instant -> @schedule Job (ideal.processor_state Job)

Arguments make_edf_at {Job H0 H1} sched t1 _
```

## Lean

```lean
@Prosa.Analysis.Transform.EdfTrans.make_edf_at : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
          Prosa.Behavior.Time.instant →
            Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)
```

Body:

```lean
def Prosa.Analysis.Transform.EdfTrans.make_edf_at.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
          Prosa.Behavior.Time.instant →
            Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobDeadline Job] [Prosa.Behavior.Job.JobArrival Job] sched t1 =>
  match sched t1 with
  | none => sched
  | some j =>
    have t2 := Prosa.Analysis.Transform.EdfTrans.find_swap_candidate sched t1 j;
    Prosa.Analysis.Transform.Swap.swapped sched t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_EdfTrans_make_edf_at
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
Prosa_Analysis_Transform_EdfTrans_make_edf_at@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobDeadline Job
                                                                             inst_3)
  (inst_9 : Prosa_Behavior_Job_JobArrival Job
                                                                             inst_3)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Ideal_processor_state Job
                inst_3))
  (t1 : Prosa_Behavior_Time_instant) =>
Prosa_Analysis_Transform_EdfTrans_earlier_deadline_match_1 Job
  inst_3
  (fun
     _ : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
           inst_3
           (Prosa_Model_Processor_Ideal_processor_state Job
              inst_3) =>
   Prosa_Behavior_Schedule_schedule_inst4 Job
     inst_3
     (Prosa_Model_Processor_Ideal_processor_state Job
        inst_3))
  (sched t1) (fun _ : Unit => sched)
  (fun j : Job =>
   let t2 :=
     Prosa_Analysis_Transform_EdfTrans_find_swap_candidate Job
       inst_3
       inst_6
       inst_9 sched t1 j
     in
   Prosa_Analysis_Transform_Swap_swapped_inst4 Job
     inst_3
     (Prosa_Model_Processor_Ideal_processor_state Job
        inst_3)
     sched t1 t2)
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

Arguments Prosa_Analysis_Transform_EdfTrans_make_edf_at Job
  inst_3
  inst_6
  inst_9 sched t1 
  a____at____internal__hyg0
```
