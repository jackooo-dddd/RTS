# `search_result`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.transform.wc_correctness.search_result`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.search_result`
- Certificate: `search_result_correspondence`

## Official Rocq

```coq
search_result :
forall {Job : JobType},
JobArrival Job ->
JobDeadline Job -> arrival_sequence Job -> @schedule Job (processor_state Job) -> instant -> option nat

search_result is not universe polymorphic
Arguments search_result {Job H H1} arr_seq sched t
search_result is transparent
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.search_result
Declared in library prosa.analysis.facts.transform.wc_correctness, line 232, characters 17-30
@search_result
     : forall Job : JobType,
       JobArrival Job ->
       JobDeadline Job ->
       arrival_sequence Job -> @schedule Job (processor_state Job) -> instant -> option nat
```

Body:

```coq
search_result =
fun (Job : JobType) (H : JobArrival Job) (H1 : JobDeadline Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job (processor_state Job)) (t : instant) =>
let max_dl := @max_deadline_for_jobs_arrived_before Job H1 arr_seq t in
@search_arg (@State Job (processor_state Job)) sched (@relevant_pstate Job H t)
  (fun x x0 : @State Job (processor_state Job) =>
   order (nat_of_bool (@isSome (Equality.sort Job) x)) (nat_of_bool (@isSome (Equality.sort Job) x0)))
  t max_dl
     : forall {Job : JobType},
       JobArrival Job ->
       JobDeadline Job ->
       arrival_sequence Job -> @schedule Job (processor_state Job) -> instant -> option nat

Arguments search_result {Job H H1} arr_seq sched t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.search_result : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
            Prosa.Behavior.Time.instant → Option ℕ
```

Body:

```lean
def Prosa.Analysis.Facts.Transform.WcCorrectness.search_result.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
            Prosa.Behavior.Time.instant → Option ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobDeadline Job] arr_seq sched t =>
  have max_dl := Prosa.Analysis.Transform.WcTrans.max_deadline_for_jobs_arrived_before arr_seq t;
  Prosa.Util.SearchArg.search_arg sched (Prosa.Analysis.Transform.WcTrans.relevant_pstate t)
    (fun x y => Prosa.Analysis.Facts.Transform.WcCorrectness.order (Option.isSome x).toNat (Option.isSome y).toNat) t
    max_dl
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_search_result
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
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
       Prosa_Behavior_Time_instant -> Option_inst1 Nat
```

Body:

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_search_result@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (inst_9 : 
   Prosa_Behavior_Job_JobDeadline Job
     inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Ideal_processor_state Job
                inst_3))
  (t : Prosa_Behavior_Time_instant) =>
let max_dl :=
  Prosa_Analysis_Transform_WcTrans_max_deadline_for_jobs_arrived_before Job
    inst_3
    inst_9 arr_seq t
  in
Prosa_Util_SearchArg_search_arg
  (Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
     inst_3
     (Prosa_Model_Processor_Ideal_processor_state Job
        inst_3))
  sched
  (Prosa_Analysis_Transform_WcTrans_relevant_pstate Job
     inst_3
     inst_6 t)
  (fun
     x
      y : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3) =>
   Prosa_Analysis_Facts_Transform_WcCorrectness_order (Bool_toNat (Option_isSome Job x))
     (Bool_toNat (Option_isSome Job y)))
  t max_dl
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
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
       Prosa_Behavior_Time_instant -> Option_inst1 Nat

Arguments Prosa_Analysis_Facts_Transform_WcCorrectness_search_result Job
  inst_3
  inst_6
  inst_9 
  arr_seq sched t
```
