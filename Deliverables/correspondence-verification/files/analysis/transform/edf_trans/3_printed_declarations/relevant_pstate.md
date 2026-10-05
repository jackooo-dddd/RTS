# `relevant_pstate`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.edf_trans.relevant_pstate`
- Lean: `Prosa.Analysis.Transform.EdfTrans.relevant_pstate`
- Certificate: `relevant_pstate_correspondence`

## Official Rocq

```coq
relevant_pstate :
forall {Job : JobType}, JobArrival Job -> instant -> @State Job (ideal.processor_state Job) -> bool

relevant_pstate is not universe polymorphic
Arguments relevant_pstate {Job H1} reference_time s
relevant_pstate is transparent
Expands to: Constant prosa.analysis.transform.edf_trans.relevant_pstate
Declared in library prosa.analysis.transform.edf_trans, line 27, characters 13-28
@relevant_pstate
     : forall Job : JobType, JobArrival Job -> instant -> @State Job (ideal.processor_state Job) -> bool
```

Body:

```coq
relevant_pstate =
fun (Job : JobType) (H1 : JobArrival Job) =>
let PState := ideal.processor_state Job in
fun (reference_time : instant) (s : @State Job PState) =>
match s with
| @Some _ j' => @job_arrival Job H1 j' <= reference_time
| @None _ => false
end
     : forall {Job : JobType}, JobArrival Job -> instant -> @State Job (ideal.processor_state Job) -> bool

Arguments relevant_pstate {Job H1} reference_time s
```

## Lean

```lean
@Prosa.Analysis.Transform.EdfTrans.relevant_pstate : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.ProcessorState.State Job → Bool
```

Body:

```lean
def Prosa.Analysis.Transform.EdfTrans.relevant_pstate.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.ProcessorState.State Job → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] reference_time s =>
  match s with
  | none => false
  | some j' => decide (Prosa.Behavior.Job.job_arrival j' ≤ reference_time)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_EdfTrans_relevant_pstate
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Bool
```

Body:

```coq
Prosa_Analysis_Transform_EdfTrans_relevant_pstate@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                             inst_3)
  (reference_time : Prosa_Behavior_Time_instant)
  (s : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)) =>
Prosa_Analysis_Transform_EdfTrans_earlier_deadline_match_1 Job
  inst_3
  (fun
     _ : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
           inst_3
           (Prosa_Model_Processor_Ideal_processor_state Job
              inst_3) =>
   Bool)
  s (fun _ : Unit => Bool_false)
  (fun j' : Job =>
   Decidable_decide
     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j')
        reference_time)
     (Nat_decLe
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j')
        reference_time))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Time_instant ->
       Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Bool

Arguments Prosa_Analysis_Transform_EdfTrans_relevant_pstate Job
  inst_3
  inst_6 reference_time 
  s2
```
