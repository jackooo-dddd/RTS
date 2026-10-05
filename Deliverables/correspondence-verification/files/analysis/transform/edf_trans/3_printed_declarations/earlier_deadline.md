# `earlier_deadline`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.edf_trans.earlier_deadline`
- Lean: `Prosa.Analysis.Transform.EdfTrans.earlier_deadline`
- Certificate: `earlier_deadline_correspondence`

## Official Rocq

```coq
earlier_deadline :
forall {Job : JobType},
JobDeadline Job -> @State Job (ideal.processor_state Job) -> @State Job (ideal.processor_state Job) -> bool

earlier_deadline is not universe polymorphic
Arguments earlier_deadline {Job H0} s1 s2
earlier_deadline is transparent
Expands to: Constant prosa.analysis.transform.edf_trans.earlier_deadline
Declared in library prosa.analysis.transform.edf_trans, line 21, characters 13-29
@earlier_deadline
     : forall Job : JobType,
       JobDeadline Job ->
       @State Job (ideal.processor_state Job) -> @State Job (ideal.processor_state Job) -> bool
```

Body:

```coq
earlier_deadline =
fun (Job : JobType) (H0 : JobDeadline Job) =>
let PState := ideal.processor_state Job in
fun s1 s2 : @State Job PState => oapp (@job_deadline Job H0) 0 s1 <= oapp (@job_deadline Job H0) 0 s2
     : forall {Job : JobType},
       JobDeadline Job ->
       @State Job (ideal.processor_state Job) -> @State Job (ideal.processor_state Job) -> bool

Arguments earlier_deadline {Job H0} s1 s2
```

## Lean

```lean
@Prosa.Analysis.Transform.EdfTrans.earlier_deadline : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      Prosa.Behavior.Schedule.ProcessorState.State Job → Prosa.Behavior.Schedule.ProcessorState.State Job → Bool
```

Body:

```lean
def Prosa.Analysis.Transform.EdfTrans.earlier_deadline.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      Prosa.Behavior.Schedule.ProcessorState.State Job → Prosa.Behavior.Schedule.ProcessorState.State Job → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobDeadline Job] s1 s2 =>
  decide
    ((match s1 with
      | none => 0
      | some j => Prosa.Behavior.Job.job_deadline j) ≤
      match s2 with
      | none => 0
      | some j => Prosa.Behavior.Job.job_deadline j)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_EdfTrans_earlier_deadline
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Bool
```

Body:

```coq
Prosa_Analysis_Transform_EdfTrans_earlier_deadline@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobDeadline Job
                                                                             inst_3)
  (s1
   s2 : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
          inst_3
          (Prosa_Model_Processor_Ideal_processor_state Job
             inst_3)) =>
Decidable_decide
  (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
     (Prosa_Analysis_Transform_EdfTrans_earlier_deadline_match_1 Job
        inst_3
        (fun
           _ : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
                 inst_3
                 (Prosa_Model_Processor_Ideal_processor_state Job
                    inst_3) =>
         Prosa_Behavior_Time_instant)
        s1 (fun _ : Unit => OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0))
        (fun j : Job =>
         Prosa_Behavior_Job_JobDeadline_job_deadline Job
           inst_3
           inst_6 j))
     (Prosa_Analysis_Transform_EdfTrans_earlier_deadline_match_1 Job
        inst_3
        (fun
           _ : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
                 inst_3
                 (Prosa_Model_Processor_Ideal_processor_state Job
                    inst_3) =>
         Prosa_Behavior_Time_instant)
        s2 (fun _ : Unit => OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0))
        (fun j : Job =>
         Prosa_Behavior_Job_JobDeadline_job_deadline Job
           inst_3
           inst_6 j)))
  (Nat_decLe
     (Prosa_Analysis_Transform_EdfTrans_earlier_deadline_match_1 Job
        inst_3
        (fun
           _ : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
                 inst_3
                 (Prosa_Model_Processor_Ideal_processor_state Job
                    inst_3) =>
         Prosa_Behavior_Time_instant)
        s1 (fun _ : Unit => OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0))
        (fun j : Job =>
         Prosa_Behavior_Job_JobDeadline_job_deadline Job
           inst_3
           inst_6 j))
     (Prosa_Analysis_Transform_EdfTrans_earlier_deadline_match_1 Job
        inst_3
        (fun
           _ : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
                 inst_3
                 (Prosa_Model_Processor_Ideal_processor_state Job
                    inst_3) =>
         Prosa_Behavior_Time_instant)
        s2 (fun _ : Unit => OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0))
        (fun j : Job =>
         Prosa_Behavior_Job_JobDeadline_job_deadline Job
           inst_3
           inst_6 j)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Bool

Arguments Prosa_Analysis_Transform_EdfTrans_earlier_deadline Job
  inst_3
  inst_6 s1 s2
```
