# `find_swap_candidate`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.edf_trans.find_swap_candidate`
- Lean: `Prosa.Analysis.Transform.EdfTrans.find_swap_candidate`
- Certificate: `find_swap_candidate_correspondence`

## Official Rocq

```coq
find_swap_candidate :
forall {Job : JobType},
JobDeadline Job ->
JobArrival Job -> @schedule Job (ideal.processor_state Job) -> instant -> Equality.sort Job -> nat

find_swap_candidate is not universe polymorphic
Arguments find_swap_candidate {Job H0 H1} sched t1 j
find_swap_candidate is transparent
Expands to: Constant prosa.analysis.transform.edf_trans.find_swap_candidate
Declared in library prosa.analysis.transform.edf_trans, line 38, characters 13-32
@find_swap_candidate
     : forall Job : JobType,
       JobDeadline Job ->
       JobArrival Job -> @schedule Job (ideal.processor_state Job) -> instant -> Equality.sort Job -> nat
```

Body:

```coq
find_swap_candidate =
fun (Job : JobType) (H0 : JobDeadline Job) (H1 : JobArrival Job) =>
let PState := ideal.processor_state Job in
let SchedType := @schedule Job PState in
fun (sched : SchedType) (t1 : instant) (j : Equality.sort Job) =>
match
  @search_arg (@State Job PState) sched (@relevant_pstate Job H1 t1) (@earlier_deadline Job H0) t1
    (@job_deadline Job H0 j)
with
| @Some _ t => t
| @None _ => 0
end
     : forall {Job : JobType},
       JobDeadline Job ->
       JobArrival Job -> @schedule Job (ideal.processor_state Job) -> instant -> Equality.sort Job -> nat

Arguments find_swap_candidate {Job H0 H1} sched t1 j
```

## Lean

```lean
@Prosa.Analysis.Transform.EdfTrans.find_swap_candidate : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
          Prosa.Behavior.Time.instant → Job → ℕ
```

Body:

```lean
def Prosa.Analysis.Transform.EdfTrans.find_swap_candidate.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobDeadline Job] →
      [Prosa.Behavior.Job.JobArrival Job] →
        Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
          Prosa.Behavior.Time.instant → Job → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobDeadline Job] [Prosa.Behavior.Job.JobArrival Job] sched t1 j =>
  match
    Prosa.Util.SearchArg.search_arg sched (Prosa.Analysis.Transform.EdfTrans.relevant_pstate t1)
      Prosa.Analysis.Transform.EdfTrans.earlier_deadline t1 (Prosa.Behavior.Job.job_deadline j) with
  | some t => t
  | none => 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_EdfTrans_find_swap_candidate
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
       Prosa_Behavior_Time_instant -> Job -> Nat
```

Body:

```coq
Prosa_Analysis_Transform_EdfTrans_find_swap_candidate@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
  (t1 : Prosa_Behavior_Time_instant) (j : Job) =>
Prosa_Analysis_Transform_EdfTrans_find_swap_candidate_match_1 (fun _ : Option_inst1 Nat => Nat)
  (Prosa_Util_SearchArg_search_arg
     (Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
        inst_3
        (Prosa_Model_Processor_Ideal_processor_state Job
           inst_3))
     sched
     (Prosa_Analysis_Transform_EdfTrans_relevant_pstate Job
        inst_3
        inst_9 t1)
     (Prosa_Analysis_Transform_EdfTrans_earlier_deadline Job
        inst_3
        inst_6)
     t1
     (Prosa_Behavior_Job_JobDeadline_job_deadline Job
        inst_3
        inst_6 j))
  (fun a : Nat => a) (fun _ : Unit => OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
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
       Prosa_Behavior_Time_instant -> Job -> Nat

Arguments Prosa_Analysis_Transform_EdfTrans_find_swap_candidate Job
  inst_3
  inst_6
  inst_9 sched t1 
  j
```
