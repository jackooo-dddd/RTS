# `another_hep_job_interference`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.interference.another_hep_job_interference`
- Lean: `Prosa.Analysis.Definitions.Interference.another_hep_job_interference`
- Certificate: `another_hep_job_interference_correspondence`

## Official Rocq

```coq
another_hep_job_interference :
forall {Job : JobType} {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool

another_hep_job_interference is not universe polymorphic
Arguments another_hep_job_interference {Job PState} arr_seq sched {JLFP} j t
another_hep_job_interference is transparent
Expands to: Constant prosa.analysis.definitions.interference.another_hep_job_interference
Declared in library prosa.analysis.definitions.interference, line 85, characters 15-43
@another_hep_job_interference
     : forall (Job : JobType) (PState : ProcessorState Job),
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
another_hep_job_interference =
fun (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (JLFP : JLFP_policy Job) (j : Equality.sort Job) 
  (t : instant) =>
@has (Equality.sort Job) ((@another_hep_job Job JLFP)^~ j) (@served_jobs_at Job PState arr_seq sched t)
     : forall {Job : JobType} {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool

Arguments another_hep_job_interference {Job PState} arr_seq sched {JLFP} j t
```

## Lean

```lean
@Prosa.Analysis.Definitions.Interference.another_hep_job_interference : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Analysis.Definitions.Interference.another_hep_job_interference.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} arr_seq sched [Prosa.Model.Priority.Definitions.JLFP_policy Job] j t =>
  (Prosa.Analysis.Definitions.Service.served_jobs_at arr_seq sched t).any fun x =>
    Prosa.Model.Priority.Definitions.another_hep_job x j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Interference_another_hep_job_interference
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_Interference_another_hep_job_interference@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (inst_12 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
List_any Job
  (Prosa_Analysis_Definitions_Service_served_jobs_at Job
     inst_3 PState arr_seq sched t)
  (fun x : Job =>
   Prosa_Model_Priority_Definitions_another_hep_job Job
     inst_3
     inst_12 x j)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Definitions_Interference_another_hep_job_interference Job
  inst_3 PState 
  arr_seq sched inst_12 
  j t
```
