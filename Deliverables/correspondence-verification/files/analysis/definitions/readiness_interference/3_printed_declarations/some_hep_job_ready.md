# `some_hep_job_ready`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.readiness_interference.some_hep_job_ready`
- Lean: `Prosa.Analysis.Definitions.ReadinessInterference.some_hep_job_ready`
- Certificate: `some_hep_job_ready_correspondence`

## Official Rocq

```coq
some_hep_job_ready :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
@JobReady Job PState H0 H ->
arrival_sequence Job -> @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool

some_hep_job_ready is not universe polymorphic
Arguments some_hep_job_ready {Job H H0 PState JobReady0} arr_seq sched {JLFP} j t
some_hep_job_ready is transparent
Expands to: Constant prosa.analysis.definitions.readiness_interference.some_hep_job_ready
Declared in library prosa.analysis.definitions.readiness_interference, line 58, characters 15-33
@some_hep_job_ready
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job),
       @JobReady Job PState H0 H ->
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
some_hep_job_ready =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
  (JobReady0 : @JobReady Job PState H0 H) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  (JLFP : JLFP_policy Job) (j : Equality.sort Job) (t : instant) =>
@has (Equality.sort Job) ((@job_ready Job PState H0 H JobReady0 sched)^~ t)
  [seq j' <- @arrivals_up_to Job arr_seq t | @hep_job Job JLFP j' j]
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
       @JobReady Job PState H0 H ->
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool

Arguments some_hep_job_ready {Job H H0 PState JobReady0} arr_seq sched {JLFP} j t
```

## Lean

```lean
@Prosa.Analysis.Definitions.ReadinessInterference.some_hep_job_ready : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Analysis.Definitions.ReadinessInterference.some_hep_job_ready.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState}
    [Prosa.Behavior.Ready.JobReady Job PState] arr_seq sched [Prosa.Model.Priority.Definitions.JLFP_policy Job] j t =>
  (List.filter (fun j' => Prosa.Model.Priority.Definitions.hep_job j' j)
        (Prosa.Behavior.Arrival_sequence.arrivals_up_to arr_seq t)).any
    fun j' => Prosa.Behavior.Ready.job_ready sched j' t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_9
         inst_6 ->
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
Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (inst_9 : 
   Prosa_Behavior_Job_JobCost Job
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (inst_14 : 
   Prosa_Behavior_Ready_JobReady Job
     inst_3 PState
     inst_9
     inst_6)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (inst_22 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
List_any Job
  (List_filter Job
     (fun j' : Job =>
      Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
        inst_3
        inst_22 j' j)
     (Prosa_Behavior_Arrival_sequence_arrivals_up_to Job
        inst_3 arr_seq t))
  (fun j' : Job =>
   Prosa_Behavior_Ready_JobReady_job_ready Job
     inst_3 PState
     inst_9
     inst_6
     inst_14 sched j' t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_9
         inst_6 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready Job
  inst_3
  inst_6
  inst_9 
  PState inst_14 
  arr_seq sched inst_22 
  j t
```
