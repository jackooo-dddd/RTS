# `priority_inversion_of_job_cond_is_bounded_by`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.priority_inversion.priority_inversion_of_job_cond_is_bounded_by`
- Lean: `Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_of_job_cond_is_bounded_by`
- Certificate: `priority_inversion_of_job_cond_is_bounded_by_correspondence`

## Official Rocq

```coq
priority_inversion_of_job_cond_is_bounded_by :
forall {Job : JobType},
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState ->
JLFP_policy Job -> Equality.sort Job -> pred (Equality.sort Job) -> (duration -> duration) -> Prop

priority_inversion_of_job_cond_is_bounded_by is not universe polymorphic
Arguments priority_inversion_of_job_cond_is_bounded_by {Job H0 H1 PState} arr_seq 
  sched {H2} j P B%function_scope
priority_inversion_of_job_cond_is_bounded_by is transparent
Expands to: Constant
            prosa.analysis.definitions.priority_inversion.priority_inversion_of_job_cond_is_bounded_by
Declared in library prosa.analysis.definitions.priority_inversion, line 79, characters 13-57
@priority_inversion_of_job_cond_is_bounded_by
     : forall Job : JobType,
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState ->
       JLFP_policy Job -> Equality.sort Job -> pred (Equality.sort Job) -> (duration -> duration) -> Prop
```

Body:

```coq
priority_inversion_of_job_cond_is_bounded_by =
fun (Job : JobType) (H0 : JobArrival Job) (H1 : JobCost Job) (PState : ProcessorState Job)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (H2 : JLFP_policy Job)
  (j : Equality.sort Job) (P : pred (Equality.sort Job)) (B : duration -> duration) =>
forall t1 t2 : instant,
@busy_interval_prefix Job H0 H1 PState arr_seq sched H2 j t1 t2 ->
is_true
  (@cumulative_priority_inversion_cond Job PState arr_seq sched H2 j P t1 t2 <=
   B (@job_arrival Job H0 j - t1))
     : forall {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       JLFP_policy Job -> Equality.sort Job -> pred (Equality.sort Job) -> (duration -> duration) -> Prop

Arguments priority_inversion_of_job_cond_is_bounded_by {Job H0 H1 PState} arr_seq 
  sched {H2} j P B%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_of_job_cond_is_bounded_by : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            Prosa.Behavior.Schedule.schedule PState →
              [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                Job → (Job → Bool) → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_of_job_cond_is_bounded_by.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            Prosa.Behavior.Schedule.schedule PState →
              [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                Job → (Job → Bool) → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched
    [Prosa.Model.Priority.Definitions.JLFP_policy Job] j P B =>
  ∀ (t1 t2 : Prosa.Behavior.Time.instant),
    Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
      Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion_cond arr_seq sched j P t1 t2 ≤
        B (Prosa.Behavior.Job.job_arrival j - t1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_of_job_cond_is_bounded_by
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> (Job -> Bool) -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_of_job_cond_is_bounded_by@{u_1 u_2 u_3
Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_14 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_7)
  (inst_17 : 
   Prosa_Behavior_Job_JobCost Job
     inst_7)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7 PState)
  (inst_26 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_7)
  (j : Job) (P : Job -> Bool) (B : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) =>
forall t1 t2 : Prosa_Behavior_Time_instant,
Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
  inst_7
  inst_14
  inst_17 PState arr_seq sched
  inst_26 j t1 t2 ->
LE_le_inst1 Nat instLENat
  (Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion_cond Job
     inst_7 PState arr_seq sched
     inst_26 j P t1 t2)
  (B
     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_7
           inst_14 j)
        t1))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> (Job -> Bool) -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp

Arguments Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_of_job_cond_is_bounded_by 
  Job inst_7
  inst_14
  inst_17 
  PState arr_seq sched inst_26 
  j (P B)%_function_scope
```
