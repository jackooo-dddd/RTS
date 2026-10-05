# `valid_busy_sbf`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.sbf.busy.valid_busy_sbf`
- Lean: `Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf`
- Certificate: `valid_busy_sbf_correspondence`

## Official Rocq

```coq
valid_busy_sbf :
forall {Task : TaskType} {Job : JobType},
JobArrival Job ->
JobCost Job ->
JobTask Job Task ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState -> JLFP_policy Job -> Equality.sort Task -> (duration -> work) -> Prop

valid_busy_sbf is not universe polymorphic
Arguments valid_busy_sbf {Task Job H H0 H1 PState} arr_seq sched {H2} tsk SBF%function_scope
valid_busy_sbf is transparent
Expands to: Constant prosa.analysis.definitions.sbf.busy.valid_busy_sbf
Declared in library prosa.analysis.definitions.sbf.busy, line 49, characters 13-27
@valid_busy_sbf
     : forall (Task : TaskType) (Job : JobType),
       JobArrival Job ->
       JobCost Job ->
       JobTask Job Task ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Task -> (duration -> work) -> Prop
```

Body:

```coq
valid_busy_sbf =
fun (Task : TaskType) (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobTask Job Task)
  (PState : ProcessorState Job) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  (H2 : JLFP_policy Job) (tsk : Equality.sort Task) =>
let bi_prefix_of_tsk :=
  fun (j : Equality.sort Job) (t1 t2 : instant) =>
  is_true (@job_of_task Job Task H1 tsk j) /\ @busy_interval_prefix Job H H0 PState arr_seq sched H2 j t1 t2
  in
     : forall {Task : TaskType} {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       JobTask Job Task ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Task -> (duration -> work) -> Prop

Arguments valid_busy_sbf {Task Job H H0 H1 PState} arr_seq sched {H2} tsk SBF%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                  Prosa.Behavior.Schedule.schedule PState →
                    [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                      Task → (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                  Prosa.Behavior.Schedule.schedule PState →
                    [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                      Task → (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Task.Concept.JobTask Job Task] {PState} arr_seq sched
    [Prosa.Model.Priority.Definitions.JLFP_policy Job] tsk SBF =>
  Prosa.Analysis.Definitions.Sbf.Pred.valid_pred_sbf arr_seq sched
    (fun j t1 t2 =>
      Prosa.Model.Task.Concept.job_of_task tsk j = true ∧
        Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2)
    SBF
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Sbf_Busy_valid_busy_sbf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Task -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Sbf_Busy_valid_busy_sbf@{u_1 u_2 u_3 u_4 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0 Lean.u_2+2.0
Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_7)
  (inst_13 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_7)
  (inst_16 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7 PState)
  (inst_26 : Prosa_Model_Priority_Definitions_JLFP_policy
                                                                                Job
                                                                                inst_7)
  (tsk : Task) (SBF : Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) =>
Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf Job
  inst_7 PState arr_seq sched
  (fun (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
   And
     (@eq Bool
        (Prosa_Model_Task_Concept_job_of_task Job
           inst_7 Task
           inst_3
           inst_16 tsk j)
        Bool_true)
     (Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
        inst_7
        inst_10
        inst_13 PState arr_seq sched
        inst_26 j t1 t2))
  SBF
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Task -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp

Arguments Prosa_Analysis_Definitions_Sbf_Busy_valid_busy_sbf Task
  inst_3 Job
  inst_7
  inst_10
  inst_13
  inst_16 PState 
  arr_seq sched inst_26 
  tsk SBF%_function_scope
```
