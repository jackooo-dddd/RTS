# `cumulative_interference_from_hep_jobs_from_other_ep_tasks`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.interference.cumulative_interference_from_hep_jobs_from_other_ep_tasks`
- Lean: `Prosa.Analysis.Definitions.Interference.cumulative_interference_from_hep_jobs_from_other_ep_tasks`
- Certificate: `cumulative_interference_from_hep_jobs_from_other_ep_tasks_correspondence`

## Official Rocq

```coq
cumulative_interference_from_hep_jobs_from_other_ep_tasks :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState -> FP_policy Task -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> nat

cumulative_interference_from_hep_jobs_from_other_ep_tasks is not universe polymorphic
Arguments cumulative_interference_from_hep_jobs_from_other_ep_tasks {Task Job jt PState} 
  arr_seq sched {FP JLFP} j t1 t2
cumulative_interference_from_hep_jobs_from_other_ep_tasks is transparent
Expands to: Constant
            prosa.analysis.definitions.interference.cumulative_interference_from_hep_jobs_from_other_ep_tasks
Declared in library prosa.analysis.definitions.interference, line 69, characters 15-72
@cumulative_interference_from_hep_jobs_from_other_ep_tasks
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState ->
       FP_policy Task -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> nat
```

Body:

```coq
cumulative_interference_from_hep_jobs_from_other_ep_tasks =
fun (Task : TaskType) (Job : JobType) (jt : JobTask Job Task) (PState : ProcessorState Job)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (FP : FP_policy Task)
  (JLFP : JLFP_policy Job) (j : Equality.sort Job) (t1 t2 : instant) =>
\sum_(t1 <= t < t2)
   nat_of_bool (@hep_job_from_other_ep_task_interference Task Job jt PState arr_seq sched FP JLFP j t)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       FP_policy Task -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> nat

Arguments cumulative_interference_from_hep_jobs_from_other_ep_tasks {Task Job jt PState} 
  arr_seq sched {FP JLFP} j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Definitions.Interference.cumulative_interference_from_hep_jobs_from_other_ep_tasks : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
                  [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                    Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.Interference.cumulative_interference_from_hep_jobs_from_other_ep_tasks.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
                  [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                    Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] {PState} arr_seq sched
    [Prosa.Model.Priority.Definitions.FP_policy Task] [Prosa.Model.Priority.Definitions.JLFP_policy Job] j t1 t2 =>
  Prosa.Util.Sum.sumSeq (List.range' t1 (t2 - t1)) fun t =>
    (Prosa.Analysis.Definitions.Interference.hep_job_from_other_ep_task_interference arr_seq sched j t).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Interference_cumulative_interference_from_hep_jobs_from_other_ep_tasks
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
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
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_Interference_cumulative_interference_from_hep_jobs_from_other_ep_tasks@{u_1 u_2
u_3 u_4 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0
Lean.u_4+1.0 Lean.u_1+2.0 Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7 Task
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7 PState)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (inst_22 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_7)
  (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
Prosa_Util_Sum_sumSeq_inst1 Nat
  (List_range' t1
     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
  (fun t : Nat =>
   Bool_toNat
     (Prosa_Analysis_Definitions_Interference_hep_job_from_other_ep_task_interference Task
        inst_3 Job
        inst_7
        inst_10 PState arr_seq sched FP
        inst_22 j t))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
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
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Definitions_Interference_cumulative_interference_from_hep_jobs_from_other_ep_tasks
  Task inst_3 
  Job inst_7
  inst_10 PState 
  arr_seq sched FP inst_22 
  j t1 t2
```
