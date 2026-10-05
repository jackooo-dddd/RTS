# `athep_workload_is_bounded`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.workload.bounded.athep_workload_is_bounded`
- Lean: `Prosa.Analysis.Definitions.Workload.Bounded.athep_workload_is_bounded`
- Certificate: `athep_workload_is_bounded_correspondence`

## Official Rocq

```coq
athep_workload_is_bounded :
forall {Task : TaskType} {Job : JobType},
JobCost Job ->
JobArrival Job ->
JobTask Job Task ->
forall {PState : ProcessorState Job},
JLFP_policy Job ->
arrival_sequence Job -> @schedule Job PState -> Equality.sort Task -> (duration -> duration -> work) -> Prop

athep_workload_is_bounded is not universe polymorphic
Arguments athep_workload_is_bounded {Task Job H H0 H1 PState JLFP} arr_seq sched tsk B%function_scope
athep_workload_is_bounded is transparent
Expands to: Constant prosa.analysis.definitions.workload.bounded.athep_workload_is_bounded
Declared in library prosa.analysis.definitions.workload.bounded, line 42, characters 13-38
@athep_workload_is_bounded
     : forall (Task : TaskType) (Job : JobType),
       JobCost Job ->
       JobArrival Job ->
       JobTask Job Task ->
       forall PState : ProcessorState Job,
       JLFP_policy Job ->
       arrival_sequence Job ->
       @schedule Job PState -> Equality.sort Task -> (duration -> duration -> work) -> Prop
```

Body:

```coq
athep_workload_is_bounded =
fun (Task : TaskType) (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (H1 : JobTask Job Task)
  (PState : ProcessorState Job) (JLFP : JLFP_policy Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (tsk : Equality.sort Task) (B : duration -> duration -> work) =>
forall (j : Equality.sort Job) (t1 : instant) (Δ : duration),
is_true (@job_cost_positive Job H j) ->
is_true (@job_of_task Job Task H1 tsk j) ->
@quiet_time Job H0 H PState arr_seq sched JLFP j t1 ->
is_true
  (@workload_of_jobs Job H ((@another_task_hep_job Task Job H1 JLFP)^~ j)
     (@arrivals_between Job arr_seq t1 (t1 + Δ)) <=
   B (@job_arrival Job H0 j - t1) Δ)
     : forall {Task : TaskType} {Job : JobType},
       JobCost Job ->
       JobArrival Job ->
       JobTask Job Task ->
       forall {PState : ProcessorState Job},
       JLFP_policy Job ->
       arrival_sequence Job ->
       @schedule Job PState -> Equality.sort Task -> (duration -> duration -> work) -> Prop

Arguments athep_workload_is_bounded {Task Job H H0 H1 PState JLFP} arr_seq sched tsk B%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.Workload.Bounded.athep_workload_is_bounded : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Behavior.Job.JobCost Job] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                    Prosa.Behavior.Schedule.schedule PState →
                      Task →
                        (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.Workload.Bounded.athep_workload_is_bounded.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Behavior.Job.JobCost Job] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                    Prosa.Behavior.Schedule.schedule PState →
                      Task →
                        (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) →
                          Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Model.Task.Concept.JobTask Job Task] {PState}
    [Prosa.Model.Priority.Definitions.JLFP_policy Job] arr_seq sched tsk B =>
  ∀ (j : Job) (t1 : Prosa.Behavior.Time.instant) (Δ : Prosa.Behavior.Time.duration),
    Prosa.Model.Job.Properties.job_cost_positive j = true →
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t1 →
          Prosa.Model.Aggregate.Workload.workload_of_jobs
              (fun j' => Prosa.Model.Priority.Definitions.another_task_hep_job j' j)
              (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + Δ)) ≤
            B (Prosa.Behavior.Job.job_arrival j - t1) Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Workload_Bounded_athep_workload_is_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Task ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Workload_Bounded_athep_workload_is_bounded@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0
Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : 
   Prosa_Behavior_Job_JobCost Job
     inst_7)
  (inst_13 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_7)
  (inst_16 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7 Task
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7 PState)
  (tsk : Task) (B : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) =>
forall (j : Job) (t1 : Prosa_Behavior_Time_instant) (_UU0394_ : Prosa_Behavior_Time_duration),
@eq Bool
  (Prosa_Model_Job_Properties_job_cost_positive Job
     inst_7
     inst_10 j)
  Bool_true ->
@eq Bool
  (Prosa_Model_Task_Concept_job_of_task Job
     inst_7 Task
     inst_3
     inst_16 tsk j)
  Bool_true ->
Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
  inst_7
  inst_13
  inst_10 PState arr_seq sched JLFP
  j t1 ->
LE_le_inst1 Nat instLENat
  (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
     inst_7
     inst_10
     (fun j' : Job =>
      Prosa_Model_Priority_Definitions_another_task_hep_job Task
        inst_3 Job
        inst_7
        inst_16 JLFP j' j)
     (Prosa_Behavior_Arrival_sequence_arrivals_between Job
        inst_7 arr_seq t1
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)))
  (B
     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_7
           inst_13 j)
        t1)
     _UU0394_)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Task ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp

Arguments Prosa_Analysis_Definitions_Workload_Bounded_athep_workload_is_bounded Task
  inst_3 
  Job inst_7
  inst_10
  inst_13
  inst_16 
  PState JLFP arr_seq sched tsk B%_function_scope
```
