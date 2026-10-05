# `sequential_readiness`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.readiness.sequential_readiness`
- Lean: `Prosa.Analysis.Definitions.Readiness.sequential_readiness`
- Certificate: `sequential_readiness_correspondence`

## Official Rocq

```coq
sequential_readiness :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job},
@JobReady Job PState H H0 -> forall {Task : TaskType}, JobTask Job Task -> arrival_sequence Job -> Prop

sequential_readiness is not universe polymorphic
Arguments sequential_readiness {Job H H0 PState} ReadinessModel {Task H2} arr_seq
sequential_readiness is transparent
Expands to: Constant prosa.analysis.definitions.readiness.sequential_readiness
Declared in library prosa.analysis.definitions.readiness, line 57, characters 13-33
@sequential_readiness
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job),
       @JobReady Job PState H H0 -> forall Task : TaskType, JobTask Job Task -> arrival_sequence Job -> Prop
```

Body:

```coq
sequential_readiness =
fun (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job)
  (ReadinessModel : @JobReady Job PState H H0) (Task : TaskType) (H2 : JobTask Job Task)
  (arr_seq : arrival_sequence Job) =>
forall (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant),
is_true (@job_ready Job PState H H0 ReadinessModel sched j t) ->
is_true (@prior_jobs_complete Job Task H2 H0 H PState arr_seq sched j t)
     : forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job},
       @JobReady Job PState H H0 ->
       forall {Task : TaskType}, JobTask Job Task -> arrival_sequence Job -> Prop

Arguments sequential_readiness {Job H H0 PState} ReadinessModel {Task H2} arr_seq
```

## Lean

```lean
@Prosa.Analysis.Definitions.Readiness.sequential_readiness : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Ready.JobReady Job PState →
            {Task : Prosa.Model.Task.Concept.TaskType} →
              [inst_3 : DecidableEq Task] →
                [Prosa.Model.Task.Concept.JobTask Job Task] →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.Readiness.sequential_readiness.{u_1, u_2, u_3, u_4} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Ready.JobReady Job PState →
            {Task : Prosa.Model.Task.Concept.TaskType} →
              [inst_3 : DecidableEq Task] →
                [Prosa.Model.Task.Concept.JobTask Job Task] →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job] {PState} ReadinessModel
    {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task] arr_seq =>
  ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Ready.job_ready sched j t = true →
      Prosa.Model.Task.Sequentiality.prior_jobs_complete arr_seq sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Readiness_sequential_readiness
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_6
         inst_9 ->
       forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_18 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_18 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Readiness_sequential_readiness@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.max__u_1+1_u_4+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0
Lean.u_4+1.0 Lean.u_1+2.0 Lean.u_3+2.0 Lean.u_4+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (inst_9 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (ReadinessModel : Prosa_Behavior_Ready_JobReady Job
                      inst_3 PState
                      inst_6
                      inst_9)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_18 : DecidableEq Task)
  (inst_21 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_3
                                                                                Task
                                                                                inst_18)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3) =>
forall
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (j : Job) (t : Prosa_Behavior_Time_instant),
@eq Bool
  (Prosa_Behavior_Ready_JobReady_job_ready Job
     inst_3 PState
     inst_6
     inst_9 ReadinessModel sched j t)
  Bool_true ->
@eq Bool
  (Prosa_Model_Task_Sequentiality_prior_jobs_complete Job
     inst_3 Task
     inst_18
     inst_21
     inst_9
     inst_6 PState arr_seq sched j t)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_6
         inst_9 ->
       forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_18 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_18 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       SProp

Arguments Prosa_Analysis_Definitions_Readiness_sequential_readiness Job
  inst_3
  inst_6
  inst_9 PState 
  ReadinessModel Task inst_18
  inst_21 arr_seq
```
