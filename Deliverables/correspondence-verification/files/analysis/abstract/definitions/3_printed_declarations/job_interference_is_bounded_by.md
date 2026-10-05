# `job_interference_is_bounded_by`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.definitions.job_interference_is_bounded_by`
- Lean: `Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by`
- Certificate: `ad_job_interference_bounded_correspondence`

## Official Rocq

```coq
job_interference_is_bounded_by :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task ->
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState ->
Equality.sort Task ->
Interference Job ->
InterferingWorkload Job -> (duration -> duration -> work) -> (Equality.sort Job -> nat -> Prop) -> Prop

job_interference_is_bounded_by is not universe polymorphic
Arguments job_interference_is_bounded_by {Job Task H H0 H1 PState} arr_seq sched 
  tsk {H2 H3} (IBF Param)%function_scope
job_interference_is_bounded_by is transparent
Expands to: Constant prosa.analysis.abstract.definitions.job_interference_is_bounded_by
Declared in library prosa.analysis.abstract.definitions, line 334, characters 13-43
@job_interference_is_bounded_by
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState ->
       Equality.sort Task ->
       Interference Job ->
       InterferingWorkload Job ->
       (duration -> duration -> work) -> (Equality.sort Job -> nat -> Prop) -> Prop
```

Body:

```coq
job_interference_is_bounded_by =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) 
  (H1 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (tsk : Equality.sort Task) (H2 : Interference Job)
  (H3 : InterferingWorkload Job) (IBF : duration -> duration -> work) =>
(@cond_interference_is_bounded_by Job Task H H0 H1 PState arr_seq sched tsk H2 H3 IBF)^~ 
(fun=> xpredT)
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       Equality.sort Task ->
       Interference Job ->
       InterferingWorkload Job ->
       (duration -> duration -> work) -> (Equality.sort Job -> nat -> Prop) -> Prop

Arguments job_interference_is_bounded_by {Job Task H H0 H1 PState} arr_seq sched 
  tsk {H2 H3} (IBF Param)%function_scope
```

## Lean

```lean
@Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                Prosa.Behavior.Schedule.schedule PState →
                  {Task : Prosa.Model.Task.Concept.TaskType} →
                    [inst_5 : DecidableEq Task] →
                      [Prosa.Model.Task.Concept.JobTask Job Task] →
                        Task →
                          (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) →
                            (Job → ℕ → Prop) → Prop
def Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by.{u_1, u_2, u_3, u_4} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                Prosa.Behavior.Schedule.schedule PState →
                  {Task : Prosa.Model.Task.Concept.TaskType} →
                    [inst_5 : DecidableEq Task] →
                      [Prosa.Model.Task.Concept.JobTask Job Task] →
                        Task →
                          (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) →
                            (Job → ℕ → Prop) → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Analysis.Abstract.Definitions.Interference Job]
    [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Job.JobCost Job] {PState} arrSeq sched {Task} [DecidableEq Task]
    [Prosa.Model.Task.Concept.JobTask Job Task] tsk IBF ParamSem =>
  Prosa.Analysis.Abstract.Definitions.cond_interference_is_bounded_by arrSeq sched tsk IBF ParamSem fun x x_1 => true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_25 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_25 ->
       Task ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) ->
       (Job -> Nat -> SProp) -> SProp
```

Body:

```coq
Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_4+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0
Lean.u_3+2.0 Lean.u_4+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                                Job
                                                                                inst_3)
  (inst_9 : Prosa_Analysis_Abstract_Definitions_InterferingWorkload
                                                                                Job
                                                                                inst_3)
  (inst_12 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (inst_15 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arrSeq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_25 : DecidableEq Task)
  (inst_28 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_3
                                                                                Task
                                                                                inst_25)
  (tsk : Task)
  (IBF : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work)
  (ParamSem : Job -> Nat -> SProp) =>
Prosa_Analysis_Abstract_Definitions_cond_interference_is_bounded_by Job
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15 PState arrSeq sched Task
  inst_25
  inst_28 tsk IBF ParamSem
  (fun (_ : Job) (_ : Prosa_Behavior_Time_instant) => Bool_true)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_25 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_25 ->
       Task ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) ->
       (Job -> Nat -> SProp) -> SProp

Arguments Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by Job
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15 PState 
  arrSeq sched Task inst_25
  inst_28 tsk
  (IBF ParamSem)%_function_scope
```
