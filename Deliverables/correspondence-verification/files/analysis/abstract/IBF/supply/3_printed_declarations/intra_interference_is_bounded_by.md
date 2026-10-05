# `intra_interference_is_bounded_by`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.IBF.supply.intra_interference_is_bounded_by`
- Lean: `Prosa.Analysis.Abstract.IBF.Supply.intra_interference_is_bounded_by`
- Certificate: `intra_interference_is_bounded_by_correspondence`

## Official Rocq

```coq
intra_interference_is_bounded_by :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task ->
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState ->
Equality.sort Task -> Interference Job -> InterferingWorkload Job -> (duration -> duration -> work) -> Prop

intra_interference_is_bounded_by is not universe polymorphic
Arguments intra_interference_is_bounded_by {Job Task H H0 H1 PState} arr_seq sched 
  tsk {H2 H3} intra_IBF%function_scope
intra_interference_is_bounded_by is transparent
Expands to: Constant prosa.analysis.abstract.IBF.supply.intra_interference_is_bounded_by
Declared in library prosa.analysis.abstract.IBF.supply, line 68, characters 13-45
@intra_interference_is_bounded_by
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState ->
       Equality.sort Task ->
       Interference Job -> InterferingWorkload Job -> (duration -> duration -> work) -> Prop
```

Body:

```coq
intra_interference_is_bounded_by =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) 
  (H1 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (tsk : Equality.sort Task) (H2 : Interference Job)
  (H3 : InterferingWorkload Job) (intra_IBF : duration -> duration -> work) =>
@cond_interference_is_bounded_by Job Task H H0 H1 PState arr_seq sched tsk H2 H3 intra_IBF
  (@relative_arrival_time_of_job_is_A Job H0 H1 PState sched H2 H3)
  (fun=> [eta @has_supply Job PState sched])
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       Equality.sort Task ->
       Interference Job -> InterferingWorkload Job -> (duration -> duration -> work) -> Prop

Arguments intra_interference_is_bounded_by {Job Task H H0 H1 PState} arr_seq sched 
  tsk {H2 H3} intra_IBF%function_scope
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Supply.intra_interference_is_bounded_by : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                  Prosa.Behavior.Schedule.schedule PState →
                    Task →
                      [Prosa.Analysis.Abstract.Definitions.Interference Job] →
                        [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
                          (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop
```

Body:

```lean
def Prosa.Analysis.Abstract.IBF.Supply.intra_interference_is_bounded_by.{u_1, u_2, u_3, u_4} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                  Prosa.Behavior.Schedule.schedule PState →
                    Task →
                      [Prosa.Analysis.Abstract.Definitions.Interference Job] →
                        [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
                          (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) →
                            Prop :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched tsk
    [Prosa.Analysis.Abstract.Definitions.Interference Job] [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
    intra_IBF =>
  Prosa.Analysis.Abstract.Definitions.cond_interference_is_bounded_by arr_seq sched tsk intra_IBF
    (Prosa.Analysis.Abstract.AbstractRta.relative_arrival_time_of_job_is_A sched) fun x t =>
    Prosa.Model.Processor.Supply.has_supply sched t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Supply_intra_interference_is_bounded_by
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Task ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp
```

Body:

```coq
Prosa_Analysis_Abstract_IBF_Supply_intra_interference_is_bounded_by@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.max__u_1+1_u_3+2_u_4+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0
Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_3
                                                                                Task
                                                                                inst_7)
  (inst_14 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (inst_17 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (tsk : Task)
  (inst_27 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                                Job
                                                                                inst_3)
  (inst_30 : Prosa_Analysis_Abstract_Definitions_InterferingWorkload
                                                                                Job
                                                                                inst_3)
  (intra_IBF : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) =>
Prosa_Analysis_Abstract_Definitions_cond_interference_is_bounded_by Job
  inst_3
  inst_27
  inst_30
  inst_14
  inst_17 PState arr_seq sched Task
  inst_7
  inst_10 tsk intra_IBF
  (Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A Job
     inst_3
     inst_14
     inst_17 PState sched
     inst_27
     inst_30)
  (fun (_ : Job) (t : Prosa_Behavior_Time_instant) =>
   Prosa_Model_Processor_Supply_has_supply Job
     inst_3 PState sched t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Task ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp

Arguments Prosa_Analysis_Abstract_IBF_Supply_intra_interference_is_bounded_by Job
  inst_3 Task
  inst_7
  inst_10
  inst_14
  inst_17 PState 
  arr_seq sched tsk inst_27
  inst_30 intra_IBF%_function_scope
```
