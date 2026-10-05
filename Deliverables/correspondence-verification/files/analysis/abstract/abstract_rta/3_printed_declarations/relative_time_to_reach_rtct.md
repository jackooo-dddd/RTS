# `relative_time_to_reach_rtct`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.abstract_rta.relative_time_to_reach_rtct`
- Lean: `Prosa.Analysis.Abstract.AbstractRta.relative_time_to_reach_rtct`
- Certificate: `relative_time_to_reach_rtct_correspondence`

## Official Rocq

```coq
relative_time_to_reach_rtct :
forall {Task : TaskType},
TaskRunToCompletionThreshold Task ->
forall {Job : JobType},
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
@schedule Job PState ->
Equality.sort Task ->
Interference Job ->
InterferingWorkload Job -> (duration -> duration -> duration) -> Equality.sort Job -> duration -> Prop

relative_time_to_reach_rtct is not universe polymorphic
Arguments relative_time_to_reach_rtct {Task H0 Job H2 jc PState} sched tsk {H3 H4} IBF_P%function_scope j F
relative_time_to_reach_rtct is transparent
Expands to: Constant prosa.analysis.abstract.abstract_rta.relative_time_to_reach_rtct
Declared in library prosa.analysis.abstract.abstract_rta, line 141, characters 13-40
@relative_time_to_reach_rtct
     : forall Task : TaskType,
       TaskRunToCompletionThreshold Task ->
       forall Job : JobType,
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       @schedule Job PState ->
       Equality.sort Task ->
       Interference Job ->
       InterferingWorkload Job -> (duration -> duration -> duration) -> Equality.sort Job -> duration -> Prop
```

Body:

```coq
relative_time_to_reach_rtct =
fun (Task : TaskType) (H0 : TaskRunToCompletionThreshold Task) (Job : JobType) (H2 : JobArrival Job)
  (jc : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (tsk : Equality.sort Task) (H3 : Interference Job) (H4 : InterferingWorkload Job)
  (IBF_P : duration -> duration -> duration) (j : Equality.sort Job) (F : duration) =>
forall t1 t2 : instant,
@busy_interval Job H2 jc PState sched H3 H4 j t1 t2 ->
is_true (@task_rtct Task H0 tsk + IBF_P (@job_arrival Job H2 j - t1) F <= F) /\
is_true (@task_rtct Task H0 tsk <= @service Job PState sched j (t1 + F))
     : forall {Task : TaskType},
       TaskRunToCompletionThreshold Task ->
       forall {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       @schedule Job PState ->
       Equality.sort Task ->
       Interference Job ->
       InterferingWorkload Job -> (duration -> duration -> duration) -> Equality.sort Job -> duration -> Prop

Arguments relative_time_to_reach_rtct {Task H0 Job H2 jc PState} sched tsk {H3 H4} IBF_P%function_scope j F
```

## Lean

```lean
@Prosa.Analysis.Abstract.AbstractRta.relative_time_to_reach_rtct : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst : DecidableEq Job] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Schedule.schedule PState →
                  Task →
                    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
                      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
                        (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
                          Job → Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Analysis.Abstract.AbstractRta.relative_time_to_reach_rtct.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst : DecidableEq Job] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Schedule.schedule PState →
                  Task →
                    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
                      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
                        (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
                          Job → Prosa.Behavior.Time.duration → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] {Job}
    [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} sched tsk
    [Prosa.Analysis.Abstract.Definitions.Interference Job] [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
    IBF_P j F =>
  ∀ (t1 t2 : Prosa.Behavior.Time.instant),
    Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
      Prosa.Model.Task.Preemption.Parameters.task_rtct tsk + IBF_P (Prosa.Behavior.Job.job_arrival j - t1) F ≤ F ∧
        Prosa.Model.Task.Preemption.Parameters.task_rtct tsk ≤ Prosa.Behavior.Service.service sched j (t1 + F)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_AbstractRta_relative_time_to_reach_rtct
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_10 ->
       Prosa_Behavior_Job_JobCost Job
         inst_10 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_10,
       Prosa_Behavior_Schedule_schedule Job
         inst_10 PState ->
       Task ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_10 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_10 ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       Job -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Analysis_Abstract_AbstractRta_relative_time_to_reach_rtct@{u_1 u_2 u_3 u_4 Lean.u_1+1.0 Lean.u_2+1.0
Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0 Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold
                                                                                Task
                                                                                inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_10)
  (inst_16 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_10)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_10)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_10 PState)
  (tsk : Task)
  (inst_24 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                                Job
                                                                                inst_10)
  (inst_27 : Prosa_Analysis_Abstract_Definitions_InterferingWorkload
                                                                                Job
                                                                                inst_10)
  (IBF_P : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
  (j : Job) (F : Prosa_Behavior_Time_duration) =>
forall t1 t2 : Prosa_Behavior_Time_instant,
Prosa_Analysis_Abstract_Definitions_busy_interval Job
  inst_10
  inst_24
  inst_27
  inst_13
  inst_16 PState sched j t1 t2 ->
And
  (LE_le_inst1 Prosa_Behavior_Job_work instLENat
     (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
        (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
        (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
           inst_3
           inst_6 tsk)
        (IBF_P
           (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
              Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                 inst_10
                 inst_13 j)
              t1)
           F))
     F)
  (LE_le_inst1 Prosa_Behavior_Job_work instLENat
     (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
        inst_3
        inst_6 tsk)
     (Prosa_Behavior_Service_service Job
        inst_10 PState sched j
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 F)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_10 ->
       Prosa_Behavior_Job_JobCost Job
         inst_10 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_10,
       Prosa_Behavior_Schedule_schedule Job
         inst_10 PState ->
       Task ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_10 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_10 ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       Job -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Analysis_Abstract_AbstractRta_relative_time_to_reach_rtct Task
  inst_3
  inst_6 Job
  inst_10
  inst_13
  inst_16 PState 
  sched tsk inst_24
  inst_27 IBF_P%_function_scope 
  j L
```
