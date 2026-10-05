# `sbf_respected_in_busy_interval`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.restricted_supply.busy_sbf.sbf_respected_in_busy_interval`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.BusySbf.sbf_respected_in_busy_interval`
- Certificate: `sbf_respected_in_busy_interval_correspondence`

## Official Rocq

```coq
sbf_respected_in_busy_interval :
forall {Task : TaskType} {Job : JobType},
JobArrival Job ->
JobCost Job ->
JobTask Job Task ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState ->
Equality.sort Task -> Interference Job -> InterferingWorkload Job -> (duration -> work) -> Prop

sbf_respected_in_busy_interval is not universe polymorphic
Arguments sbf_respected_in_busy_interval {Task Job H H0 H1 PState} arr_seq sched 
  tsk {H2 H3} SBF%function_scope
sbf_respected_in_busy_interval is transparent
Expands to: Constant prosa.analysis.abstract.restricted_supply.busy_sbf.sbf_respected_in_busy_interval
Declared in library prosa.analysis.abstract.restricted_supply.busy_sbf, line 47, characters 13-43
@sbf_respected_in_busy_interval
     : forall (Task : TaskType) (Job : JobType),
       JobArrival Job ->
       JobCost Job ->
       JobTask Job Task ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState ->
       Equality.sort Task -> Interference Job -> InterferingWorkload Job -> (duration -> work) -> Prop
```

Body:

```coq
sbf_respected_in_busy_interval =
fun (Task : TaskType) (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobTask Job Task)
  (PState : ProcessorState Job) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  (tsk : Equality.sort Task) (H2 : Interference Job) (H3 : InterferingWorkload Job) =>
let bi_prefix_of_tsk :=
  fun (j : Equality.sort Job) (t1 t2 : instant) =>
  is_true (@job_of_task Job Task H1 tsk j) /\ @busy_interval_prefix Job H H0 PState sched H2 H3 j t1 t2 in
     : forall {Task : TaskType} {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       JobTask Job Task ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       Equality.sort Task -> Interference Job -> InterferingWorkload Job -> (duration -> work) -> Prop

Arguments sbf_respected_in_busy_interval {Task Job H H0 H1 PState} arr_seq sched 
  tsk {H2 H3} SBF%function_scope
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.BusySbf.sbf_respected_in_busy_interval : {Task :
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
                    Task →
                      [Prosa.Analysis.Abstract.Definitions.Interference Job] →
                        [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
                          (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop
def Prosa.Analysis.Abstract.RestrictedSupply.BusySbf.sbf_respected_in_busy_interval.{u_1, u_2, u_3, u_4} : {Task :
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
                    Task →
                      [Prosa.Analysis.Abstract.Definitions.Interference Job] →
                        [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
                          (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Task.Concept.JobTask Job Task] {PState} arr_seq sched tsk
    [Prosa.Analysis.Abstract.Definitions.Interference Job] [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
    SBF =>
  Prosa.Analysis.Definitions.Sbf.Pred.pred_sbf_respected arr_seq sched
    (fun j t1 t2 =>
      Prosa.Model.Task.Concept.job_of_task tsk j = true ∧
        Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2)
    SBF
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_BusySbf_sbf_respected_in_busy_interval
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job),
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
       Task ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_7 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_7 ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp
```

Body:

```coq
Prosa_Analysis_Abstract_RestrictedSupply_BusySbf_sbf_respected_in_busy_interval@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0
Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_7)
  (inst_13 : 
   Prosa_Behavior_Job_JobCost Job
     inst_7)
  (inst_16 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7 Task
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7 PState)
  (tsk : Task)
  (inst_27 : 
   Prosa_Analysis_Abstract_Definitions_Interference Job
     inst_7)
  (inst_30 : 
   Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
     inst_7)
  (SBF : Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) =>
Prosa_Analysis_Definitions_Sbf_Pred_pred_sbf_respected Job
  inst_7 PState arr_seq sched
  (fun (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
   And
     (@eq Bool
        (Prosa_Model_Task_Concept_job_of_task Job
           inst_7 Task
           inst_3
           inst_16 tsk j)
        Bool_true)
     (Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
        inst_7
        inst_27
        inst_30
        inst_10
        inst_13 PState sched j
        t1 t2))
  SBF
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job),
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
       Task ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_7 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_7 ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp

Arguments Prosa_Analysis_Abstract_RestrictedSupply_BusySbf_sbf_respected_in_busy_interval 
  Task inst_3 
  Job inst_7
  inst_10
  inst_13
  inst_16 
  PState arr_seq sched tsk
  inst_27
  inst_30 
  SBF%_function_scope
```
