# `arrivals_have_valid_min_job_costs`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.concept.arrivals_have_valid_min_job_costs`
- Lean: `Prosa.Model.Task.Concept.arrivals_have_valid_min_job_costs`
- Certificate: ``

## Official Rocq

```coq
arrivals_have_valid_min_job_costs :
forall {Task : TaskType},
TaskMinCost Task -> forall {Job : JobType}, JobTask Job Task -> JobCost Job -> arrival_sequence Job -> Prop

arrivals_have_valid_min_job_costs is not universe polymorphic
Arguments arrivals_have_valid_min_job_costs {Task H0 Job H2 H3} arr_seq
arrivals_have_valid_min_job_costs is transparent
Expands to: Constant prosa.model.task.concept.arrivals_have_valid_min_job_costs
Declared in library prosa.model.task.concept, line 114, characters 15-48
@arrivals_have_valid_min_job_costs
     : forall Task : TaskType,
       TaskMinCost Task ->
       forall Job : JobType, JobTask Job Task -> JobCost Job -> arrival_sequence Job -> Prop
```

Body:

```coq
arrivals_have_valid_min_job_costs =
fun (Task : TaskType) (H0 : TaskMinCost Task) (Job : JobType) (H2 : JobTask Job Task) 
  (H3 : JobCost Job) (arr_seq : arrival_sequence Job) =>
forall j : Equality.sort Job, @arrives_in Job arr_seq j -> is_true (@valid_min_job_cost Task H0 Job H2 H3 j)
     : forall {Task : TaskType},
       TaskMinCost Task ->
       forall {Job : JobType}, JobTask Job Task -> JobCost Job -> arrival_sequence Job -> Prop

Arguments arrivals_have_valid_min_job_costs {Task H0 Job H2 H3} arr_seq
```

## Lean

```lean
@Prosa.Model.Task.Concept.arrivals_have_valid_min_job_costs : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskMinCost Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobCost Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
def Prosa.Model.Task.Concept.arrivals_have_valid_min_job_costs.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskMinCost Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobCost Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskMinCost Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobCost Job] arrSeq =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arrSeq j → Prosa.Model.Task.Concept.valid_min_job_cost j = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_arrivals_have_valid_min_job_costs
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskMinCost Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_16 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_16
         Task inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_16 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_16 ->
       SProp
```

Body:

```coq
Prosa_Model_Task_Concept_arrivals_have_valid_min_job_costs@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_9 : Prosa_Model_Task_Concept_TaskMinCost Task
                                                                     inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_16 : DecidableEq Job)
  (inst_19 : Prosa_Model_Task_Concept_JobTask Job
                                                                      inst_16
                                                                      Task
                                                                      inst_3)
  (inst_23 : Prosa_Behavior_Job_JobCost Job
                                                                      inst_16)
  (arrSeq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
              inst_16) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job inst_16
  arrSeq j ->
@eq Bool
  (Prosa_Model_Task_Concept_valid_min_job_cost Task
     inst_3
     inst_9 Job
     inst_16
     inst_19
     inst_23 j)
  Bool_true
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskMinCost Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_16 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_16
         Task inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_16 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_16 ->
       SProp

Arguments Prosa_Model_Task_Concept_arrivals_have_valid_min_job_costs Task
  inst_3
  inst_9 Job
  inst_16
  inst_19
  inst_23 arrSeq
```
