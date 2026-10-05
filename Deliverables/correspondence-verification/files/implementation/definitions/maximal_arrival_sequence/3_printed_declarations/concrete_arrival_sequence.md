# `concrete_arrival_sequence`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.maximal_arrival_sequence.concrete_arrival_sequence`
- Lean: `Prosa.Implementation.Definitions.MaximalArrivalSequence.concrete_arrival_sequence`
- Certificate: `concrete_arrival_sequence_correspondence`

## Official Rocq

```coq
concrete_arrival_sequence :
forall {Task : TaskType} {Job : JobType},
MaxArrivals Task ->
(Equality.sort Task -> nat -> instant -> seq (Equality.sort Job)) ->
seq (Equality.sort Task) -> instant -> seq (Equality.sort Job)

concrete_arrival_sequence is not universe polymorphic
Arguments concrete_arrival_sequence {Task Job H3} generate_jobs_at%function_scope ts%seq_scope t
concrete_arrival_sequence is transparent
Expands to: Constant prosa.implementation.definitions.maximal_arrival_sequence.concrete_arrival_sequence
Declared in library prosa.implementation.definitions.maximal_arrival_sequence, line 85, characters 13-38
@concrete_arrival_sequence
     : forall (Task : TaskType) (Job : JobType),
       MaxArrivals Task ->
       (Equality.sort Task -> nat -> instant -> seq (Equality.sort Job)) ->
       seq (Equality.sort Task) -> instant -> seq (Equality.sort Job)
```

Body:

```coq
concrete_arrival_sequence =
fun (Task : TaskType) (Job : JobType) (H3 : MaxArrivals Task)
  (generate_jobs_at : Equality.sort Task -> nat -> instant -> seq (Equality.sort Job))
  (ts : seq (Equality.sort Task)) (t : instant) =>
\cat_(tsk<-ts)generate_jobs_at tsk (@max_arrivals_at Task H3 tsk t) t
     : forall {Task : TaskType} {Job : JobType},
       MaxArrivals Task ->
       (Equality.sort Task -> nat -> instant -> seq (Equality.sort Job)) ->
       seq (Equality.sort Task) -> instant -> seq (Equality.sort Job)

Arguments concrete_arrival_sequence {Task Job H3} generate_jobs_at%function_scope ts%seq_scope t
```

## Lean

```lean
@Prosa.Implementation.Definitions.MaximalArrivalSequence.concrete_arrival_sequence : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [DecidableEq Job] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          (Task → ℕ → Prosa.Behavior.Time.instant → List Job) → List Task → Prosa.Behavior.Time.instant → List Job
def Prosa.Implementation.Definitions.MaximalArrivalSequence.concrete_arrival_sequence.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [DecidableEq Job] →
        [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
          (Task → ℕ → Prosa.Behavior.Time.instant → List Job) → List Task → Prosa.Behavior.Time.instant → List Job :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
    generate_jobs_at ts t =>
  Prosa.Util.Bigcat.bigCatSeqAll ts fun tsk =>
    generate_jobs_at tsk (Prosa.Implementation.Definitions.MaximalArrivalSequence.max_arrivals_at tsk t) t
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType),
       DecidableEq Job ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       (Task -> Nat -> Prosa_Behavior_Time_instant -> List Job) ->
       List Task -> Prosa_Behavior_Time_instant -> List Job
```

Body:

```coq
Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.max__u_1+2_u_2+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : 
   DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType) (_ : DecidableEq Job)
  (inst_10 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (generate_jobs_at : Task -> Nat -> Prosa_Behavior_Time_instant -> List Job) (ts : List Task)
  (t : Prosa_Behavior_Time_instant) =>
Prosa_Util_Bigcat_bigCatSeqAll Task Job ts
  (fun tsk : Task =>
   generate_jobs_at tsk
     (Prosa_Implementation_Definitions_MaximalArrivalSequence_max_arrivals_at Task
        inst_3
        inst_10 tsk t)
     t)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType),
       DecidableEq Job ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       (Task -> Nat -> Prosa_Behavior_Time_instant -> List Job) ->
       List Task -> Prosa_Behavior_Time_instant -> List Job

Arguments Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence 
  Task inst_3 
  Job inst_7
  inst_10
  generate_jobs_at%_function_scope ts a____at____internal__hyg0
```
