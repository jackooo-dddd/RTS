# `blocking_bound`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.blocking_bound.edf.blocking_bound`
- Lean: `Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_bound`
- Certificate: `blocking_bound_correspondence`

## Official Rocq

```coq
blocking_bound :
forall {Task : TaskType},
TaskCost Task ->
TaskDeadline Task ->
TaskMaxNonpreemptiveSegment Task ->
seq (Equality.sort Task) -> MaxArrivals Task -> Equality.sort Task -> duration -> nat

blocking_bound is not universe polymorphic
Arguments blocking_bound {Task H H0 H1} ts%seq_scope {H2} tsk A
blocking_bound is transparent
Expands to: Constant prosa.analysis.definitions.blocking_bound.edf.blocking_bound
Declared in library prosa.analysis.definitions.blocking_bound.edf, line 36, characters 13-27
@blocking_bound
     : forall Task : TaskType,
       TaskCost Task ->
       TaskDeadline Task ->
       TaskMaxNonpreemptiveSegment Task ->
       seq (Equality.sort Task) -> MaxArrivals Task -> Equality.sort Task -> duration -> nat
```

Body:

```coq
blocking_bound =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : TaskMaxNonpreemptiveSegment Task) =>
let D := [eta @task_deadline Task H0] in
fun (ts : seq (Equality.sort Task)) (H2 : MaxArrivals Task) (tsk : Equality.sort Task) (A : duration) =>
\max_(tsk_o <- ts | @blocking_relevant Task H H2 tsk_o && (D tsk + A < D tsk_o))
   (@task_max_nonpreemptive_segment Task H1 tsk_o - 1)
     : forall {Task : TaskType},
       TaskCost Task ->
       TaskDeadline Task ->
       TaskMaxNonpreemptiveSegment Task ->
       seq (Equality.sort Task) -> MaxArrivals Task -> Equality.sort Task -> duration -> nat

Arguments blocking_bound {Task H H0 H1} ts%seq_scope {H2} tsk A
```

## Lean

```lean
@Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_bound : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
          List Task → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_bound.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
          List Task → [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Task → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task]
    [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] ts
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] tsk A =>
  Prosa.Util.Minmax.bigMaxListCond ts
    (fun tsk_o =>
      Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_relevant tsk_o &&
        decide (Prosa.Model.Task.Concept.task_deadline tsk + A < Prosa.Model.Task.Concept.task_deadline tsk_o))
    fun tsk_o => Prosa.Model.Task.Preemption.Parameters.task_max_nonpreemptive_segment tsk_o - 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       List Task ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Concept_TaskDeadline Task
     inst_3)
  (inst_12 : 
   Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
     inst_3)
  (ts : List Task)
  (inst_17 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (tsk : Task) (A : Prosa_Behavior_Time_duration) =>
Prosa_Util_Minmax_bigMaxListCond Task ts
  (fun tsk_o : Task =>
   Bool_and
     (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_relevant Task
        inst_3
        inst_6
        inst_17 tsk_o)
     (Decidable_decide
        (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
              Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
              (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                 inst_3
                 inst_9 tsk)
              A)
           (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
              inst_3
              inst_9 tsk_o))
        (Nat_decLt
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
              Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
              (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                 inst_3
                 inst_9 tsk)
              A)
           (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
              inst_3
              inst_9 tsk_o))))
  (fun tsk_o : Task =>
   HSub_hSub_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
     (instHSub_inst1 Prosa_Behavior_Job_work instSubNat)
     (Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment Task
        inst_3
        inst_12 tsk_o)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       List Task ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
  inst_3
  inst_6
  inst_9
  inst_12 
  ts inst_17 
  tsk a____at____internal__hyg0
```
