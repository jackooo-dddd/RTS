# `longest_busy_interval_with_pi`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.busy_interval.edf_pi_bound.longest_busy_interval_with_pi`
- Lean: `Prosa.Analysis.Definitions.BusyInterval.EdfPiBound.longest_busy_interval_with_pi`
- Certificate: `longest_busy_interval_with_pi_correspondence`

## Official Rocq

```coq
longest_busy_interval_with_pi :
forall {Task : TaskType},
TaskCost Task ->
TaskDeadline Task ->
TaskMaxNonpreemptiveSegment Task -> MaxArrivals Task -> seq (Equality.sort Task) -> Equality.sort Task -> nat

longest_busy_interval_with_pi is not universe polymorphic
Arguments longest_busy_interval_with_pi {Task H H0 H1 H2} ts%seq_scope tsk
longest_busy_interval_with_pi is transparent
Expands to: Constant prosa.analysis.definitions.busy_interval.edf_pi_bound.longest_busy_interval_with_pi
Declared in library prosa.analysis.definitions.busy_interval.edf_pi_bound, line 42, characters 13-42
@longest_busy_interval_with_pi
     : forall Task : TaskType,
       TaskCost Task ->
       TaskDeadline Task ->
       TaskMaxNonpreemptiveSegment Task ->
       MaxArrivals Task -> seq (Equality.sort Task) -> Equality.sort Task -> nat
```

Body:

```coq
longest_busy_interval_with_pi =
fun (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : TaskMaxNonpreemptiveSegment Task)
  (H2 : MaxArrivals Task) =>
let D := [eta @task_deadline Task H0] in
fun (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) =>
let lp_interference := fun tsk_lp : Equality.sort Task => @task_max_nonpreemptive_segment Task H1 tsk_lp - 1
  in
let hep_interference :=
  fun tsk_lp : Equality.sort Task =>
  \sum_(tsk_hp <- ts | D tsk_hp <= D tsk_lp)
     @task_request_bound_function Task H H2 tsk_hp (D tsk_lp - D tsk_hp)
  in
\max_(tsk_lp <- ts | D tsk < D tsk_lp) (lp_interference tsk_lp + hep_interference tsk_lp)
     : forall {Task : TaskType},
       TaskCost Task ->
       TaskDeadline Task ->
       TaskMaxNonpreemptiveSegment Task ->
       MaxArrivals Task -> seq (Equality.sort Task) -> Equality.sort Task -> nat

Arguments longest_busy_interval_with_pi {Task H H0 H1 H2} ts%seq_scope tsk
```

## Lean

```lean
@Prosa.Analysis.Definitions.BusyInterval.EdfPiBound.longest_busy_interval_with_pi : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
          [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → List Task → Task → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.BusyInterval.EdfPiBound.longest_busy_interval_with_pi.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Concept.TaskDeadline Task] →
        [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
          [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → List Task → Task → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] [Prosa.Model.Task.Concept.TaskDeadline Task]
    [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts tsk =>
  have lp_interference := fun tsk_lp =>
    Prosa.Model.Task.Preemption.Parameters.task_max_nonpreemptive_segment tsk_lp - 1;
  have hep_interference := fun tsk_lp =>
    Prosa.Util.Sum.sumFiltered ts
      (fun tsk_hp =>
        decide (Prosa.Model.Task.Concept.task_deadline tsk_hp ≤ Prosa.Model.Task.Concept.task_deadline tsk_lp))
      fun tsk_hp =>
      Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk_hp
        (Prosa.Model.Task.Concept.task_deadline tsk_lp - Prosa.Model.Task.Concept.task_deadline tsk_hp);
  Prosa.Util.Minmax.bigMaxListCond ts
    (fun tsk_lp => decide (Prosa.Model.Task.Concept.task_deadline tsk < Prosa.Model.Task.Concept.task_deadline tsk_lp))
    fun tsk_lp => lp_interference tsk_lp + hep_interference tsk_lp
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_BusyInterval_EdfPiBound_longest_busy_interval_with_pi
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task -> Task -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_BusyInterval_EdfPiBound_longest_busy_interval_with_pi@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
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
  (inst_15 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task) (tsk : Task) =>
let lp_interference :=
  fun tsk_lp : Task =>
  HSub_hSub_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
    (instHSub_inst1 Prosa_Behavior_Job_work instSubNat)
    (Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment Task
       inst_3
       inst_12 tsk_lp)
    (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
  in
let hep_interference :=
  fun tsk_lp : Task =>
  Prosa_Util_Sum_sumFiltered Task ts
    (fun tsk_hp : Task =>
     Decidable_decide
       (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
          (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
             inst_3
             inst_9 tsk_hp)
          (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
             inst_3
             inst_9 tsk_lp))
       (Nat_decLe
          (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
             inst_3
             inst_9 tsk_hp)
          (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
             inst_3
             inst_9 tsk_lp)))
    (fun tsk_hp : Task =>
     Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
       inst_3
       inst_6
       inst_15 tsk_hp
       (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
          Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
          (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
             inst_3
             inst_9 tsk_lp)
          (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
             inst_3
             inst_9 tsk_hp)))
  in
Prosa_Util_Minmax_bigMaxListCond Task ts
  (fun tsk_lp : Task =>
   Decidable_decide
     (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
        (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
           inst_3
           inst_9 tsk)
        (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
           inst_3
           inst_9 tsk_lp))
     (Nat_decLt
        (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
           inst_3
           inst_9 tsk)
        (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
           inst_3
           inst_9 tsk_lp)))
  (fun tsk_lp : Task =>
   HAdd_hAdd_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
     (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat) (lp_interference tsk_lp) 
     (hep_interference tsk_lp))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task -> Task -> Nat

Arguments Prosa_Analysis_Definitions_BusyInterval_EdfPiBound_longest_busy_interval_with_pi 
  Task inst_3
  inst_6
  inst_9
  inst_12
  inst_15 
  ts tsk
```
