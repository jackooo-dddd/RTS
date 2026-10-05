# `blocking_bound`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.blocking_bound.fp.blocking_bound`
- Lean: `Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound`
- Certificate: `blocking_bound_correspondence`

## Official Rocq

```coq
blocking_bound :
forall {Task : TaskType},
TaskMaxNonpreemptiveSegment Task -> FP_policy Task -> seq (Equality.sort Task) -> Equality.sort Task -> nat

blocking_bound is not universe polymorphic
Arguments blocking_bound {Task H FP} ts%seq_scope tsk
blocking_bound is transparent
Expands to: Constant prosa.analysis.definitions.blocking_bound.fp.blocking_bound
Declared in library prosa.analysis.definitions.blocking_bound.fp, line 22, characters 13-27
@blocking_bound
     : forall Task : TaskType,
       TaskMaxNonpreemptiveSegment Task ->
       FP_policy Task -> seq (Equality.sort Task) -> Equality.sort Task -> nat
```

Body:

```coq
blocking_bound =
fun (Task : TaskType) (H : TaskMaxNonpreemptiveSegment Task) (FP : FP_policy Task)
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) =>
\max_(tsk_other <- ts | ~~ @hep_task Task FP tsk_other tsk)
   (@task_max_nonpreemptive_segment Task H tsk_other - 1)
     : forall {Task : TaskType},
       TaskMaxNonpreemptiveSegment Task ->
       FP_policy Task -> seq (Equality.sort Task) -> Equality.sort Task -> nat

Arguments blocking_bound {Task H FP} ts%seq_scope tsk
```

## Lean

```lean
@Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
      [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → List Task → Task → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
      [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → List Task → Task → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
    [Prosa.Model.Priority.Definitions.FP_policy Task] ts tsk =>
  Prosa.Util.Minmax.bigMaxListCond ts (fun tsk_other => !Prosa.Model.Priority.Definitions.hep_task tsk_other tsk)
    fun tsk_other => Prosa.Model.Task.Preemption.Parameters.task_max_nonpreemptive_segment tsk_other - 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       List Task -> Task -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
     inst_3)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (ts : List Task) (tsk : Task) =>
Prosa_Util_Minmax_bigMaxListCond Task ts
  (fun tsk_other : Task =>
   Bool_not
     (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
        inst_3 FP tsk_other tsk))
  (fun tsk_other : Task =>
   HSub_hSub_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
     (instHSub_inst1 Prosa_Behavior_Job_work instSubNat)
     (Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment_task_max_nonpreemptive_segment Task
        inst_3
        inst_6 tsk_other)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       List Task -> Task -> Nat

Arguments Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound Task
  inst_3
  inst_6 
  FP ts tsk
```
