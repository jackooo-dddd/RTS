# `multiprocessor_state`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.multiprocessor.multiprocessor_state`
- Lean: `Prosa.Model.Processor.Multiprocessor.multiprocessor_state`
- Certificate: `multiprocessor_state_source_total, multiprocessor_state_target_total`

## Official Rocq

```coq
multiprocessor_state : forall Job : JobType, ProcessorState Job -> nat -> Type

multiprocessor_state is not universe polymorphic
Arguments multiprocessor_state Job processor_state num_cpus%nat_scope
multiprocessor_state is transparent
Expands to: Constant prosa.model.processor.multiprocessor.multiprocessor_state
Declared in library prosa.model.processor.multiprocessor, line 41, characters 13-33
multiprocessor_state
     : forall Job : JobType, ProcessorState Job -> nat -> Type
```

Body:

```coq
multiprocessor_state =
fun (Job : JobType) (processor_state : ProcessorState Job) (num_cpus : nat) =>
processor num_cpus -> @State Job processor_state
     : forall Job : JobType, ProcessorState Job -> nat -> Type

Arguments multiprocessor_state Job processor_state num_cpus%nat_scope
```

## Lean

```lean
Prosa.Model.Processor.Multiprocessor.multiprocessor_state : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → ℕ → Type u_2
```

Body:

```lean
@[reducible] def Prosa.Model.Processor.Multiprocessor.multiprocessor_state.{u_1, u_2, u_3} : (Job :
    Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job → ℕ → Type u_2 :=
fun Job [DecidableEq Job] processor_state num_cpus =>
  Prosa.Model.Processor.Multiprocessor.processor num_cpus → Prosa.Behavior.Schedule.ProcessorState.State Job
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Multiprocessor_multiprocessor_state
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       Nat -> Type
```

Body:

```coq
Prosa_Model_Processor_Multiprocessor_multiprocessor_state@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (processor_state : Prosa_Behavior_Schedule_ProcessorState Job
                       inst_3)
  (num_cpus : Nat) =>
Prosa_Model_Processor_Multiprocessor_processor num_cpus ->
Prosa_Behavior_Schedule_ProcessorState_State Job
  inst_3 processor_state
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState Job
         inst_3 ->
       Nat -> Type

Arguments Prosa_Model_Processor_Multiprocessor_multiprocessor_state Job
  inst_3 processor_state
  num_cpus%_Nat_scope
```
