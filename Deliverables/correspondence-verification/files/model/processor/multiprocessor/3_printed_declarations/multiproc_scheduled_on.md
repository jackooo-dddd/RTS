# `multiproc_scheduled_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.multiprocessor.multiproc_scheduled_on`
- Lean: `Prosa.Model.Processor.Multiprocessor.multiproc_scheduled_on`
- Certificate: `multiproc_scheduled_on_correspondence`

## Official Rocq

```coq
multiproc_scheduled_on :
forall (Job : JobType) (processor_state : ProcessorState Job) (num_cpus : nat),
Equality.sort Job -> multiprocessor_state Job processor_state num_cpus -> processor num_cpus -> bool

multiproc_scheduled_on is not universe polymorphic
Arguments multiproc_scheduled_on Job processor_state num_cpus%nat_scope j mps cpu
multiproc_scheduled_on is transparent
Expands to: Constant prosa.model.processor.multiprocessor.multiproc_scheduled_on
Declared in library prosa.model.processor.multiprocessor, line 47, characters 13-35
multiproc_scheduled_on
     : forall (Job : JobType) (processor_state : ProcessorState Job) (num_cpus : nat),
       Equality.sort Job -> multiprocessor_state Job processor_state num_cpus -> processor num_cpus -> bool
```

Body:

```coq
multiproc_scheduled_on =
fun (Job : JobType) (processor_state : ProcessorState Job) (num_cpus : nat) (j : Equality.sort Job)
  (mps : multiprocessor_state Job processor_state num_cpus) (cpu : processor num_cpus) =>
@scheduled_in Job processor_state j (mps cpu)
     : forall (Job : JobType) (processor_state : ProcessorState Job) (num_cpus : nat),
       Equality.sort Job -> multiprocessor_state Job processor_state num_cpus -> processor num_cpus -> bool

Arguments multiproc_scheduled_on Job processor_state num_cpus%nat_scope j mps cpu
```

## Lean

```lean
Prosa.Model.Processor.Multiprocessor.multiproc_scheduled_on : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] →
    (processor_state : Prosa.Behavior.Schedule.ProcessorState Job) →
      (num_cpus : ℕ) →
        Job →
          Prosa.Model.Processor.Multiprocessor.multiprocessor_state Job processor_state num_cpus →
            Prosa.Model.Processor.Multiprocessor.processor num_cpus → Bool
```

Body:

```lean
def Prosa.Model.Processor.Multiprocessor.multiproc_scheduled_on.{u_1, u_2, u_3} : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] →
    (processor_state : Prosa.Behavior.Schedule.ProcessorState Job) →
      (num_cpus : ℕ) →
        Job →
          Prosa.Model.Processor.Multiprocessor.multiprocessor_state Job processor_state num_cpus →
            Prosa.Model.Processor.Multiprocessor.processor num_cpus → Bool :=
fun Job [DecidableEq Job] processor_state num_cpus j mps cpu => processor_state.scheduled_in j (mps cpu)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Multiprocessor_multiproc_scheduled_on
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (processor_state : Prosa_Behavior_Schedule_ProcessorState Job
                              inst_3)
         (num_cpus : Nat),
       Job ->
       Prosa_Model_Processor_Multiprocessor_multiprocessor_state Job
         inst_3 processor_state num_cpus ->
       Prosa_Model_Processor_Multiprocessor_processor num_cpus -> Bool
```

Body:

```coq
Prosa_Model_Processor_Multiprocessor_multiproc_scheduled_on@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (processor_state : Prosa_Behavior_Schedule_ProcessorState Job
                       inst_3)
  (num_cpus : Nat) (j : Job)
  (mps : Prosa_Model_Processor_Multiprocessor_multiprocessor_state Job
           inst_3 processor_state num_cpus)
  (cpu : Prosa_Model_Processor_Multiprocessor_processor num_cpus) =>
Prosa_Behavior_Schedule_ProcessorState_scheduled_in Job
  inst_3 processor_state j 
  (mps cpu)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (processor_state : Prosa_Behavior_Schedule_ProcessorState Job
                              inst_3)
         (num_cpus : Nat),
       Job ->
       Prosa_Model_Processor_Multiprocessor_multiprocessor_state Job
         inst_3 processor_state num_cpus ->
       Prosa_Model_Processor_Multiprocessor_processor num_cpus -> Bool

Arguments Prosa_Model_Processor_Multiprocessor_multiproc_scheduled_on Job
  inst_3 processor_state
  num_cpus%_Nat_scope j mps cpu
```
