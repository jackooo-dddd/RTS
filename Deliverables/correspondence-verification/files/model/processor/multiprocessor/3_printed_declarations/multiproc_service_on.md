# `multiproc_service_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.multiprocessor.multiproc_service_on`
- Lean: `Prosa.Model.Processor.Multiprocessor.multiproc_service_on`
- Certificate: `multiproc_service_on_correspondence`

## Official Rocq

```coq
multiproc_service_on :
forall (Job : JobType) (processor_state : ProcessorState Job) (num_cpus : nat),
Equality.sort Job -> multiprocessor_state Job processor_state num_cpus -> processor num_cpus -> work

multiproc_service_on is not universe polymorphic
Arguments multiproc_service_on Job processor_state num_cpus%nat_scope j mps cpu
multiproc_service_on is transparent
Expands to: Constant prosa.model.processor.multiprocessor.multiproc_service_on
Declared in library prosa.model.processor.multiprocessor, line 62, characters 13-33
multiproc_service_on
     : forall (Job : JobType) (processor_state : ProcessorState Job) (num_cpus : nat),
       Equality.sort Job -> multiprocessor_state Job processor_state num_cpus -> processor num_cpus -> work
```

Body:

```coq
multiproc_service_on =
fun (Job : JobType) (processor_state : ProcessorState Job) (num_cpus : nat) (j : Equality.sort Job)
  (mps : multiprocessor_state Job processor_state num_cpus) (cpu : processor num_cpus) =>
@service_in Job processor_state j (mps cpu)
     : forall (Job : JobType) (processor_state : ProcessorState Job) (num_cpus : nat),
       Equality.sort Job -> multiprocessor_state Job processor_state num_cpus -> processor num_cpus -> work

Arguments multiproc_service_on Job processor_state num_cpus%nat_scope j mps cpu
```

## Lean

```lean
Prosa.Model.Processor.Multiprocessor.multiproc_service_on : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] →
    (processor_state : Prosa.Behavior.Schedule.ProcessorState Job) →
      (num_cpus : ℕ) →
        Job →
          Prosa.Model.Processor.Multiprocessor.multiprocessor_state Job processor_state num_cpus →
            Prosa.Model.Processor.Multiprocessor.processor num_cpus → Prosa.Behavior.Job.work
```

Body:

```lean
def Prosa.Model.Processor.Multiprocessor.multiproc_service_on.{u_1, u_2, u_3} : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] →
    (processor_state : Prosa.Behavior.Schedule.ProcessorState Job) →
      (num_cpus : ℕ) →
        Job →
          Prosa.Model.Processor.Multiprocessor.multiprocessor_state Job processor_state num_cpus →
            Prosa.Model.Processor.Multiprocessor.processor num_cpus → Prosa.Behavior.Job.work :=
fun Job [DecidableEq Job] processor_state num_cpus j mps cpu => processor_state.service_in j (mps cpu)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Multiprocessor_multiproc_service_on
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (processor_state : Prosa_Behavior_Schedule_ProcessorState Job
                              inst_3)
         (num_cpus : Nat),
       Job ->
       Prosa_Model_Processor_Multiprocessor_multiprocessor_state Job
         inst_3 processor_state num_cpus ->
       Prosa_Model_Processor_Multiprocessor_processor num_cpus -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Model_Processor_Multiprocessor_multiproc_service_on@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (processor_state : Prosa_Behavior_Schedule_ProcessorState Job
                       inst_3)
  (num_cpus : Nat) (j : Job)
  (mps : Prosa_Model_Processor_Multiprocessor_multiprocessor_state Job
           inst_3 processor_state num_cpus)
  (cpu : Prosa_Model_Processor_Multiprocessor_processor num_cpus) =>
Prosa_Behavior_Schedule_ProcessorState_service_in Job
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
       Prosa_Model_Processor_Multiprocessor_processor num_cpus -> Prosa_Behavior_Job_work

Arguments Prosa_Model_Processor_Multiprocessor_multiproc_service_on Job
  inst_3 processor_state
  num_cpus%_Nat_scope j mps cpu
```
