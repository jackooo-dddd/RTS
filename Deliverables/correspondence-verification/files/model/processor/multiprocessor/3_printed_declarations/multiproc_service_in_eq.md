# `multiproc_service_in_eq`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.processor.multiprocessor.multiproc_service_in_eq`
- Lean: `Prosa.Model.Processor.Multiprocessor.multiproc_service_in_eq`
- Certificate: `multiproc_service_in_eq_correspondence`

## Official Rocq

```coq
multiproc_service_in_eq :
forall (Job : JobType) (processor_state : ProcessorState Job) (num_cpus : nat) (j : Equality.sort Job)
  (mps : multiprocessor_state Job processor_state num_cpus),
@service_in Job (multiproc_state Job processor_state num_cpus) j mps =
\sum_(cpu < num_cpus) @service_in Job processor_state j (mps cpu)

multiproc_service_in_eq is not universe polymorphic
Arguments multiproc_service_in_eq Job processor_state num_cpus%nat_scope j mps
multiproc_service_in_eq is opaque
Expands to: Constant prosa.model.processor.multiprocessor.multiproc_service_in_eq
Declared in library prosa.model.processor.multiprocessor, line 84, characters 8-31
multiproc_service_in_eq
     : forall (Job : JobType) (processor_state : ProcessorState Job) (num_cpus : nat) 
         (j : Equality.sort Job) (mps : multiprocessor_state Job processor_state num_cpus),
       @service_in Job (multiproc_state Job processor_state num_cpus) j mps =
       \sum_(cpu < num_cpus) @service_in Job processor_state j (mps cpu)
```

## Lean

```lean
Prosa.Model.Processor.Multiprocessor.multiproc_service_in_eq : ∀ (Job : Prosa.Behavior.Job.JobType)
  [inst : DecidableEq Job] (processor_state : Prosa.Behavior.Schedule.ProcessorState Job) (num_cpus : ℕ) (j : Job)
  (mps : Prosa.Model.Processor.Multiprocessor.multiprocessor_state Job processor_state num_cpus),
  (Prosa.Model.Processor.Multiprocessor.multiproc_state Job processor_state num_cpus).service_in j mps =
    ∑ cpu, processor_state.service_in j (mps cpu)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Multiprocessor_multiproc_service_in_eq
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (processor_state : Prosa_Behavior_Schedule_ProcessorState Job
                              inst_3)
         (num_cpus : Nat) (j : Job)
         (mps : Prosa_Model_Processor_Multiprocessor_multiprocessor_state Job
                  inst_3 processor_state
                  num_cpus),
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Schedule_ProcessorState_service_in_inst4 Job
            inst_3
            (Prosa_Model_Processor_Multiprocessor_multiproc_state Job
               inst_3 processor_state
               num_cpus)
            j mps)
         (Finset_sum_inst3 (Fin num_cpus) Prosa_Behavior_Job_work Nat_instAddCommMonoid
            (Finset_univ_inst1 (Fin num_cpus) (Fin_fintype num_cpus))
            (fun cpu : Fin num_cpus =>
             Prosa_Behavior_Schedule_ProcessorState_service_in Job
               inst_3 processor_state j
               (mps cpu)))
```
