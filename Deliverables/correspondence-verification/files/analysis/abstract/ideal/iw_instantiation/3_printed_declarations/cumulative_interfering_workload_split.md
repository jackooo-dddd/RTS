# `cumulative_interfering_workload_split`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.ideal.iw_instantiation.cumulative_interfering_workload_split`
- Lean: `Prosa.Analysis.Abstract.Ideal.IwInstantiation.cumulative_interfering_workload_split`
- Certificate: `cumulative_interfering_workload_split_correspondence`

## Official Rocq

```coq
cumulative_interfering_workload_split :
forall {Job : JobType} {H2 : JobCost Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job (ideal.processor_state Job)) {JLFP : JLFP_policy Job} (j : Equality.sort Job)
  (t1 t2 : nat),
@cumulative_interfering_workload Job (@ideal_jlfp_interfering_workload Job H2 arr_seq sched JLFP) j t1 t2 =
@cumulative_priority_inversion Job (ideal.processor_state Job) arr_seq sched JLFP j t1 t2 +
@cumulative_other_hep_jobs_interfering_workload Job H2 arr_seq JLFP j t1 t2

cumulative_interfering_workload_split is not universe polymorphic
Arguments cumulative_interfering_workload_split {Job H2} arr_seq sched {JLFP} j (t1 t2)%nat_scope
cumulative_interfering_workload_split is opaque
Expands to: Constant prosa.analysis.abstract.ideal.iw_instantiation.cumulative_interfering_workload_split
Declared in library prosa.analysis.abstract.ideal.iw_instantiation, line 248, characters 8-45
@cumulative_interfering_workload_split
     : forall (Job : JobType) (H2 : JobCost Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job (ideal.processor_state Job)) (JLFP : JLFP_policy Job) 
         (j : Equality.sort Job) (t1 t2 : nat),
       @cumulative_interfering_workload Job (@ideal_jlfp_interfering_workload Job H2 arr_seq sched JLFP) j t1
         t2 =
       @cumulative_priority_inversion Job (ideal.processor_state Job) arr_seq sched JLFP j t1 t2 +
       @cumulative_other_hep_jobs_interfering_workload Job H2 arr_seq JLFP j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Abstract.Ideal.IwInstantiation.cumulative_interfering_workload_split : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  [inst_2 : Prosa.Model.Priority.Definitions.JLFP_policy Job] (j : Job) (t1 t2 : ℕ),
  Prosa.Analysis.Abstract.Definitions.cumulative_interfering_workload j t1 t2 =
    Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion arr_seq sched j t1 t2 +
      Prosa.Analysis.Definitions.Interference.cumulative_other_hep_jobs_interfering_workload arr_seq j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Ideal_IwInstantiation_cumulative_interfering_workload_split
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_7
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_7))
         (inst_20 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_7)
         (j : Job) (t1 t2 : Nat),
       @eq Nat
         (Prosa_Analysis_Abstract_Definitions_cumulative_interfering_workload Job
            inst_7
            (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
               inst_7
               inst_10 arr_seq
               sched inst_20)
            j t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion_inst4 Job
               inst_7
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_7)
               arr_seq sched
               inst_20 j t1 t2)
            (Prosa_Analysis_Definitions_Interference_cumulative_other_hep_jobs_interfering_workload Job
               inst_7
               inst_10 arr_seq
               inst_20 j t1 t2))
```
