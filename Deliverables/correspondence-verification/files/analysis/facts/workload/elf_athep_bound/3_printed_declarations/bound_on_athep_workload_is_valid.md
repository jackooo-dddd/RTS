# `bound_on_athep_workload_is_valid`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.workload.elf_athep_bound.bound_on_athep_workload_is_valid`
- Lean: `Prosa.Analysis.Facts.Workload.ElfAthepBound.bound_on_athep_workload_is_valid`
- Certificate: `bound_on_athep_workload_is_valid_correspondence`

## Official Rocq

```coq
bound_on_athep_workload_is_valid :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {H1 : PriorityPoint Task}
  {Job : JobType} {H2 : JobTask Job Task} {H3 : JobArrival Job} {H4 : JobCost Job}
  {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H3 arr_seq ->
@arrivals_have_valid_job_costs Task H Job H2 H4 arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H2 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H2 arr_seq H0 ts ->
forall (tsk : Equality.sort Task) (sched : @schedule Job PState) (FP : FP_policy Task),
@athep_workload_is_bounded Task Job H4 H3 H2 PState (@ELF Task H1 Job H3 H2 FP) arr_seq sched tsk
  (@bound_on_athep_workload Task H H0 H1 ts FP tsk)

bound_on_athep_workload_is_valid is not universe polymorphic
Arguments bound_on_athep_workload_is_valid {Task H H0 H1 Job H2 H3 H4 PState} arr_seq
  H_valid_arrival_sequence H_valid_job_cost ts%seq_scope H_all_jobs_from_taskset 
  H_is_arrival_curve tsk sched FP j t1 Δ _ _ _
bound_on_athep_workload_is_valid is opaque
Expands to: Constant prosa.analysis.facts.workload.elf_athep_bound.bound_on_athep_workload_is_valid
Declared in library prosa.analysis.facts.workload.elf_athep_bound, line 231, characters 12-44
@bound_on_athep_workload_is_valid
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (H1 : PriorityPoint Task)
         (Job : JobType) (H2 : JobTask Job Task) (H3 : JobArrival Job) (H4 : JobCost Job)
         (PState : ProcessorState Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H3 arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H2 H4 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H2 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H2 arr_seq H0 ts ->
       forall (tsk : Equality.sort Task) (sched : @schedule Job PState) (FP : FP_policy Task),
       @athep_workload_is_bounded Task Job H4 H3 H2 PState (@ELF Task H1 Job H3 H2 FP) arr_seq sched tsk
         (@bound_on_athep_workload Task H H0 H1 ts FP tsk)
New coercion path [GRing.subring_closedM; GRing.smulr_closedN] : GRing.subring_closed >-> GRing.oppr_closed is ambiguous with existing 
New coercion path [GRing.subring_closed_semi; GRing.semiring_closedM] : GRing.subring_closed >-> GRing.mulr_closed is ambiguous with existing 
New coercion path [GRing.subring_closed_semi; GRing.semiring_closedD] : GRing.subring_closed >-> GRing.addr_closed is ambiguous with existing 
New coercion path [GRing.submod_closed_semi; GRing.subsemimod_closedD] : GRing.submod_closed >-> GRing.addr_closed is ambiguous with existing 
New coercion path [GRing.subalg_closedBM; GRing.subring_closedB] : GRing.subalg_closed >-> GRing.zmod_closed is ambiguous with existing 
New coercion path [GRing.sdivr_closedM; GRing.smulr_closedM] : GRing.sdivr_closed >-> GRing.mulr_closed is ambiguous with existing 
New coercion path [GRing.divring_closed_div; GRing.sdivr_closedM] : GRing.divring_closed >-> GRing.smulr_closed is ambiguous with existing 
New coercion path [GRing.divalg_closedZ; GRing.subalg_closedBM] : GRing.divalg_closed >-> GRing.subring_closed is ambiguous with existing
```

## Lean

```lean
@Prosa.Analysis.Facts.Workload.ElfAthepBound.bound_on_athep_workload_is_valid : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [inst_3 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_4 : DecidableEq Job] [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_6 : Prosa.Behavior.Job.JobArrival Job] [inst_7 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
      ∀ (ts : List Task),
        Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
          Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
            ∀ (tsk : Task) (sched : Prosa.Behavior.Schedule.schedule PState)
              (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
              Prosa.Analysis.Definitions.Workload.Bounded.athep_workload_is_bounded arr_seq sched tsk
                (Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_athep_workload ts tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Workload_ElfAthepBound_bound_on_athep_workload_is_valid
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_12 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_16 : DecidableEq Job)
         (inst_19 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_16 Task
            inst_3)
         (inst_23 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_16)
         (inst_26 : 
          Prosa_Behavior_Job_JobCost Job
            inst_16)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_16)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_16),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_16
         inst_23 arr_seq ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_16
         inst_19
         inst_26 arr_seq ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_16
         inst_19 arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_16
         inst_19 arr_seq
         inst_9 ts ->
       forall (tsk : Task)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_16 PState)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3),
       Prosa_Analysis_Definitions_Workload_Bounded_athep_workload_is_bounded Task
         inst_3 Job
         inst_16
         inst_26
         inst_23
         inst_19 PState
         (Prosa_Model_Priority_Elf_ELF Task
            inst_3
            inst_12 Job
            inst_16
            inst_23
            inst_19 FP)
         arr_seq sched tsk
         (Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_athep_workload Task
            inst_3
            inst_6
            inst_9
            inst_12 ts FP tsk)
```
