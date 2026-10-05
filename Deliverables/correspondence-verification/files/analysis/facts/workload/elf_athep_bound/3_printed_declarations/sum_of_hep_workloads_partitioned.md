# `sum_of_hep_workloads_partitioned`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.workload.elf_athep_bound.sum_of_hep_workloads_partitioned`
- Lean: `Prosa.Analysis.Facts.Workload.ElfAthepBound.sum_of_hep_workloads_partitioned`
- Certificate: `sum_of_hep_workloads_partitioned_correspondence`

## Official Rocq

```coq
sum_of_hep_workloads_partitioned :
forall {Task : TaskType} {H1 : PriorityPoint Task} {Job : JobType} {H2 : JobTask Job Task}
  {H3 : JobArrival Job} {H4 : JobCost Job} (arr_seq : arrival_sequence Job) (ts : seq (Equality.sort Task))
  (tsk : Equality.sort Task) (FP : FP_policy Task) (j : Equality.sort Job),
is_true (@job_of_task Job Task H2 tsk j) ->
forall t1 delta : duration,
\sum_(tsk_o <- ts | tsk_o != tsk)
   @workload_of_jobs Job H4
     ((fun (tsk_o0 : Equality.sort Task) (jo : Equality.sort Job) =>
       @hep_job Job (@ELF Task H1 Job H3 H2 FP) jo j && (@job_task Job Task H2 jo == tsk_o0)) tsk_o)
     (@arrivals_between Job arr_seq t1 (t1 + delta)) =
\sum_(tsk_o <- ts | @ep_task Task FP tsk tsk_o && (tsk_o != tsk))
   @workload_of_jobs Job H4
     ((fun (tsk_o0 : Equality.sort Task) (jo : Equality.sort Job) =>
       @hep_job Job (@ELF Task H1 Job H3 H2 FP) jo j && (@job_task Job Task H2 jo == tsk_o0)) tsk_o)
     (@arrivals_between Job arr_seq t1 (t1 + delta)) +
\sum_(tsk_o <- ts | @hp_task Task FP tsk_o tsk)
   @workload_of_jobs Job H4
     ((fun (tsk_o0 : Equality.sort Task) (jo : Equality.sort Job) =>
       @hep_job Job (@ELF Task H1 Job H3 H2 FP) jo j && (@job_task Job Task H2 jo == tsk_o0)) tsk_o)
     (@arrivals_between Job arr_seq t1 (t1 + delta))

sum_of_hep_workloads_partitioned is not universe polymorphic
Arguments sum_of_hep_workloads_partitioned {Task H1 Job H2 H3 H4} arr_seq ts%seq_scope 
  tsk FP j H_job_of_tsk t1 delta
sum_of_hep_workloads_partitioned is opaque
Expands to: Constant prosa.analysis.facts.workload.elf_athep_bound.sum_of_hep_workloads_partitioned
Declared in library prosa.analysis.facts.workload.elf_athep_bound, line 174, characters 10-42
@sum_of_hep_workloads_partitioned
     : forall (Task : TaskType) (H1 : PriorityPoint Task) (Job : JobType) (H2 : JobTask Job Task)
         (H3 : JobArrival Job) (H4 : JobCost Job) (arr_seq : arrival_sequence Job)
         (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (FP : FP_policy Task)
         (j : Equality.sort Job),
       is_true (@job_of_task Job Task H2 tsk j) ->
       forall t1 delta : duration,
       \sum_(tsk_o <- ts | tsk_o != tsk)
          @workload_of_jobs Job H4
            (fun jo : Equality.sort Job =>
             @hep_job Job (@ELF Task H1 Job H3 H2 FP) jo j && (@job_task Job Task H2 jo == tsk_o))
            (@arrivals_between Job arr_seq t1 (t1 + delta)) =
       \sum_(tsk_o <- ts | @ep_task Task FP tsk tsk_o && (tsk_o != tsk))
          @workload_of_jobs Job H4
            (fun jo : Equality.sort Job =>
             @hep_job Job (@ELF Task H1 Job H3 H2 FP) jo j && (@job_task Job Task H2 jo == tsk_o))
            (@arrivals_between Job arr_seq t1 (t1 + delta)) +
       \sum_(tsk_o <- ts | @hp_task Task FP tsk_o tsk)
          @workload_of_jobs Job H4
            (fun jo : Equality.sort Job =>
             @hep_job Job (@ELF Task H1 Job H3 H2 FP) jo j && (@job_task Job Task H2 jo == tsk_o))
            (@arrivals_between Job arr_seq t1 (t1 + delta))
```

## Lean

```lean
@Prosa.Analysis.Facts.Workload.ElfAthepBound.sum_of_hep_workloads_partitioned : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Priority.Gel.PriorityPoint Task] {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobArrival Job]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (ts : List Task) (tsk : Task) (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (j : Job),
  Prosa.Model.Task.Concept.job_of_task tsk j = true →
    ∀ (t1 delta : Prosa.Behavior.Time.duration),
      (Prosa.Util.Sum.sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk)) fun tsk_o =>
          Prosa.Model.Aggregate.Workload.workload_of_jobs
            (fun jo =>
              Prosa.Model.Priority.Definitions.hep_job jo j && decide (Prosa.Model.Task.Concept.job_task jo = tsk_o))
            (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + delta))) =
        (Prosa.Util.Sum.sumFiltered ts
            (fun tsk_o => Prosa.Model.Priority.Definitions.ep_task tsk tsk_o && decide (tsk_o ≠ tsk)) fun tsk_o =>
            Prosa.Model.Aggregate.Workload.workload_of_jobs
              (fun jo =>
                Prosa.Model.Priority.Definitions.hep_job jo j && decide (Prosa.Model.Task.Concept.job_task jo = tsk_o))
              (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + delta))) +
          Prosa.Util.Sum.sumFiltered ts (fun tsk_o => Prosa.Model.Priority.Definitions.hp_task tsk_o tsk) fun tsk_o =>
            Prosa.Model.Aggregate.Workload.workload_of_jobs
              (fun jo =>
                Prosa.Model.Priority.Definitions.hep_job jo j && decide (Prosa.Model.Task.Concept.job_task jo = tsk_o))
              (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + delta))
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Workload_ElfAthepBound_sum_of_hep_workloads_partitioned
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10)
         (ts : List Task) (tsk : Task)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (j : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_10 Task
            inst_3
            inst_13 tsk j)
         Bool_true ->
       forall t1 delta : Prosa_Behavior_Time_duration,
       @eq Nat
         (Prosa_Util_Sum_sumFiltered Task ts
            (fun tsk_o : Task =>
             Decidable_decide (Ne Task tsk_o tsk)
               (instDecidableNot (@eq Task tsk_o tsk)
                  (inst_3 tsk_o tsk)))
            (fun tsk_o : Task =>
             Prosa_Model_Aggregate_Workload_workload_of_jobs Job
               inst_10
               inst_20
               (fun jo : Job =>
                Bool_and
                  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                     inst_10
                     (Prosa_Model_Priority_Elf_ELF Task
                        inst_3
                        inst_6 Job
                        inst_10
                        inst_17
                        inst_13 FP)
                     jo j)
                  (Decidable_decide
                     (@eq Task
                        (Prosa_Model_Task_Concept_JobTask_job_task Job
                           inst_10
                           Task
                           inst_3
                           inst_13
                           jo)
                        tsk_o)
                     (inst_3
                        (Prosa_Model_Task_Concept_JobTask_job_task Job
                           inst_10
                           Task
                           inst_3
                           inst_13
                           jo)
                        tsk_o)))
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_10 arr_seq
                  t1
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1
                     delta))))
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Util_Sum_sumFiltered Task ts
               (fun tsk_o : Task =>
                Bool_and
                  (Prosa_Model_Priority_Definitions_ep_task Task
                     inst_3 FP tsk
                     tsk_o)
                  (Decidable_decide (Ne Task tsk_o tsk)
                     (instDecidableNot (@eq Task tsk_o tsk)
                        (inst_3
                           tsk_o tsk))))
               (fun tsk_o : Task =>
                Prosa_Model_Aggregate_Workload_workload_of_jobs Job
                  inst_10
                  inst_20
                  (fun jo : Job =>
                   Bool_and
                     (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                        inst_10
                        (Prosa_Model_Priority_Elf_ELF Task
                           inst_3
                           inst_6
                           Job
                           inst_10
                           inst_17
                           inst_13
                           FP)
                        jo j)
                     (Decidable_decide
                        (@eq Task
                           (Prosa_Model_Task_Concept_JobTask_job_task Job
                              inst_10
                              Task
                              inst_3
                              inst_13
                              jo)
                           tsk_o)
                        (inst_3
                           (Prosa_Model_Task_Concept_JobTask_job_task Job
                              inst_10
                              Task
                              inst_3
                              inst_13
                              jo)
                           tsk_o)))
                  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                     inst_10
                     arr_seq t1
                     (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                        Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                        t1 delta))))
            (Prosa_Util_Sum_sumFiltered Task ts
               (fun tsk_o : Task =>
                Prosa_Model_Priority_Definitions_hp_task Task
                  inst_3 FP tsk_o
                  tsk)
               (fun tsk_o : Task =>
                Prosa_Model_Aggregate_Workload_workload_of_jobs Job
                  inst_10
                  inst_20
                  (fun jo : Job =>
                   Bool_and
                     (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                        inst_10
                        (Prosa_Model_Priority_Elf_ELF Task
                           inst_3
                           inst_6
                           Job
                           inst_10
                           inst_17
                           inst_13
                           FP)
                        jo j)
                     (Decidable_decide
                        (@eq Task
                           (Prosa_Model_Task_Concept_JobTask_job_task Job
                              inst_10
                              Task
                              inst_3
                              inst_13
                              jo)
                           tsk_o)
                        (inst_3
                           (Prosa_Model_Task_Concept_JobTask_job_task Job
                              inst_10
                              Task
                              inst_3
                              inst_13
                              jo)
                           tsk_o)))
                  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                     inst_10
                     arr_seq t1
                     (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                        Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                        t1 delta)))))
```
