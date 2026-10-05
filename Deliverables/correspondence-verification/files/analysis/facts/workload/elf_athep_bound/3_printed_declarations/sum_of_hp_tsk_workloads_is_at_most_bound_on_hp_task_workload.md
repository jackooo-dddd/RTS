# `sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.workload.elf_athep_bound.sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload`
- Lean: `Prosa.Analysis.Facts.Workload.ElfAthepBound.sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload`
- Certificate: `sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload_correspondence`

## Official Rocq

```coq
sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {H1 : PriorityPoint Task}
  {Job : JobType} {H2 : JobTask Job Task} {H3 : JobArrival Job} {H4 : JobCost Job}
  (arr_seq : arrival_sequence Job),
@arrivals_have_valid_job_costs Task H Job H2 H4 arr_seq ->
forall ts : seq (Equality.sort Task),
@taskset_respects_max_arrivals Task Job H2 arr_seq H0 ts ->
forall (tsk : Equality.sort Task) (FP : FP_policy Task) (j : Equality.sort Job) (t1 delta : duration),
is_true
  (\sum_(tsk_o <- ts | @hp_task Task FP tsk_o tsk)
      @workload_of_jobs Job H4
        ((fun (tsk_o0 : Equality.sort Task) (jo : Equality.sort Job) =>
          @hep_job Job (@ELF Task H1 Job H3 H2 FP) jo j && (@job_task Job Task H2 jo == tsk_o0)) tsk_o)
        (@arrivals_between Job arr_seq t1 (t1 + delta)) <=
   @bound_on_hp_task_workload Task H H0 ts FP tsk delta)

sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload is not universe polymorphic
Arguments sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload {Task H H0 H1 Job H2 H3 H4} 
  arr_seq H_valid_job_cost ts%seq_scope H_is_arrival_curve tsk FP j t1 delta
sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload is opaque
Expands to: Constant
            prosa.analysis.facts.workload.elf_athep_bound.sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload
Declared in library prosa.analysis.facts.workload.elf_athep_bound, line 162, characters 14-74
@sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (H1 : PriorityPoint Task)
         (Job : JobType) (H2 : JobTask Job Task) (H3 : JobArrival Job) (H4 : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @arrivals_have_valid_job_costs Task H Job H2 H4 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @taskset_respects_max_arrivals Task Job H2 arr_seq H0 ts ->
       forall (tsk : Equality.sort Task) (FP : FP_policy Task) (j : Equality.sort Job) (t1 delta : duration),
       is_true
         (\sum_(tsk_o <- ts | @hp_task Task FP tsk_o tsk)
             @workload_of_jobs Job H4
               (fun jo : Equality.sort Job =>
                @hep_job Job (@ELF Task H1 Job H3 H2 FP) jo j && (@job_task Job Task H2 jo == tsk_o))
               (@arrivals_between Job arr_seq t1 (t1 + delta)) <=
          @bound_on_hp_task_workload Task H H0 ts FP tsk delta)
```

## Lean

```lean
@Prosa.Analysis.Facts.Workload.ElfAthepBound.sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [inst_3 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_4 : DecidableEq Job] [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_6 : Prosa.Behavior.Job.JobArrival Job] [inst_7 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
    ∀ (ts : List Task),
      Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
        ∀ (tsk : Task) (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (j : Job)
          (t1 delta : Prosa.Behavior.Time.duration),
          (Prosa.Util.Sum.sumFiltered ts (fun tsk_o => Prosa.Model.Priority.Definitions.hp_task tsk_o tsk) fun tsk_o =>
              Prosa.Model.Aggregate.Workload.workload_of_jobs
                (fun jo =>
                  Prosa.Model.Priority.Definitions.hep_job jo j &&
                    decide (Prosa.Model.Task.Concept.job_task jo = tsk_o))
                (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + delta))) ≤
            Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_hp_task_workload ts tsk delta
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Workload_ElfAthepBound_sum_of_hp_tsk_workloads_is_at_most_bound_on_hp_task_workload
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
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
         (inst_16 : 
          DecidableEq Job)
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
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_16),
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_16
         inst_19
         inst_26 arr_seq ->
       forall ts : List Task,
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_16
         inst_19 arr_seq
         inst_9 ts ->
       forall (tsk : Task)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (j : Job) (t1 delta : Prosa_Behavior_Time_duration),
       LE_le_inst1 Nat instLENat
         (Prosa_Util_Sum_sumFiltered Task ts
            (fun tsk_o : Task =>
             Prosa_Model_Priority_Definitions_hp_task Task
               inst_3 FP tsk_o tsk)
            (fun tsk_o : Task =>
             Prosa_Model_Aggregate_Workload_workload_of_jobs Job
               inst_16
               inst_26
               (fun jo : Job =>
                Bool_and
                  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                     inst_16
                     (Prosa_Model_Priority_Elf_ELF Task
                        inst_3
                        inst_12 Job
                        inst_16
                        inst_23
                        inst_19 FP)
                     jo j)
                  (Decidable_decide
                     (@eq Task
                        (Prosa_Model_Task_Concept_JobTask_job_task Job
                           inst_16
                           Task
                           inst_3
                           inst_19
                           jo)
                        tsk_o)
                     (inst_3
                        (Prosa_Model_Task_Concept_JobTask_job_task Job
                           inst_16
                           Task
                           inst_3
                           inst_19
                           jo)
                        tsk_o)))
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_16 arr_seq
                  t1
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1
                     delta))))
         (Prosa_Analysis_Definitions_Workload_ElfAthepBound_bound_on_hp_task_workload Task
            inst_3
            inst_6
            inst_9 ts FP tsk delta)
```
