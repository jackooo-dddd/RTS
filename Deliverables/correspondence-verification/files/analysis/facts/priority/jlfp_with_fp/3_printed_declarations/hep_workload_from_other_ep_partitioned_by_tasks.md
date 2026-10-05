# `hep_workload_from_other_ep_partitioned_by_tasks`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.jlfp_with_fp.hep_workload_from_other_ep_partitioned_by_tasks`
- Lean: `Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_workload_from_other_ep_partitioned_by_tasks`
- Certificate: `hep_workload_from_other_ep_partitioned_by_tasks_correspondence`

## Official Rocq

```coq
hep_workload_from_other_ep_partitioned_by_tasks :
forall {Task : TaskType} {Job : JobType} {H0 : JobArrival Job} {H1 : JobTask Job Task} 
  {H2 : JobCost Job} {FP : FP_policy Task} {JLFP : JLFP_policy Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H0 arr_seq ->
forall ts : seq (Equality.sort Task),
is_true (@uniq Task ts) ->
@all_jobs_from_taskset Task Job H1 arr_seq ts ->
forall (tsk : Equality.sort Task) (j : Equality.sort Job),
is_true (@job_of_task Job Task H1 tsk j) ->
forall t1 t2 : duration,
@workload_of_jobs Job H2 (@hep_job_of_ep_other_task Task Job H1 FP JLFP j)
  (@arrivals_between Job arr_seq t1 t2) =
\sum_(tsk_o <- ts | @other_ep_task Task FP tsk tsk_o)
   @workload_of_jobs Job H2
     (fun j0 : Equality.sort Job =>
      @hep_job_of_ep_other_task Task Job H1 FP JLFP j j0 && (@job_task Job Task H1 j0 == tsk_o))
     (@arrivals_between Job arr_seq t1 t2)

hep_workload_from_other_ep_partitioned_by_tasks is not universe polymorphic
Arguments hep_workload_from_other_ep_partitioned_by_tasks {Task Job H0 H1 H2 FP JLFP} 
  arr_seq H_valid_arrival_sequence ts%seq_scope H_task_set H_all_jobs_from_taskset 
  tsk j H_job_of_task t1 t2
hep_workload_from_other_ep_partitioned_by_tasks is opaque
Expands to: Constant
            prosa.analysis.facts.priority.jlfp_with_fp.hep_workload_from_other_ep_partitioned_by_tasks
Declared in library prosa.analysis.facts.priority.jlfp_with_fp, line 59, characters 8-55
@hep_workload_from_other_ep_partitioned_by_tasks
     : forall (Task : TaskType) (Job : JobType) (H0 : JobArrival Job) (H1 : JobTask Job Task)
         (H2 : JobCost Job) (FP : FP_policy Task) (JLFP : JLFP_policy Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H0 arr_seq ->
       forall ts : seq (Equality.sort Task),
       is_true (@uniq Task ts) ->
       @all_jobs_from_taskset Task Job H1 arr_seq ts ->
       forall (tsk : Equality.sort Task) (j : Equality.sort Job),
       is_true (@job_of_task Job Task H1 tsk j) ->
       forall t1 t2 : duration,
       @workload_of_jobs Job H2 (@hep_job_of_ep_other_task Task Job H1 FP JLFP j)
         (@arrivals_between Job arr_seq t1 t2) =
       \sum_(tsk_o <- ts | @other_ep_task Task FP tsk tsk_o)
          @workload_of_jobs Job H2
            (fun j0 : Equality.sort Job =>
             @hep_job_of_ep_other_task Task Job H1 FP JLFP j j0 && (@job_task Job Task H1 j0 == tsk_o))
            (@arrivals_between Job arr_seq t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_workload_from_other_ep_partitioned_by_tasks : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  [FP : Prosa.Model.Priority.Definitions.FP_policy Task] [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : List Task),
      ts.Nodup →
        Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
          ∀ (tsk : Task) (j : Job),
            Prosa.Model.Task.Concept.job_of_task tsk j = true →
              ∀ (t1 t2 : Prosa.Behavior.Time.duration),
                Prosa.Model.Aggregate.Workload.workload_of_jobs
                    (Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_job_of_ep_other_task j)
                    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) =
                  Prosa.Util.Sum.sumFiltered ts (Prosa.Analysis.Facts.Priority.JlfpWithFp.other_ep_task tsk)
                    fun tsk_o =>
                    Prosa.Model.Aggregate.Workload.workload_of_jobs
                      (fun j0 =>
                        Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_job_of_ep_other_task j j0 &&
                          decide (Prosa.Model.Task.Concept.job_task j0 = tsk_o))
                      (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_workload_from_other_ep_partitioned_by_tasks
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_10 arr_seq ->
       forall ts : List Task,
       List_Nodup Task ts ->
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_7
         inst_13 arr_seq ts ->
       forall (tsk : Task) (j : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_13 tsk j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_duration,
       @eq Nat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_7
            inst_17
            (Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_job_of_ep_other_task Task
               inst_3 Job
               inst_7
               inst_13 FP JLFP j)
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_7 arr_seq t1 t2))
         (Prosa_Util_Sum_sumFiltered Task ts
            (Prosa_Analysis_Facts_Priority_JlfpWithFp_other_ep_task Task
               inst_3 FP tsk)
            (fun tsk_o : Task =>
             Prosa_Model_Aggregate_Workload_workload_of_jobs Job
               inst_7
               inst_17
               (fun j0 : Job =>
                Bool_and
                  (Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_job_of_ep_other_task Task
                     inst_3 Job
                     inst_7
                     inst_13 FP JLFP j
                     j0)
                  (Decidable_decide
                     (@eq Task
                        (Prosa_Model_Task_Concept_JobTask_job_task Job
                           inst_7 Task
                           inst_3
                           inst_13 j0)
                        tsk_o)
                     (inst_3
                        (Prosa_Model_Task_Concept_JobTask_job_task Job
                           inst_7 Task
                           inst_3
                           inst_13 j0)
                        tsk_o)))
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_7 arr_seq t1 t2)))
```
