# `hep_hp_workload_hp`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.jlfp_with_fp.hep_hp_workload_hp`
- Lean: `Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_hp_workload_hp`
- Certificate: `hep_hp_workload_hp_correspondence`

## Official Rocq

```coq
hep_hp_workload_hp :
forall {Task : TaskType} {Job : JobType} {H1 : JobTask Job Task} {H2 : JobCost Job} 
  {FP : FP_policy Task} {JLFP : JLFP_policy Job},
@JLFP_FP_compatible Task Job H1 JLFP FP ->
forall (arr_seq : arrival_sequence Job) (j : Equality.sort Job) (t1 t2 : duration),
@workload_of_jobs Job H2 (@hep_from_hp_task Task Job H1 FP JLFP j) (@arrivals_between Job arr_seq t1 t2) =
@workload_of_jobs Job H2 (@from_hp_task Task Job H1 FP j) (@arrivals_between Job arr_seq t1 t2)

hep_hp_workload_hp is not universe polymorphic
Arguments hep_hp_workload_hp {Task Job H1 H2 FP JLFP} JLFP_FP_is_compatible arr_seq j t1 t2
hep_hp_workload_hp is opaque
Expands to: Constant prosa.analysis.facts.priority.jlfp_with_fp.hep_hp_workload_hp
Declared in library prosa.analysis.facts.priority.jlfp_with_fp, line 91, characters 8-26
@hep_hp_workload_hp
     : forall (Task : TaskType) (Job : JobType) (H1 : JobTask Job Task) (H2 : JobCost Job)
         (FP : FP_policy Task) (JLFP : JLFP_policy Job),
       @JLFP_FP_compatible Task Job H1 JLFP FP ->
       forall (arr_seq : arrival_sequence Job) (j : Equality.sort Job) (t1 t2 : duration),
       @workload_of_jobs Job H2 (@hep_from_hp_task Task Job H1 FP JLFP j)
         (@arrivals_between Job arr_seq t1 t2) =
       @workload_of_jobs Job H2 (@from_hp_task Task Job H1 FP j) (@arrivals_between Job arr_seq t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_hp_workload_hp : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobCost Job]
  [FP : Prosa.Model.Priority.Definitions.FP_policy Task] [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
  Prosa.Analysis.Definitions.Priority.Classes.JLFP_FP_compatible JLFP FP →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (j : Job) (t1 t2 : Prosa.Behavior.Time.duration),
      Prosa.Model.Aggregate.Workload.workload_of_jobs (Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_from_hp_task j)
          (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2) =
        Prosa.Model.Aggregate.Workload.workload_of_jobs (Prosa.Analysis.Facts.Priority.JlfpWithFp.from_hp_task j)
          (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_hp_workload_hp
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7),
       Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible Task
         inst_3 Job
         inst_7
         inst_10 JLFP FP ->
       forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (j : Job) (t1 t2 : Prosa_Behavior_Time_duration),
       @eq Nat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_7
            inst_14
            (Prosa_Analysis_Facts_Priority_JlfpWithFp_hep_from_hp_task Task
               inst_3 Job
               inst_7
               inst_10 FP JLFP j)
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_7 arr_seq t1 t2))
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_7
            inst_14
            (Prosa_Analysis_Facts_Priority_JlfpWithFp_from_hp_task Task
               inst_3 Job
               inst_7
               inst_10 FP j)
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_7 arr_seq t1 t2))
```
