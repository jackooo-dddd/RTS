# `task_arrivals_with_deadline_within_eq`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.dbf.task_arrivals_with_deadline_within_eq`
- Lean: `Prosa.Analysis.Facts.Model.Dbf.task_arrivals_with_deadline_within_eq`
- Certificate: `task_arrivals_with_deadline_within_eq_correspondence`

## Official Rocq

```coq
task_arrivals_with_deadline_within_eq :
forall {Task : TaskType} {H : TaskDeadline Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall (tsk : Equality.sort Task) (t : instant) (delta : duration),
@task_arrivals_with_deadline_within Job Task H0 arr_seq tsk
  (@job_deadline_from_task_deadline Job Task H H1 H0) t (t + delta) =
@task_arrivals_between Job Task H0 arr_seq tsk t (t + (delta - (@task_deadline Task H tsk - 1)))

task_arrivals_with_deadline_within_eq is not universe polymorphic
Arguments task_arrivals_with_deadline_within_eq {Task H Job H0 H1} arr_seq H_valid_arrival_sequence 
  tsk t delta
task_arrivals_with_deadline_within_eq is opaque
Expands to: Constant prosa.analysis.facts.model.dbf.task_arrivals_with_deadline_within_eq
Declared in library prosa.analysis.facts.model.dbf, line 19, characters 8-45
@task_arrivals_with_deadline_within_eq
     : forall (Task : TaskType) (H : TaskDeadline Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall (tsk : Equality.sort Task) (t : instant) (delta : duration),
       @task_arrivals_with_deadline_within Job Task H0 arr_seq tsk
         (@job_deadline_from_task_deadline Job Task H H1 H0) t (t + delta) =
       @task_arrivals_between Job Task H0 arr_seq tsk t (t + (delta - (@task_deadline Task H tsk - 1)))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Dbf.task_arrivals_with_deadline_within_eq : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskDeadline Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task) (t : Prosa.Behavior.Time.instant) (delta : Prosa.Behavior.Time.duration),
      Prosa.Model.Task.Arrivals.task_arrivals_with_deadline_within arr_seq tsk t (t + delta) =
        Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t
          (t + (delta - (Prosa.Model.Task.Concept.task_deadline tsk - 1)))
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Dbf_task_arrivals_with_deadline_within_eq
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Task_Concept_TaskDeadline
                                                                                Task
                                                                                inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_10
         inst_17 arr_seq ->
       forall (tsk : Task) (t : Prosa_Behavior_Time_instant) (delta : Prosa_Behavior_Time_duration),
       @eq (List Job)
         (Prosa_Model_Task_Arrivals_task_arrivals_with_deadline_within Job
            inst_10 Task
            inst_3
            inst_13 arr_seq tsk
            (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
               inst_10
               inst_3
               inst_6
               inst_17
               inst_13)
            t
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t delta))
         (Prosa_Model_Task_Arrivals_task_arrivals_between Job
            inst_10 Task
            inst_3
            inst_13 arr_seq tsk t
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
               (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) delta
                  (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
                     Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                     (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                        inst_3
                        inst_6 tsk)
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))))
```
