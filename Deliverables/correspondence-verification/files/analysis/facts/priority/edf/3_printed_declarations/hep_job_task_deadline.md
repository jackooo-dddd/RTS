# `hep_job_task_deadline`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.priority.edf.hep_job_task_deadline`
- Lean: `Prosa.Analysis.Facts.Priority.Edf.hep_job_task_deadline`
- Certificate: `hep_job_task_deadline_correspondence`

## Official Rocq

```coq
hep_job_task_deadline :
forall {Job : JobType} {H : JobArrival Job} {Task : TaskType} {H0 : TaskDeadline Task}
  {H1 : JobTask Job Task} (j j' : Equality.sort Job),
@hep_job Job (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H H1)) j j' =
(@job_arrival Job H j + @task_deadline Task H0 (@job_task Job Task H1 j) <=
 @job_arrival Job H j' + @task_deadline Task H0 (@job_task Job Task H1 j'))

hep_job_task_deadline is not universe polymorphic
Arguments hep_job_task_deadline {Job H Task H0 H1} j j'
hep_job_task_deadline is opaque
Expands to: Constant prosa.analysis.facts.priority.edf.hep_job_task_deadline
Declared in library prosa.analysis.facts.priority.edf, line 36, characters 9-30
@hep_job_task_deadline
     : forall (Job : JobType) (H : JobArrival Job) (Task : TaskType) (H0 : TaskDeadline Task)
         (H1 : JobTask Job Task) (j j' : Equality.sort Job),
       @hep_job Job (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H H1)) j j' =
       (@job_arrival Job H j + @task_deadline Task H0 (@job_task Job Task H1 j) <=
        @job_arrival Job H j' + @task_deadline Task H0 (@job_task Job Task H1 j'))
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Edf.hep_job_task_deadline : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_2 : DecidableEq Task]
  [inst_3 : Prosa.Model.Task.Concept.TaskDeadline Task] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  (j j' : Job),
  Prosa.Model.Priority.Definitions.hep_job j j' =
    decide
      (Prosa.Behavior.Job.job_arrival j + Prosa.Model.Task.Concept.task_deadline (Prosa.Model.Task.Concept.job_task j) ≤
        Prosa.Behavior.Job.job_arrival j' +
          Prosa.Model.Task.Concept.task_deadline (Prosa.Model.Task.Concept.job_task j'))
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Edf_hep_job_task_deadline
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_10 : DecidableEq Task)
         (inst_13 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_10)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_10)
         (j j' : Job),
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_3
            (Prosa_Model_Priority_Edf_EDF Job
               inst_3
               (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
                  inst_3
                  inst_10
                  inst_13
                  inst_6
                  inst_16))
            j j')
         (Decidable_decide
            (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_6 j)
                  (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                     inst_10
                     inst_13
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_3 Task
                        inst_10
                        inst_16 j)))
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_6 j')
                  (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                     inst_10
                     inst_13
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_3 Task
                        inst_10
                        inst_16 j'))))
            (Nat_decLe
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_6 j)
                  (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                     inst_10
                     inst_13
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_3 Task
                        inst_10
                        inst_16 j)))
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_6 j')
                  (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                     inst_10
                     inst_13
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_3 Task
                        inst_10
                        inst_16 j')))))
```
