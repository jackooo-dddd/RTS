# `job_suspension_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.dynamic_suspension.job_suspension_bounded`
- Lean: `Prosa.Analysis.Facts.Model.DynamicSuspension.job_suspension_bounded`
- Certificate: `job_suspension_bounded_correspondence`

## Official Rocq

```coq
job_suspension_bounded :
forall {Task : TaskType} {H1 : TaskTotalSuspension Task} {Job : JobType} {H2 : JobTask Job Task}
  {H3 : JobArrival Job} {H4 : JobCost Job} {H5 : JobSuspension Job},
@valid_dynamic_suspensions Job H4 H5 Task H2 H1 ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState) (tsk : Equality.sort Task) 
  (t1 : instant) (Δ : duration) (j : Equality.sort Job),
is_true (@job_of_task Job Task H2 tsk j) ->
is_true
  (\sum_(t1 <= t < t1 + Δ) nat_of_bool (@suspended Job PState H3 H4 H5 sched j t) <=
   @task_total_suspension Task H1 tsk)

job_suspension_bounded is not universe polymorphic
Arguments job_suspension_bounded {Task H1 Job H2 H3 H4 H5} H_valid_dynamic_suspensions 
  {PState} sched tsk t1 Δ j H_job_tsk
job_suspension_bounded is opaque
Expands to: Constant prosa.analysis.facts.model.dynamic_suspension.job_suspension_bounded
Declared in library prosa.analysis.facts.model.dynamic_suspension, line 60, characters 10-32
@job_suspension_bounded
     : forall (Task : TaskType) (H1 : TaskTotalSuspension Task) (Job : JobType) (H2 : JobTask Job Task)
         (H3 : JobArrival Job) (H4 : JobCost Job) (H5 : JobSuspension Job),
       @valid_dynamic_suspensions Job H4 H5 Task H2 H1 ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState) (tsk : Equality.sort Task)
         (t1 : instant) (Δ : duration) (j : Equality.sort Job),
       is_true (@job_of_task Job Task H2 tsk j) ->
       is_true
         (\sum_(t1 <= t < t1 + Δ) nat_of_bool (@suspended Job PState H3 H4 H5 sched j t) <=
          @task_total_suspension Task H1 tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.DynamicSuspension.job_suspension_bounded : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Suspension.Dynamic.TaskTotalSuspension Task]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobArrival Job]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] [inst_6 : Prosa.Model.Readiness.Suspension.JobSuspension Job],
  Prosa.Model.Task.Suspension.Dynamic.valid_dynamic_suspensions →
    ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job) (sched : Prosa.Behavior.Schedule.schedule PState)
      (tsk : Task) (t1 : Prosa.Behavior.Time.instant) (Δ : Prosa.Behavior.Time.duration) (j : Job),
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        ∑ t ∈ Finset.Ico t1 (t1 + Δ), (Prosa.Model.Readiness.Suspension.suspended sched j t).toNat ≤
          Prosa.Model.Task.Suspension.Dynamic.task_total_suspension tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_DynamicSuspension_job_suspension_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (inst_23 : 
          Prosa_Model_Readiness_Suspension_JobSuspension Job
            inst_7),
       Prosa_Model_Task_Suspension_Dynamic_valid_dynamic_suspensions Job
         inst_7
         inst_20
         inst_23 Task
         inst_3
         inst_13
         inst_10 ->
       forall
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (tsk : Task) (t1 : Prosa_Behavior_Time_instant) (_UU0394_ : Prosa_Behavior_Time_duration) 
         (j : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_13 tsk j)
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat
               (fun t : Nat =>
                Bool_toNat
                  (Prosa_Model_Readiness_Suspension_suspended Job
                     inst_7 PState
                     inst_17
                     inst_20
                     inst_23 sched
                     j t))
               (List_range' t1
                  (Nat_sub
                     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                        Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                        t1 _UU0394_)
                     t1)
                  1)))
         (Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension_task_total_suspension Task
            inst_3
            inst_10 tsk)
```
