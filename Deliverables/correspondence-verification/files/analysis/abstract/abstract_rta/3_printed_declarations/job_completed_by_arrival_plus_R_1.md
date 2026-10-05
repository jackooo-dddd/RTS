# `job_completed_by_arrival_plus_R_1`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.abstract_rta.job_completed_by_arrival_plus_R_1`
- Lean: `Prosa.Analysis.Abstract.AbstractRta.job_completed_by_arrival_plus_R_1`
- Certificate: `job_completed_by_arrival_plus_R_1_correspondence`

## Official Rocq

```coq
job_completed_by_arrival_plus_R_1 :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H2 : JobArrival Job} 
  {jc : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (tsk : Equality.sort Task) {H3 : Interference Job} {H4 : InterferingWorkload Job}
  (IBF_NP : duration -> duration -> duration),
(forall (F : nat) (Δ : duration), is_true (F <= @task_cost Task H tsk + IBF_NP F Δ)) ->
forall (R : duration) (j : Equality.sort Job) (t1 t2 : instant),
@busy_interval Job H2 jc PState sched H3 H4 j t1 t2 ->
forall A_sp : duration,
is_true (A_sp <= @job_arrival Job H2 j - t1) ->
forall F : duration,
is_true (@task_cost Task H tsk + IBF_NP F (A_sp + R) <= A_sp + R) ->
is_true (t2 <= t1 + F) -> is_true (@completed_by Job PState sched jc j (@job_arrival Job H2 j + R))

job_completed_by_arrival_plus_R_1 is not universe polymorphic
Arguments job_completed_by_arrival_plus_R_1 {Task H Job H2 jc PState} sched tsk {H3 H4}
  (IBF_NP H_IBF_NP_ge_param)%function_scope R j t1 t2 H_busy_interval A_sp H_Asp_le_A 
  F H_Asp_R_fixpoint H_big_fixpoint_solution
job_completed_by_arrival_plus_R_1 is opaque
Expands to: Constant prosa.analysis.abstract.abstract_rta.job_completed_by_arrival_plus_R_1
Declared in library prosa.analysis.abstract.abstract_rta, line 291, characters 12-45
@job_completed_by_arrival_plus_R_1
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H2 : JobArrival Job) 
         (jc : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (tsk : Equality.sort Task) (H3 : Interference Job) (H4 : InterferingWorkload Job)
         (IBF_NP : duration -> duration -> duration),
       (forall (F : nat) (Δ : duration), is_true (F <= @task_cost Task H tsk + IBF_NP F Δ)) ->
       forall (R : duration) (j : Equality.sort Job) (t1 t2 : instant),
       @busy_interval Job H2 jc PState sched H3 H4 j t1 t2 ->
       forall A_sp : duration,
       is_true (A_sp <= @job_arrival Job H2 j - t1) ->
       forall F : duration,
       is_true (@task_cost Task H tsk + IBF_NP F (A_sp + R) <= A_sp + R) ->
       is_true (t2 <= t1 + F) -> is_true (@completed_by Job PState sched jc j (@job_arrival Job H2 j + R))
```

## Lean

```lean
@Prosa.Analysis.Abstract.AbstractRta.job_completed_by_arrival_plus_R_1 : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (tsk : Task)
  [inst_5 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_6 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
  (IBF_NP : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
  (∀ (F : ℕ) (Δ : Prosa.Behavior.Time.duration), F ≤ Prosa.Model.Task.Concept.task_cost tsk + IBF_NP F Δ) →
    ∀ (R : Prosa.Behavior.Time.duration) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
      Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
        ∀ A_sp ≤ Prosa.Behavior.Job.job_arrival j - t1,
          ∀ (F : Prosa.Behavior.Time.duration),
            Prosa.Model.Task.Concept.task_cost tsk + IBF_NP F (A_sp + R) ≤ A_sp + R →
              t2 ≤ t1 + F → Prosa.Behavior.Service.completed_by sched j (Prosa.Behavior.Job.job_arrival j + R) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_AbstractRta_job_completed_by_arrival_plus_R_1
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job)
         (inst_13 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (inst_16 : 
          Prosa_Behavior_Job_JobCost Job
            inst_10)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_10)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_10 PState)
         (tsk : Task)
         (inst_24 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_10)
         (inst_27 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_10)
         (IBF_NP : Prosa_Behavior_Time_duration ->
                   Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration),
       (forall (F : Nat) (_UU0394_ : Prosa_Behavior_Time_duration),
        LE_le_inst1 Nat instLENat F
          (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
             Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
             (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                inst_3
                inst_6 tsk)
             (IBF_NP F _UU0394_))) ->
       forall (R : Prosa_Behavior_Time_duration) (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_10
         inst_24
         inst_27
         inst_13
         inst_16 PState sched j t1 t2 ->
       forall A_sp : Prosa_Behavior_Time_duration,
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat A_sp
         (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
            (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
            (Prosa_Behavior_Job_JobArrival_job_arrival Job
               inst_10
               inst_13 j)
            t1) ->
       forall F : Prosa_Behavior_Time_duration,
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
               inst_3
               inst_6 tsk)
            (IBF_NP F
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A_sp
                  R)))
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A_sp R) ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t2
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 F) ->
       @eq Bool
         (Prosa_Behavior_Service_completed_by Job
            inst_10 PState sched
            inst_16 j
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_10
                  inst_13 j)
               R))
         Bool_true
```
