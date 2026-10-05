# `suspension_of_task_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.dynamic_suspension.suspension_of_task_bounded`
- Lean: `Prosa.Analysis.Facts.Model.DynamicSuspension.suspension_of_task_bounded`
- Certificate: `suspension_of_task_bounded_correspondence`

## Official Rocq

```coq
suspension_of_task_bounded :
forall {Task : TaskType} {H0 : MaxArrivals Task} {H1 : TaskTotalSuspension Task} 
  {Job : JobType} {H2 : JobTask Job Task} {H3 : JobArrival Job} {H4 : JobCost Job} 
  {H5 : JobSuspension Job},
@valid_dynamic_suspensions Job H4 H5 Task H2 H1 ->
forall (arr_seq : arrival_sequence Job) {PState : ProcessorState Job} (sched : @schedule Job PState)
  (tsk : Equality.sort Task) (t1 : instant) (Δ : duration),
@respects_max_arrivals Task Job H2 arr_seq tsk (@max_arrivals Task H0 tsk) ->
is_true
  (\sum_(t1 <= t < t1 + Δ)
      \sum_(j <- @task_arrivals_between Job Task H2 arr_seq tsk t1 (t1 + Δ))
         nat_of_bool (@suspended Job PState H3 H4 H5 sched j t) <=
   @max_arrivals Task H0 tsk Δ * @task_total_suspension Task H1 tsk)

suspension_of_task_bounded is not universe polymorphic
Arguments suspension_of_task_bounded {Task H0 H1 Job H2 H3 H4 H5} H_valid_dynamic_suspensions 
  arr_seq {PState} sched tsk t1 Δ H_tsk_respects_max_arrivals
suspension_of_task_bounded is opaque
Expands to: Constant prosa.analysis.facts.model.dynamic_suspension.suspension_of_task_bounded
Declared in library prosa.analysis.facts.model.dynamic_suspension, line 107, characters 8-34
@suspension_of_task_bounded
     : forall (Task : TaskType) (H0 : MaxArrivals Task) (H1 : TaskTotalSuspension Task) 
         (Job : JobType) (H2 : JobTask Job Task) (H3 : JobArrival Job) (H4 : JobCost Job)
         (H5 : JobSuspension Job),
       @valid_dynamic_suspensions Job H4 H5 Task H2 H1 ->
       forall (arr_seq : arrival_sequence Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (tsk : Equality.sort Task) (t1 : instant) (Δ : duration),
       @respects_max_arrivals Task Job H2 arr_seq tsk (@max_arrivals Task H0 tsk) ->
       is_true
         (\sum_(t1 <= t < t1 + Δ)
             \sum_(j <- @task_arrivals_between Job Task H2 arr_seq tsk t1 (t1 + Δ))
                nat_of_bool (@suspended Job PState H3 H4 H5 sched j t) <=
          @max_arrivals Task H0 tsk Δ * @task_total_suspension Task H1 tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.DynamicSuspension.suspension_of_task_bounded : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_3 : Prosa.Model.Task.Suspension.Dynamic.TaskTotalSuspension Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobArrival Job]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Model.Readiness.Suspension.JobSuspension Job],
  Prosa.Model.Task.Suspension.Dynamic.valid_dynamic_suspensions →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
      (PState : Prosa.Behavior.Schedule.ProcessorState Job) (sched : Prosa.Behavior.Schedule.schedule PState)
      (tsk : Task) (t1 : Prosa.Behavior.Time.instant) (Δ : Prosa.Behavior.Time.duration),
      Prosa.Model.Task.Arrival.Curves.respects_max_arrivals arr_seq tsk
          (Prosa.Model.Task.Arrival.Curves.max_arrivals tsk) →
        (∑ t ∈ Finset.Ico t1 (t1 + Δ),
            Prosa.Util.Sum.sumSeq (Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 (t1 + Δ)) fun j =>
              (Prosa.Model.Readiness.Suspension.suspended sched j t).toNat) ≤
          Prosa.Model.Task.Arrival.Curves.max_arrivals tsk Δ *
            Prosa.Model.Task.Suspension.Dynamic.task_total_suspension tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_DynamicSuspension_suspension_of_task_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension Task
            inst_3)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (inst_26 : 
          Prosa_Model_Readiness_Suspension_JobSuspension Job
            inst_7),
       Prosa_Model_Task_Suspension_Dynamic_valid_dynamic_suspensions Job
         inst_7
         inst_23
         inst_26 Task
         inst_3
         inst_16
         inst_13 ->
       forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (tsk : Task) (t1 : Prosa_Behavior_Time_instant) (_UU0394_ : Prosa_Behavior_Time_duration),
       Prosa_Model_Task_Arrival_Curves_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_16 arr_seq tsk
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_10 tsk) ->
       LE_le_inst1 Nat instLENat
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat
               (fun t : Nat =>
                Prosa_Util_Sum_sumSeq Job
                  (Prosa_Model_Task_Arrivals_task_arrivals_between Job
                     inst_7 Task
                     inst_3
                     inst_16
                     arr_seq tsk t1
                     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                        Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                        t1 _UU0394_))
                  (fun j : Job =>
                   Bool_toNat
                     (Prosa_Model_Readiness_Suspension_suspended Job
                        inst_7
                        PState
                        inst_20
                        inst_23
                        inst_26
                        sched j t)))
               (List_range' t1
                  (Nat_sub
                     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                        Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                        t1 _UU0394_)
                     t1)
                  1)))
         (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat)
            (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
               inst_3
               inst_10 tsk _UU0394_)
            (Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension_task_total_suspension Task
               inst_3
               inst_13 tsk))
```
