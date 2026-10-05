# `cumulative_task_interference_split`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_task_interference_split`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.cumulative_task_interference_split`
- Certificate: `cumulative_task_interference_split_correspondence`

## Official Rocq

```coq
cumulative_task_interference_split :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {H2 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall {JobReady0 : @JobReady Job PState H2 H1} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
forall {JLFP : JLFP_policy Job} (tsk : Equality.sort Task) (j : Equality.sort Job) (t1 : nat) (t2 : instant),
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H0 tsk j) ->
is_true (~~ @completed_by Job PState sched H2 j t2) ->
is_true
  (@cumul_cond_interference Job
     (@rs_readiness_jlfp_interference Job H1 H2 PState JobReady0 arr_seq sched JLFP)
     (@nonself_intra Job Task H0 PState arr_seq sched) j t1 t2 <=
   @cumulative_another_task_hep_job_interference Task Job H0 PState arr_seq sched JLFP j t1 t2 +
   @cumulative_service_inversion Job H1 H2 PState JobReady0 arr_seq sched JLFP j t1 t2 +
   (fun (j0 : Equality.sort Job) (t3 t4 : instant) =>
    \sum_(t3 <= t < t4)
       nat_of_bool
         (@has_supply Job PState sched t &&
          ~~ @some_hep_job_ready Job H1 H2 PState JobReady0 arr_seq sched JLFP j0 t))
     j t1 t2)

cumulative_task_interference_split is not universe polymorphic
Arguments cumulative_task_interference_split {Task Job H0 H1 H2 PState} H_uniprocessor_proc_model
  H_consumed_supply_proc_model {JobReady0} arr_seq H_valid_arrival_sequence sched 
  H_valid_schedule {JLFP} tsk j t1%nat_scope t2 _ _ _
cumulative_task_interference_split is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_task_interference_split
Declared in library prosa.analysis.abstract.restricted_supply.iw_readiness, line 156, characters 8-42
@cumulative_task_interference_split
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (H2 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall (JobReady0 : @JobReady Job PState H2 H1) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       forall (JLFP : JLFP_policy Job) (tsk : Equality.sort Task) (j : Equality.sort Job) 
         (t1 : nat) (t2 : instant),
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H0 tsk j) ->
       is_true (~~ @completed_by Job PState sched H2 j t2) ->
       is_true
         (@cumul_cond_interference Job
            (@rs_readiness_jlfp_interference Job H1 H2 PState JobReady0 arr_seq sched JLFP)
            (@nonself_intra Job Task H0 PState arr_seq sched) j t1 t2 <=
          @cumulative_another_task_hep_job_interference Task Job H0 PState arr_seq sched JLFP j t1 t2 +
          @cumulative_service_inversion Job H1 H2 PState JobReady0 arr_seq sched JLFP j t1 t2 +
          \sum_(t1 <= t < t2)
             nat_of_bool
               (@has_supply Job PState sched t &&
                ~~ @some_hep_job_ready Job H1 H2 PState JobReady0 arr_seq sched JLFP j t))
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.cumulative_task_interference_split : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
      ∀ [JobReady0 : Prosa.Behavior.Ready.JobReady Job PState]
        (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
              ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] (tsk : Task) (j : Job) (t1 : ℕ)
                (t2 : Prosa.Behavior.Time.instant),
                Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                  Prosa.Model.Task.Concept.job_of_task tsk j = true →
                    (!Prosa.Behavior.Service.completed_by sched j t2) = true →
                      Prosa.Analysis.Abstract.Definitions.cumul_cond_interference
                          (Prosa.Analysis.Abstract.IBF.SupplyTask.nonself_intra arr_seq sched) j t1 t2 ≤
                        Prosa.Analysis.Definitions.Interference.cumulative_another_task_hep_job_interference arr_seq
                              sched j t1 t2 +
                            Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.cumulative_service_inversion
                              arr_seq sched j t1 t2 +
                          ∑ t ∈ Finset.Ico t1 t2,
                            (Prosa.Model.Processor.Supply.has_supply sched t &&
                                !Prosa.Analysis.Definitions.ReadinessInterference.some_hep_job_ready arr_seq sched j
                                    t).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_cumulative_task_interference_split
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_7 PState ->
       forall
         (JobReady0 : Prosa_Behavior_Ready_JobReady Job
                        inst_7
                        PState
                        inst_17
                        inst_14)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7
                   PState,
       Prosa_Behavior_Ready_valid_schedule Job
         inst_7
         inst_14 PState
         sched inst_17
         JobReady0 arr_seq ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7)
         (tsk : Task) (j : Job) (t1 : Nat) (t2 : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_7
               PState sched
               inst_17 j t2))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
            inst_7
            (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interference Job
               inst_7
               inst_14
               inst_17
               PState JobReady0 arr_seq sched JLFP)
            (Prosa_Analysis_Abstract_IBF_SupplyTask_nonself_intra Job
               inst_7 Task
               inst_3
               inst_10
               PState arr_seq sched)
            j t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
               (Prosa_Analysis_Definitions_Interference_cumulative_another_task_hep_job_interference Task
                  inst_3
                  Job
                  inst_7
                  inst_10
                  PState arr_seq sched JLFP j t1 t2)
               (Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_cumulative_service_inversion Job
                  inst_7
                  inst_14
                  inst_17
                  PState JobReady0 arr_seq sched JLFP j t1 t2))
            (List_foldr_inst3 Nat Nat Nat_add 0
               (List_map_inst3 Nat Nat
                  (fun t : Nat =>
                   Bool_toNat
                     (Bool_and
                        (Prosa_Model_Processor_Supply_has_supply Job
                           inst_7
                           PState sched t)
                        (Bool_not
                           (Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready Job
                              inst_7
                              inst_14
                              inst_17
                              PState JobReady0 arr_seq sched JLFP j t))))
                  (List_range' t1 (Nat_sub t2 t1) 1))))
```
