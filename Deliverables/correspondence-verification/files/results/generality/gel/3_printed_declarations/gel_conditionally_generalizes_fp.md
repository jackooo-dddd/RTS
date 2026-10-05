# `gel_conditionally_generalizes_fp`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.generality.gel.gel_conditionally_generalizes_fp`
- Lean: `Prosa.Results.Generality.Gel.gel_conditionally_generalizes_fp`
- Certificate: `gel_conditionally_generalizes_fp_correspondence`

## Official Rocq

```coq
gel_conditionally_generalizes_fp :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H0 : JobTask Job Task}
  {PState : ProcessorState Job} {Arrival : JobArrival Job} {Cost : JobCost Job} {H1 : JobPreemptable Job}
  {JR : @JobReady Job PState Cost Arrival} (fp : FP_policy Task),
@reflexive_task_priorities Task fp ->
@total_task_priorities Task fp ->
forall arr_seq : arrival_sequence Job,
(forall j j' : Equality.sort Job,
 @arrives_in Job arr_seq j ->
 @arrives_in Job arr_seq j' ->
 is_true (~~ @same_task Job Task H0 j j') ->
 is_true (@hep_task Task fp (@job_task Job Task H0 j) (@job_task Job Task H0 j')) ->
 is_true (@hp_task Task fp (@job_task Job Task H0 j) (@job_task Job Task H0 j'))) ->
(forall j j' : Equality.sort Job,
 @arrives_in Job arr_seq j ->
 @arrives_in Job arr_seq j' ->
 is_true (@hp_task Task fp (@job_task Job Task H0 j) (@job_task Job Task H0 j')) ->
 is_true (0 <= @pp_delta Task H (@job_task Job Task H0 j) (@job_task Job Task H0 j'))%R) ->
forall sched : @schedule Job PState,
@valid_schedule Job Arrival PState sched Cost JR arr_seq ->
(forall j j' : Equality.sort Job,
 @arrives_in Job arr_seq j ->
 @arrives_in Job arr_seq j' ->
 is_true (@hp_task Task fp (@job_task Job Task H0 j) (@job_task Job Task H0 j')) ->
 is_true
   (@job_response_time_bound Job PState sched Cost Arrival j'
      `|@pp_delta Task H (@job_task Job Task H0 j) (@job_task Job Task H0 j')|)) ->
@sequential_tasks Job Task H0 Arrival Cost PState arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H1 JR arr_seq sched
  (@GEL Job Task H Arrival H0) <->
@respects_FP_policy_at_preemption_point Task Job H0 Arrival Cost PState H1 JR arr_seq sched fp

gel_conditionally_generalizes_fp is not universe polymorphic
Arguments gel_conditionally_generalizes_fp {Task H Job H0 PState Arrival Cost H1 JR} 
  fp H_reflexive H_total arr_seq (H_unique_fixed_priorities H_hp_delta_pos)%function_scope 
  sched H_sched_valid H_hp_delta_rtb%function_scope H_sequential
gel_conditionally_generalizes_fp is opaque
Expands to: Constant prosa.results.generality.gel.gel_conditionally_generalizes_fp
Declared in library prosa.results.generality.gel, line 220, characters 12-44
@gel_conditionally_generalizes_fp
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H0 : JobTask Job Task)
         (PState : ProcessorState Job) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (H1 : JobPreemptable Job) (JR : @JobReady Job PState Cost Arrival) (fp : FP_policy Task),
       @reflexive_task_priorities Task fp ->
       @total_task_priorities Task fp ->
       forall arr_seq : arrival_sequence Job,
       (forall j j' : Equality.sort Job,
        @arrives_in Job arr_seq j ->
        @arrives_in Job arr_seq j' ->
        is_true (~~ @same_task Job Task H0 j j') ->
        is_true (@hep_task Task fp (@job_task Job Task H0 j) (@job_task Job Task H0 j')) ->
        is_true (@hp_task Task fp (@job_task Job Task H0 j) (@job_task Job Task H0 j'))) ->
       (forall j j' : Equality.sort Job,
        @arrives_in Job arr_seq j ->
        @arrives_in Job arr_seq j' ->
        is_true (@hp_task Task fp (@job_task Job Task H0 j) (@job_task Job Task H0 j')) ->
        is_true (0 <= @pp_delta Task H (@job_task Job Task H0 j) (@job_task Job Task H0 j'))%R) ->
       forall sched : @schedule Job PState,
       @valid_schedule Job Arrival PState sched Cost JR arr_seq ->
       (forall j j' : Equality.sort Job,
        @arrives_in Job arr_seq j ->
        @arrives_in Job arr_seq j' ->
        is_true (@hp_task Task fp (@job_task Job Task H0 j) (@job_task Job Task H0 j')) ->
        is_true
          (@job_response_time_bound Job PState sched Cost Arrival j'
             `|@pp_delta Task H (@job_task Job Task H0 j) (@job_task Job Task H0 j')|)) ->
       @sequential_tasks Job Task H0 Arrival Cost PState arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H1 JR arr_seq sched
         (@GEL Job Task H Arrival H0) <->
       @respects_FP_policy_at_preemption_point Task Job H0 Arrival Cost PState H1 JR arr_seq sched fp
New coercion path [GRing.subring_closedM; GRing.smulr_closedN] : GRing.subring_closed >-> GRing.oppr_closed is ambiguous with existing 
New coercion path [GRing.subring_closed_semi; GRing.semiring_closedM] : GRing.subring_closed >-> GRing.mulr_closed is ambiguous with existing 
New coercion path [GRing.subring_closed_semi; GRing.semiring_closedD] : GRing.subring_closed >-> GRing.addr_closed is ambiguous with existing 
New coercion path [GRing.submod_closed_semi; GRing.subsemimod_closedD] : GRing.submod_closed >-> GRing.addr_closed is ambiguous with existing 
New coercion path [GRing.subalg_closedBM; GRing.subring_closedB] : GRing.subalg_closed >-> GRing.zmod_closed is ambiguous with existing 
New coercion path [GRing.sdivr_closedM; GRing.smulr_closedM] : GRing.sdivr_closed >-> GRing.mulr_closed is ambiguous with existing 
New coercion path [GRing.divring_closed_div; GRing.sdivr_closedM] : GRing.divring_closed >-> GRing.smulr_closed is ambiguous with existing 
New coercion path [GRing.divalg_closedZ; GRing.subalg_closedBM] : GRing.divalg_closed >-> GRing.subring_closed is ambiguous with existing
```

## Lean

```lean
@Prosa.Results.Generality.Gel.gel_conditionally_generalizes_fp : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [Arrival : Prosa.Behavior.Job.JobArrival Job]
  [Cost : Prosa.Behavior.Job.JobCost Job] [inst_4 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  [JR : Prosa.Behavior.Ready.JobReady Job PState] (fp : Prosa.Model.Priority.Definitions.FP_policy Task),
  Prosa.Model.Priority.Definitions.reflexive_task_priorities fp →
    Prosa.Model.Priority.Definitions.total_task_priorities fp →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        (∀ (j j' : Job),
            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j' →
                (!Prosa.Model.Task.Concept.same_task j j') = true →
                  Prosa.Model.Priority.Definitions.hep_task (Prosa.Model.Task.Concept.job_task j)
                        (Prosa.Model.Task.Concept.job_task j') =
                      true →
                    Prosa.Model.Priority.Definitions.hp_task (Prosa.Model.Task.Concept.job_task j)
                        (Prosa.Model.Task.Concept.job_task j') =
                      true) →
          (∀ (j j' : Job),
              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j' →
                  Prosa.Model.Priority.Definitions.hp_task (Prosa.Model.Task.Concept.job_task j)
                        (Prosa.Model.Task.Concept.job_task j') =
                      true →
                    decide
                        (0 ≤
                          Prosa.Results.Generality.Gel.pp_delta (Prosa.Model.Task.Concept.job_task j)
                            (Prosa.Model.Task.Concept.job_task j')) =
                      true) →
            ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
              Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                (∀ (j j' : Job),
                    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j' →
                        Prosa.Model.Priority.Definitions.hp_task (Prosa.Model.Task.Concept.job_task j)
                              (Prosa.Model.Task.Concept.job_task j') =
                            true →
                          Prosa.Behavior.Service.job_response_time_bound sched j'
                              (Prosa.Results.Generality.Gel.pp_delta (Prosa.Model.Task.Concept.job_task j)
                                  (Prosa.Model.Task.Concept.job_task j')).natAbs =
                            true) →
                  Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched →
                    (Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                        (Prosa.Model.Priority.Gel.GEL Job Task) ↔
                      Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq sched fp)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Generality_Gel_gel_conditionally_generalizes_fp
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : Prosa_Model_Priority_Gel_PriorityPoint
                                                                                Task
                                                                                inst_3)
         (inst_13 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (Arrival : Prosa_Behavior_Job_JobArrival Job
                      inst_7)
         (Cost : Prosa_Behavior_Job_JobCost Job
                   inst_7)
         (inst_23 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                                Job
                                                                                inst_7)
         (JR : Prosa_Behavior_Ready_JobReady Job
                 inst_7 PState Cost Arrival)
         (fp : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 fp ->
       Prosa_Model_Priority_Definitions_total_task_priorities Task
         inst_3 fp ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       (forall j j' : Job,
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_7 arr_seq j ->
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_7 arr_seq j' ->
        @eq Bool
          (Bool_not
             (Prosa_Model_Task_Concept_same_task Job
                inst_7 Task
                inst_3
                inst_13 j j'))
          Bool_true ->
        @eq Bool
          (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
             inst_3 fp
             (Prosa_Model_Task_Concept_JobTask_job_task Job
                inst_7 Task
                inst_3
                inst_13 j)
             (Prosa_Model_Task_Concept_JobTask_job_task Job
                inst_7 Task
                inst_3
                inst_13 j'))
          Bool_true ->
        @eq Bool
          (Prosa_Model_Priority_Definitions_hp_task Task
             inst_3 fp
             (Prosa_Model_Task_Concept_JobTask_job_task Job
                inst_7 Task
                inst_3
                inst_13 j)
             (Prosa_Model_Task_Concept_JobTask_job_task Job
                inst_7 Task
                inst_3
                inst_13 j'))
          Bool_true) ->
       (forall j j' : Job,
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_7 arr_seq j ->
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_7 arr_seq j' ->
        @eq Bool
          (Prosa_Model_Priority_Definitions_hp_task Task
             inst_3 fp
             (Prosa_Model_Task_Concept_JobTask_job_task Job
                inst_7 Task
                inst_3
                inst_13 j)
             (Prosa_Model_Task_Concept_JobTask_job_task Job
                inst_7 Task
                inst_3
                inst_13 j'))
          Bool_true ->
        @eq Bool
          (Decidable_decide
             (LE_le_inst1 Int Int_instLEInt (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
                (Prosa_Results_Generality_Gel_pp_delta Task
                   inst_3
                   inst_10
                   (Prosa_Model_Task_Concept_JobTask_job_task Job
                      inst_7 Task
                      inst_3
                      inst_13 j)
                   (Prosa_Model_Task_Concept_JobTask_job_task Job
                      inst_7 Task
                      inst_3
                      inst_13 j')))
             (Int_decLe (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
                (Prosa_Results_Generality_Gel_pp_delta Task
                   inst_3
                   inst_10
                   (Prosa_Model_Task_Concept_JobTask_job_task Job
                      inst_7 Task
                      inst_3
                      inst_13 j)
                   (Prosa_Model_Task_Concept_JobTask_job_task Job
                      inst_7 Task
                      inst_3
                      inst_13 j'))))
          Bool_true) ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7 PState,
       Prosa_Behavior_Ready_valid_schedule Job
         inst_7 Arrival PState sched Cost JR
         arr_seq ->
       (forall j j' : Job,
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_7 arr_seq j ->
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_7 arr_seq j' ->
        @eq Bool
          (Prosa_Model_Priority_Definitions_hp_task Task
             inst_3 fp
             (Prosa_Model_Task_Concept_JobTask_job_task Job
                inst_7 Task
                inst_3
                inst_13 j)
             (Prosa_Model_Task_Concept_JobTask_job_task Job
                inst_7 Task
                inst_3
                inst_13 j'))
          Bool_true ->
        @eq Bool
          (Prosa_Behavior_Service_job_response_time_bound Job
             inst_7 PState sched Cost Arrival j'
             (Int_natAbs
                (Prosa_Results_Generality_Gel_pp_delta Task
                   inst_3
                   inst_10
                   (Prosa_Model_Task_Concept_JobTask_job_task Job
                      inst_7 Task
                      inst_3
                      inst_13 j)
                   (Prosa_Model_Task_Concept_JobTask_job_task Job
                      inst_7 Task
                      inst_3
                      inst_13 j'))))
          Bool_true) ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_7 Task
         inst_3
         inst_13 Arrival Cost PState arr_seq sched ->
       Iff
         (Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
            inst_7 Arrival Cost PState
            inst_23 JR arr_seq sched
            (Prosa_Model_Priority_Gel_GEL Job
               inst_7 Task
               inst_3
               inst_10 Arrival
               inst_13))
         (Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point Task
            inst_3 Job
            inst_7
            inst_13 Arrival Cost PState
            inst_23 JR arr_seq sched fp)
```
