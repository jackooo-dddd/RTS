# `backlogged_job_has_lower_gel_prio`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.generality.gel.backlogged_job_has_lower_gel_prio`
- Lean: `Prosa.Results.Generality.Gel.backlogged_job_has_lower_gel_prio`
- Certificate: `backlogged_job_has_lower_gel_prio_correspondence`

## Official Rocq

```coq
backlogged_job_has_lower_gel_prio :
forall {Task : TaskType} {H : PriorityPoint Task} {Job : JobType} {H0 : JobTask Job Task}
  {PState : ProcessorState Job} {Arrival : JobArrival Job} {Cost : JobCost Job}
  {JR : @JobReady Job PState Cost Arrival} (j j' : Equality.sort Job) (sched : @schedule Job PState)
  (t : instant),
is_true (0 <= @pp_delta Task H (@job_task Job Task H0 j) (@job_task Job Task H0 j'))%R ->
is_true
  (@job_response_time_bound Job PState sched Cost Arrival j'
     `|@pp_delta Task H (@job_task Job Task H0 j) (@job_task Job Task H0 j')|) ->
is_true (@has_arrived Job Arrival j t) ->
is_true (@backlogged Job PState Cost Arrival JR sched j' t) ->
is_true (@hep_job Job (@GEL Job Task H Arrival H0) j j')

backlogged_job_has_lower_gel_prio is not universe polymorphic
Arguments backlogged_job_has_lower_gel_prio {Task H Job H0 PState Arrival Cost JR} 
  j j' sched t H_delta_pos H_rt_bound _ _
backlogged_job_has_lower_gel_prio is opaque
Expands to: Constant prosa.results.generality.gel.backlogged_job_has_lower_gel_prio
Declared in library prosa.results.generality.gel, line 151, characters 12-45
@backlogged_job_has_lower_gel_prio
     : forall (Task : TaskType) (H : PriorityPoint Task) (Job : JobType) (H0 : JobTask Job Task)
         (PState : ProcessorState Job) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (JR : @JobReady Job PState Cost Arrival) (j j' : Equality.sort Job) (sched : @schedule Job PState)
         (t : instant),
       is_true (0 <= @pp_delta Task H (@job_task Job Task H0 j) (@job_task Job Task H0 j'))%R ->
       is_true
         (@job_response_time_bound Job PState sched Cost Arrival j'
            `|@pp_delta Task H (@job_task Job Task H0 j) (@job_task Job Task H0 j')|) ->
       is_true (@has_arrived Job Arrival j t) ->
       is_true (@backlogged Job PState Cost Arrival JR sched j' t) ->
       is_true (@hep_job Job (@GEL Job Task H Arrival H0) j j')
```

## Lean

```lean
@Prosa.Results.Generality.Gel.backlogged_job_has_lower_gel_prio : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Priority.Gel.PriorityPoint Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [Arrival : Prosa.Behavior.Job.JobArrival Job]
  [Cost : Prosa.Behavior.Job.JobCost Job] [JR : Prosa.Behavior.Ready.JobReady Job PState] (j j' : Job)
  (sched : Prosa.Behavior.Schedule.schedule PState) (t : Prosa.Behavior.Time.instant),
  decide
        (0 ≤
          Prosa.Results.Generality.Gel.pp_delta (Prosa.Model.Task.Concept.job_task j)
            (Prosa.Model.Task.Concept.job_task j')) =
      true →
    Prosa.Behavior.Service.job_response_time_bound sched j'
          (Prosa.Results.Generality.Gel.pp_delta (Prosa.Model.Task.Concept.job_task j)
              (Prosa.Model.Task.Concept.job_task j')).natAbs =
        true →
      Prosa.Behavior.Arrival_sequence.has_arrived j t = true →
        Prosa.Behavior.Ready.backlogged sched j' t = true → Prosa.Model.Priority.Definitions.hep_job j j' = true
```

## Lean, imported into Rocq

```coq
Prosa_Results_Generality_Gel_backlogged_job_has_lower_gel_prio
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
         (JR : Prosa_Behavior_Ready_JobReady Job
                 inst_7 PState Cost Arrival)
         (j j' : Job)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (t : Prosa_Behavior_Time_instant),
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
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_has_arrived Job
            inst_7 Arrival j t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Ready_backlogged Job
            inst_7 PState Cost Arrival JR sched j'
            t)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_7
            (Prosa_Model_Priority_Gel_GEL Job
               inst_7 Task
               inst_3
               inst_10 Arrival
               inst_13)
            j j')
         Bool_true
```
