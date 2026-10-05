# `no_intra_interference_after_F`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.abstract_rta.no_intra_interference_after_F`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.no_intra_interference_after_F`
- Certificate: `no_intra_interference_after_F_correspondence`

## Official Rocq

```coq
no_intra_interference_after_F :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {Job : JobType} {H1 : JobTask Job Task} {H2 : JobArrival Job} {H3 : JobCost Job} 
  {H4 : JobPreemptable Job} {PState : ProcessorState Job},
@fully_consuming_proc_model Job PState ->
forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (ts : seq (Equality.sort Task))
  (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
@valid_preemption_model Job H3 H4 PState arr_seq sched ->
@valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
forall {H5 : Interference Job} {H6 : InterferingWorkload Job},
@work_conserving Job H2 H3 PState arr_seq sched H5 H6 ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H1 tsk j) ->
is_true (@job_cost_positive Job H3 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H2 H3 PState sched H5 H6 j t1 t2 ->
forall Δ : duration,
is_true (t1 + Δ < t2) ->
is_true (~~ @completed_by Job PState sched H3 j (t1 + Δ)) ->
forall F : duration,
is_true (F <= Δ) ->
is_true (@task_rtct Task H0 tsk <= @service Job PState sched j (t1 + F)) ->
@cumul_intra_interference Job PState sched H5 j (t1 + F) (t1 + Δ) = 0

no_intra_interference_after_F is not universe polymorphic
Arguments no_intra_interference_after_F {Task H H0 Job H1 H2 H3 H4 PState} H_consumed_supply_proc_model
  arr_seq sched ts%seq_scope tsk H_tsk_in_ts H_valid_preemption_model H_valid_run_to_completion_threshold
  {H5 H6} H_work_conserving j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 
  H_busy_interval Δ H_inside_busy_interval H_job_j_is_not_completed F H_F_le_Δ H_enough_service
no_intra_interference_after_F is opaque
Expands to: Constant prosa.analysis.abstract.restricted_supply.abstract_rta.no_intra_interference_after_F
Declared in library prosa.analysis.abstract.restricted_supply.abstract_rta, line 219, characters 10-39
@no_intra_interference_after_F
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H2 : JobArrival Job) (H3 : JobCost Job)
         (H4 : JobPreemptable Job) (PState : ProcessorState Job),
       @fully_consuming_proc_model Job PState ->
       forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (ts : seq (Equality.sort Task))
         (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       @valid_preemption_model Job H3 H4 PState arr_seq sched ->
       @valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
       forall (H5 : Interference Job) (H6 : InterferingWorkload Job),
       @work_conserving Job H2 H3 PState arr_seq sched H5 H6 ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H1 tsk j) ->
       is_true (@job_cost_positive Job H3 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H2 H3 PState sched H5 H6 j t1 t2 ->
       forall Δ : duration,
       is_true (t1 + Δ < t2) ->
       is_true (~~ @completed_by Job PState sched H3 j (t1 + Δ)) ->
       forall F : duration,
       is_true (F <= Δ) ->
       is_true (@task_rtct Task H0 tsk <= @service Job PState sched j (t1 + F)) ->
       @cumul_intra_interference Job PState sched H5 j (t1 + F) (t1 + Δ) = 0
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.no_intra_interference_after_F : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobArrival Job]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
      (ts : List Task) (tsk : Task),
      decide (tsk ∈ ts) = true →
        Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
          Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
            ∀ [inst_8 : Prosa.Analysis.Abstract.Definitions.Interference Job]
              [inst_9 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
              Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                ∀ (j : Job),
                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                    Prosa.Model.Task.Concept.job_of_task tsk j = true →
                      Prosa.Model.Job.Properties.job_cost_positive j = true →
                        ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                          Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2 →
                            ∀ (Δ : Prosa.Behavior.Time.duration),
                              t1 + Δ < t2 →
                                (!Prosa.Behavior.Service.completed_by sched j (t1 + Δ)) = true →
                                  ∀ F ≤ Δ,
                                    Prosa.Model.Task.Preemption.Parameters.task_rtct tsk ≤
                                        Prosa.Behavior.Service.service sched j (t1 + F) →
                                      Prosa.Analysis.Abstract.IBF.Supply.cumul_intra_interference sched j (t1 + F)
                                          (t1 + Δ) =
                                        0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_no_intra_interference_after_F
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
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
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_7 PState ->
       forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7
                    PState)
         (ts : List Task) (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_7
         inst_23
         inst_26 PState
         arr_seq sched ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_10 Job
         inst_7
         inst_16
         inst_23
         inst_26
         inst_13 arr_seq
         tsk ->
       forall
         (inst_66 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_7)
         (inst_69 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_7),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_7
         inst_66
         inst_69
         inst_20
         inst_23 PState
         arr_seq sched ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_16 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_7
            inst_23 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
         inst_7
         inst_66
         inst_69
         inst_20
         inst_23 PState
         sched j t1 t2 ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)
         t2 ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_7
               PState sched
               inst_23 j
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  _UU0394_)))
         Bool_true ->
       forall F : Prosa_Behavior_Time_duration,
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat F _UU0394_ ->
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
            inst_3
            inst_13 tsk)
         (Prosa_Behavior_Service_service Job
            inst_7 PState
            sched j
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 F)) ->
       @eq Nat
         (Prosa_Analysis_Abstract_IBF_Supply_cumul_intra_interference Job
            inst_7 PState
            sched inst_66
            j
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 F)
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               _UU0394_))
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
```
