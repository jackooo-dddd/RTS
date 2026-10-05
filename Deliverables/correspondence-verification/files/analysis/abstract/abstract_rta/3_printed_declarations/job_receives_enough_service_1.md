# `job_receives_enough_service_1`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.abstract_rta.job_receives_enough_service_1`
- Lean: `Prosa.Analysis.Abstract.AbstractRta.job_receives_enough_service_1`
- Certificate: `job_receives_enough_service_1_correspondence`

## Official Rocq

```coq
job_receives_enough_service_1 :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {Job : JobType} {H1 : JobTask Job Task} {H2 : JobArrival Job} {jc : JobCost Job}
  {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall {H3 : Interference Job} {H4 : InterferingWorkload Job},
@work_conserving Job H2 jc PState arr_seq sched H3 H4 ->
forall L : duration,
@busy_intervals_are_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H3 H4 L ->
forall IBF_P : duration -> duration -> duration,
@job_interference_is_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H3 H4 IBF_P
  (@relative_arrival_time_of_job_is_A Job H2 jc PState sched H3 H4) ->
forall (IBF_NP : duration -> duration -> duration) (R : duration) (j : Equality.sort Job),
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H1 tsk j) ->
is_true (@job_cost_positive Job jc j) ->
forall t1 t2 : instant,
@busy_interval Job H2 jc PState sched H3 H4 j t1 t2 ->
forall A_sp : duration,
is_true (A_sp <= @job_arrival Job H2 j - t1) ->
@are_equivalent_at_values_less_than Datatypes_nat__canonical__eqtype_Equality
  (IBF_P (@job_arrival Job H2 j - t1)) (IBF_P A_sp) L ->
forall F : duration,
is_true (@task_rtct Task H0 tsk + IBF_P A_sp F <= F) ->
is_true (@task_cost Task H tsk + IBF_NP F (A_sp + R) <= A_sp + R) ->
is_true (t1 + F < t2) ->
is_true (t1 + (A_sp + R) < t2) ->
is_true (@job_cost Job jc j <= @task_rtct Task H0 tsk) ->
is_true (@job_cost Job jc j <= @service Job PState sched j (t1 + F))

job_receives_enough_service_1 is not universe polymorphic
Arguments job_receives_enough_service_1 {Task H H0 Job H1 H2 jc PState} arr_seq sched 
  ts%seq_scope tsk H_tsk_in_ts {H3 H4} H_work_conserving L H_bounded_busy_interval_exists
  IBF_P%function_scope H_job_interference_is_bounded_IBFP IBF_NP%function_scope R 
  j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval A_sp H_Asp_le_A 
  H_equivalent F H_F_fixpoint H_Asp_R_fixpoint H_small_fixpoint_solution1 H_small_fixpoint_solution2
  H_job_cost_is_small
job_receives_enough_service_1 is opaque
Expands to: Constant prosa.analysis.abstract.abstract_rta.job_receives_enough_service_1
Declared in library prosa.analysis.abstract.abstract_rta, line 374, characters 14-43
@job_receives_enough_service_1
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H2 : JobArrival Job) (jc : JobCost Job)
         (PState : ProcessorState Job) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
         (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall (H3 : Interference Job) (H4 : InterferingWorkload Job),
       @work_conserving Job H2 jc PState arr_seq sched H3 H4 ->
       forall L : duration,
       @busy_intervals_are_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H3 H4 L ->
       forall IBF_P : duration -> duration -> duration,
       @job_interference_is_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H3 H4 IBF_P
         (@relative_arrival_time_of_job_is_A Job H2 jc PState sched H3 H4) ->
       forall (IBF_NP : duration -> duration -> duration) (R : duration) (j : Equality.sort Job),
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H1 tsk j) ->
       is_true (@job_cost_positive Job jc j) ->
       forall t1 t2 : instant,
       @busy_interval Job H2 jc PState sched H3 H4 j t1 t2 ->
       forall A_sp : duration,
       is_true (A_sp <= @job_arrival Job H2 j - t1) ->
       @are_equivalent_at_values_less_than Datatypes_nat__canonical__eqtype_Equality
         (IBF_P (@job_arrival Job H2 j - t1)) (IBF_P A_sp) L ->
       forall F : duration,
       is_true (@task_rtct Task H0 tsk + IBF_P A_sp F <= F) ->
       is_true (@task_cost Task H tsk + IBF_NP F (A_sp + R) <= A_sp + R) ->
       is_true (t1 + F < t2) ->
       is_true (t1 + (A_sp + R) < t2) ->
       is_true (@job_cost Job jc j <= @task_rtct Task H0 tsk) ->
       is_true (@job_cost Job jc j <= @service Job PState sched j (t1 + F))
```

## Lean

```lean
@Prosa.Analysis.Abstract.AbstractRta.job_receives_enough_service_1 : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] [inst_6 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState) (ts : List Task) (tsk : Task),
  decide (tsk ∈ ts) = true →
    ∀ [inst_7 : Prosa.Analysis.Abstract.Definitions.Interference Job]
      [inst_8 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
      Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
        ∀ (L : Prosa.Behavior.Time.duration),
          Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by arr_seq sched tsk L →
            ∀ (IBF_P : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
              Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by arr_seq sched tsk IBF_P
                  (Prosa.Analysis.Abstract.AbstractRta.relative_arrival_time_of_job_is_A sched) →
                ∀ (IBF_NP : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration)
                  (R : Prosa.Behavior.Time.duration) (j : Job),
                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                    Prosa.Model.Task.Concept.job_of_task tsk j = true →
                      Prosa.Model.Job.Properties.job_cost_positive j = true →
                        ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                          Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
                            ∀ A_sp ≤ Prosa.Behavior.Job.job_arrival j - t1,
                              Prosa.Analysis.Abstract.SearchSpace.are_equivalent_at_values_less_than
                                  (IBF_P (Prosa.Behavior.Job.job_arrival j - t1)) (IBF_P A_sp) L →
                                ∀ (F : Prosa.Behavior.Time.duration),
                                  Prosa.Model.Task.Preemption.Parameters.task_rtct tsk + IBF_P A_sp F ≤ F →
                                    Prosa.Model.Task.Concept.task_cost tsk + IBF_NP F (A_sp + R) ≤ A_sp + R →
                                      t1 + F < t2 →
                                        t1 + (A_sp + R) < t2 →
                                          Prosa.Behavior.Job.job_cost j ≤
                                              Prosa.Model.Task.Preemption.Parameters.task_rtct tsk →
                                            Prosa.Behavior.Job.job_cost j ≤
                                              Prosa.Behavior.Service.service sched j (t1 + F)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_AbstractRta_job_receives_enough_service_1
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_13 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_13)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job
            inst_13)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_13)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_13 PState)
         (ts : List Task) (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3)
               tsk ts))
         Bool_true ->
       forall
         (inst_50 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_13)
         (inst_53 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_13),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_13
         inst_50
         inst_53
         inst_20
         inst_23 PState arr_seq sched ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by Job
         inst_13
         inst_50
         inst_53
         inst_20
         inst_23 PState arr_seq sched Task
         inst_3
         inst_16 tsk L ->
       forall
         IBF_P : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by Job
         inst_13
         inst_50
         inst_53
         inst_20
         inst_23 PState arr_seq sched Task
         inst_3
         inst_16 tsk IBF_P
         (Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A Job
            inst_13
            inst_20
            inst_23 PState sched
            inst_50
            inst_53) ->
       forall
         (IBF_NP : Prosa_Behavior_Time_duration ->
                   Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
         (R : Prosa_Behavior_Time_duration) (j : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_13 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_13 Task
            inst_3
            inst_16 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_13
            inst_23 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval Job
         inst_13
         inst_50
         inst_53
         inst_20
         inst_23 PState sched j t1 t2 ->
       forall A_sp : Prosa_Behavior_Time_duration,
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat A_sp
         (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
            (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
            (Prosa_Behavior_Job_JobArrival_job_arrival Job
               inst_13
               inst_20 j)
            t1) ->
       Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than_inst1
         Prosa_Behavior_Time_duration instDecidableEqNat
         (IBF_P
            (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_13
                  inst_20 j)
               t1))
         (IBF_P A_sp) L ->
       forall F : Prosa_Behavior_Time_duration,
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
            (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
            (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
               inst_3
               inst_9 tsk)
            (IBF_P A_sp F))
         F ->
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
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 F)
         t2 ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A_sp R))
         t2 ->
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_13
            inst_23 j)
         (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
            inst_3
            inst_9 tsk) ->
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_13
            inst_23 j)
         (Prosa_Behavior_Service_service Job
            inst_13 PState sched j
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 F))
```
