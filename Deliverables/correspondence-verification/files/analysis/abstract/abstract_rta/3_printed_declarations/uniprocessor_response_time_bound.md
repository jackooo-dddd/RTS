# `uniprocessor_response_time_bound`

- Kind (Rocq): Theorem
- Rocq: `prosa.analysis.abstract.abstract_rta.uniprocessor_response_time_bound`
- Lean: `Prosa.Analysis.Abstract.AbstractRta.uniprocessor_response_time_bound`
- Certificate: `uniprocessor_response_time_bound_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {Job : JobType} {H1 : JobTask Job Task} {H2 : JobArrival Job} {jc : JobCost Job}
  {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
@arrivals_have_valid_job_costs Task H Job H1 jc arr_seq ->
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall {H3 : Interference Job} {H4 : InterferingWorkload Job},
@work_conserving Job H2 jc PState arr_seq sched H3 H4 ->
forall L : duration,
@busy_intervals_are_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H3 H4 L ->
forall IBF_P : duration -> duration -> duration,
@job_interference_is_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H3 H4 IBF_P
  (@relative_arrival_time_of_job_is_A Job H2 jc PState sched H3 H4) ->
forall IBF_NP : duration -> duration -> duration,
@job_interference_is_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H3 H4 IBF_NP
  (@relative_time_to_reach_rtct Task H0 Job H2 jc PState sched tsk H3 H4 IBF_P) ->
(forall (F : nat) (Δ : duration), is_true (F <= @task_cost Task H tsk + IBF_NP F Δ)) ->
forall R : duration,
(forall A : duration,
 [eta is_in_search_space L IBF_P] A ->
 exists F : duration,
   is_true (@task_rtct Task H0 tsk + IBF_P A F <= F) /\
   is_true (@task_cost Task H tsk + IBF_NP F (A + R) <= A + R)) ->
@task_response_time_bound Task Job H2 jc H1 PState arr_seq sched tsk R

uniprocessor_response_time_bound is not universe polymorphic
Arguments uniprocessor_response_time_bound {Task H H0 Job H1 H2 jc PState} arr_seq 
  sched H_valid_job_cost ts%seq_scope tsk H_tsk_in_ts {H3 H4} H_work_conserving L
  H_bounded_busy_interval_exists IBF_P%function_scope H_job_interference_is_bounded_IBFP
  IBF_NP%function_scope H_job_interference_is_bounded_IBFNP H_IBF_NP_ge_param%function_scope 
  R H_R_is_maximum%function_scope j _ _
uniprocessor_response_time_bound is opaque
Expands to: Constant prosa.analysis.abstract.abstract_rta.uniprocessor_response_time_bound
Declared in library prosa.analysis.abstract.abstract_rta, line 463, characters 10-42
@uniprocessor_response_time_bound
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H2 : JobArrival Job) (jc : JobCost Job)
         (PState : ProcessorState Job) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
       @arrivals_have_valid_job_costs Task H Job H1 jc arr_seq ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall (H3 : Interference Job) (H4 : InterferingWorkload Job),
       @work_conserving Job H2 jc PState arr_seq sched H3 H4 ->
       forall L : duration,
       @busy_intervals_are_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H3 H4 L ->
       forall IBF_P : duration -> duration -> duration,
       @job_interference_is_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H3 H4 IBF_P
         (@relative_arrival_time_of_job_is_A Job H2 jc PState sched H3 H4) ->
       forall IBF_NP : duration -> duration -> duration,
       @job_interference_is_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H3 H4 IBF_NP
         (@relative_time_to_reach_rtct Task H0 Job H2 jc PState sched tsk H3 H4 IBF_P) ->
       (forall (F : nat) (Δ : duration), is_true (F <= @task_cost Task H tsk + IBF_NP F Δ)) ->
       forall R : duration,
       (forall A : duration,
        is_in_search_space L IBF_P A ->
        exists F : duration,
          is_true (@task_rtct Task H0 tsk + IBF_P A F <= F) /\
          is_true (@task_cost Task H tsk + IBF_NP F (A + R) <= A + R)) ->
       @task_response_time_bound Task Job H2 jc H1 PState arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Analysis.Abstract.AbstractRta.uniprocessor_response_time_bound : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] [inst_6 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
    ∀ (ts : List Task) (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ [inst_7 : Prosa.Analysis.Abstract.Definitions.Interference Job]
          [inst_8 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
          Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
            ∀ (L : Prosa.Behavior.Time.duration),
              Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by arr_seq sched tsk L →
                ∀ (IBF_P : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                  Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by arr_seq sched tsk IBF_P
                      (Prosa.Analysis.Abstract.AbstractRta.relative_arrival_time_of_job_is_A sched) →
                    ∀
                      (IBF_NP :
                        Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                      Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by arr_seq sched tsk IBF_NP
                          (Prosa.Analysis.Abstract.AbstractRta.relative_time_to_reach_rtct sched tsk IBF_P) →
                        (∀ (F : ℕ) (Δ : Prosa.Behavior.Time.duration),
                            F ≤ Prosa.Model.Task.Concept.task_cost tsk + IBF_NP F Δ) →
                          ∀ (R : Prosa.Behavior.Time.duration),
                            (∀ (A : Prosa.Behavior.Time.duration),
                                Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L IBF_P A →
                                  ∃ F,
                                    Prosa.Model.Task.Preemption.Parameters.task_rtct tsk + IBF_P A F ≤ F ∧
                                      Prosa.Model.Task.Concept.task_cost tsk + IBF_NP F (A + R) ≤ A + R) →
                              Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_AbstractRta_uniprocessor_response_time_bound
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
                    inst_13 PState),
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_13
         inst_16
         inst_23 arr_seq ->
       forall (ts : List Task) (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3)
               tsk ts))
         Bool_true ->
       forall
         (inst_56 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_13)
         (inst_59 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_13),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_13
         inst_56
         inst_59
         inst_20
         inst_23 PState arr_seq sched ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by Job
         inst_13
         inst_56
         inst_59
         inst_20
         inst_23 PState arr_seq sched Task
         inst_3
         inst_16 tsk L ->
       forall
         IBF_P : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by Job
         inst_13
         inst_56
         inst_59
         inst_20
         inst_23 PState arr_seq sched Task
         inst_3
         inst_16 tsk IBF_P
         (Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A Job
            inst_13
            inst_20
            inst_23 PState sched
            inst_56
            inst_59) ->
       forall
         IBF_NP : Prosa_Behavior_Time_duration ->
                  Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by Job
         inst_13
         inst_56
         inst_59
         inst_20
         inst_23 PState arr_seq sched Task
         inst_3
         inst_16 tsk IBF_NP
         (Prosa_Analysis_Abstract_AbstractRta_relative_time_to_reach_rtct Task
            inst_3
            inst_9 Job
            inst_13
            inst_20
            inst_23 PState sched tsk
            inst_56
            inst_59 IBF_P) ->
       (forall (F : Nat) (_UU0394_ : Prosa_Behavior_Time_duration),
        LE_le_inst1 Nat instLENat F
          (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
             Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
             (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                inst_3
                inst_6 tsk)
             (IBF_NP F _UU0394_))) ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Prosa_Behavior_Time_duration,
        Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L IBF_P A ->
        Exists Prosa_Behavior_Time_duration
          (fun F : Prosa_Behavior_Time_duration =>
           And
             (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                   (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                   (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                      inst_3
                      inst_9 tsk)
                   (IBF_P A F))
                F)
             (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                   (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                      inst_3
                      inst_6 tsk)
                   (IBF_NP F
                      (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                         Prosa_Behavior_Time_duration
                         (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R)))
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R)))) ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_13
         inst_20
         inst_23
         inst_16 PState arr_seq sched tsk R
```
