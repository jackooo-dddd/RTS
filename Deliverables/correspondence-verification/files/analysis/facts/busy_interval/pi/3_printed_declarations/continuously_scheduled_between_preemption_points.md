# `continuously_scheduled_between_preemption_points`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.pi.continuously_scheduled_between_preemption_points`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Pi.continuously_scheduled_between_preemption_points`
- Certificate: `continuously_scheduled_between_preemption_points_correspondence`

## Official Rocq

```coq
continuously_scheduled_between_preemption_points :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {H2 : JobCost Job} (arr_seq : arrival_sequence Job) {PState : ProcessorState Job}
  (sched : @schedule Job PState) {H3 : TaskMaxNonpreemptiveSegment Task} {H4 : JobPreemptable Job}
  {JobReady0 : @JobReady Job PState H2 H1},
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
forall t1 : instant,
@valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 H3 H4 PState arr_seq sched ->
@unit_service_proc_model Job PState ->
forall jlp : Equality.sort Job,
is_true (@scheduled_at Job PState sched jlp t1) ->
forall fpt : instant,
(forall ρ : nat,
 is_true
   (@service Job PState sched jlp t1 <= ρ <=
    @service Job PState sched jlp t1 + (@job_max_nonpreemptive_segment Job H2 H4 jlp - 1)) ->
 is_true (@job_preemptable Job H4 jlp ρ) -> is_true (@service Job PState sched jlp t1 + fpt <= ρ)) ->
is_true (fpt <= @job_max_nonpreemptive_segment Job H2 H4 jlp - 1) ->
forall t' : nat, is_true (t1 <= t' < t1 + fpt) -> is_true (@scheduled_at Job PState sched jlp t')

continuously_scheduled_between_preemption_points is not universe polymorphic
Arguments continuously_scheduled_between_preemption_points {Task Job H0 H1 H2} arr_seq 
  {PState} sched {H3 H4 JobReady0} H_sched_valid t1 H_valid_model_with_bounded_nonpreemptive_segments 
  H_unit jlp H_jlp_is_scheduled fpt H_fpt_is_first_preemption_point%function_scope
  H_progr_le_max_nonp_segment t'%nat_scope _
continuously_scheduled_between_preemption_points is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.pi.continuously_scheduled_between_preemption_points
Declared in library prosa.analysis.facts.busy_interval.pi, line 499, characters 16-64
@continuously_scheduled_between_preemption_points
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (H2 : JobCost Job) (arr_seq : arrival_sequence Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState) (H3 : TaskMaxNonpreemptiveSegment Task) (H4 : JobPreemptable Job)
         (JobReady0 : @JobReady Job PState H2 H1),
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       forall t1 : instant,
       @valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 H3 H4 PState arr_seq sched ->
       @unit_service_proc_model Job PState ->
       forall jlp : Equality.sort Job,
       is_true (@scheduled_at Job PState sched jlp t1) ->
       forall fpt : instant,
       (forall ρ : nat,
        is_true
          (@service Job PState sched jlp t1 <= ρ <=
           @service Job PState sched jlp t1 + (@job_max_nonpreemptive_segment Job H2 H4 jlp - 1)) ->
        is_true (@job_preemptable Job H4 jlp ρ) -> is_true (@service Job PState sched jlp t1 + fpt <= ρ)) ->
       is_true (fpt <= @job_max_nonpreemptive_segment Job H2 H4 jlp - 1) ->
       forall t' : nat, is_true (t1 <= t' < t1 + fpt) -> is_true (@scheduled_at Job PState sched jlp t')
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Pi.continuously_scheduled_between_preemption_points : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState)
  [inst_5 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
  [inst_6 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] [inst_7 : Prosa.Behavior.Ready.JobReady Job PState],
  Prosa.Behavior.Ready.valid_schedule sched arr_seq →
    ∀ (t1 : Prosa.Behavior.Time.instant),
      Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments arr_seq sched →
        Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
          ∀ (jlp : Job),
            Prosa.Behavior.Service.scheduled_at sched jlp t1 = true →
              ∀ (fpt : Prosa.Behavior.Time.instant),
                (∀ (ρ : ℕ),
                    (decide (Prosa.Behavior.Service.service sched jlp t1 ≤ ρ) &&
                          decide
                            (ρ ≤
                              Prosa.Behavior.Service.service sched jlp t1 +
                                (Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment jlp - 1))) =
                        true →
                      Prosa.Model.Preemption.Parameter.job_preemptable jlp ρ = true →
                        Prosa.Behavior.Service.service sched jlp t1 + fpt ≤ ρ) →
                  fpt ≤ Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment jlp - 1 →
                    ∀ (t' : ℕ),
                      (decide (t1 ≤ t') && decide (t' < t1 + fpt)) = true →
                        Prosa.Behavior.Service.scheduled_at sched jlp t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Pi_continuously_scheduled_between_preemption_points
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (inst_26 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_7)
         (inst_29 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (inst_32 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_17
            inst_14),
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_14 PState sched
         inst_17
         inst_32 arr_seq ->
       forall t1 : Prosa_Behavior_Time_instant,
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments Task
         inst_7 Job
         inst_3
         inst_10
         inst_17
         inst_26
         inst_29 PState arr_seq sched ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall jlp : Job,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched jlp t1)
         Bool_true ->
       forall fpt : Prosa_Behavior_Time_instant,
       (forall _UU03c1_ : Nat,
        @eq Bool
          (Bool_and
             (Decidable_decide
                (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                   (Prosa_Behavior_Service_service Job
                      inst_3 PState sched
                      jlp t1)
                   _UU03c1_)
                (Nat_decLe
                   (Prosa_Behavior_Service_service Job
                      inst_3 PState sched
                      jlp t1)
                   _UU03c1_))
             (Decidable_decide
                (LE_le_inst1 Nat instLENat _UU03c1_
                   (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
                      (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                      (Prosa_Behavior_Service_service Job
                         inst_3 PState
                         sched jlp t1)
                      (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
                         (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
                            inst_3
                            inst_17
                            inst_29 jlp)
                         (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))))
                (Nat_decLe _UU03c1_
                   (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
                      (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                      (Prosa_Behavior_Service_service Job
                         inst_3 PState
                         sched jlp t1)
                      (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
                         (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
                            inst_3
                            inst_17
                            inst_29 jlp)
                         (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))))))
          Bool_true ->
        @eq Bool
          (Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
             inst_3
             inst_29 jlp _UU03c1_)
          Bool_true ->
        LE_le_inst1 Prosa_Behavior_Job_work instLENat
          (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Time_instant Prosa_Behavior_Job_work
             (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
             (Prosa_Behavior_Service_service Job
                inst_3 PState sched jlp t1)
             fpt)
          _UU03c1_) ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat fpt
         (HSub_hSub_inst7 Nat Prosa_Behavior_Time_instant Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
               inst_3
               inst_17
               inst_29 jlp)
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))) ->
       forall t' : Nat,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t') (Nat_decLe t1 t'))
            (Decidable_decide
               (LT_lt_inst1 Nat instLTNat t'
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                     fpt))
               (Nat_decLt t'
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                     fpt))))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched jlp t')
         Bool_true
```
