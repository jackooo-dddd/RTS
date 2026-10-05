# `no_intermediate_preemption_point`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.pi.no_intermediate_preemption_point`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Pi.no_intermediate_preemption_point`
- Certificate: `no_intermediate_preemption_point_correspondence`

## Official Rocq

```coq
no_intermediate_preemption_point :
forall {Job : JobType} {H2 : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  {H4 : JobPreemptable Job} (t1 : instant) (jlp : Equality.sort Job) (fpt : instant),
(forall ρ : nat,
 is_true
   (@service Job PState sched jlp t1 <= ρ <=
    @service Job PState sched jlp t1 + (@job_max_nonpreemptive_segment Job H2 H4 jlp - 1)) ->
 is_true (@job_preemptable Job H4 jlp ρ) -> is_true (@service Job PState sched jlp t1 + fpt <= ρ)) ->
is_true (fpt <= @job_max_nonpreemptive_segment Job H2 H4 jlp - 1) ->
forall ρ : nat,
is_true (@service Job PState sched jlp t1 <= ρ < @service Job PState sched jlp t1 + fpt) ->
is_true (~~ @job_preemptable Job H4 jlp ρ)

no_intermediate_preemption_point is not universe polymorphic
Arguments no_intermediate_preemption_point {Job H2 PState} sched {H4} t1 jlp fpt
  H_fpt_is_first_preemption_point%function_scope H_progr_le_max_nonp_segment ρ%nat_scope 
  _
no_intermediate_preemption_point is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.pi.no_intermediate_preemption_point
Declared in library prosa.analysis.facts.busy_interval.pi, line 481, characters 16-48
@no_intermediate_preemption_point
     : forall (Job : JobType) (H2 : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (H4 : JobPreemptable Job) (t1 : instant) (jlp : Equality.sort Job) (fpt : instant),
       (forall ρ : nat,
        is_true
          (@service Job PState sched jlp t1 <= ρ <=
           @service Job PState sched jlp t1 + (@job_max_nonpreemptive_segment Job H2 H4 jlp - 1)) ->
        is_true (@job_preemptable Job H4 jlp ρ) -> is_true (@service Job PState sched jlp t1 + fpt <= ρ)) ->
       is_true (fpt <= @job_max_nonpreemptive_segment Job H2 H4 jlp - 1) ->
       forall ρ : nat,
       is_true (@service Job PState sched jlp t1 <= ρ < @service Job PState sched jlp t1 + fpt) ->
       is_true (~~ @job_preemptable Job H4 jlp ρ)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Pi.no_intermediate_preemption_point : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
  [inst_2 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] (t1 : Prosa.Behavior.Time.instant) (jlp : Job)
  (fpt : Prosa.Behavior.Time.instant),
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
      ∀ (ρ : ℕ),
        (decide (Prosa.Behavior.Service.service sched jlp t1 ≤ ρ) &&
              decide (ρ < Prosa.Behavior.Service.service sched jlp t1 + fpt)) =
            true →
          (!Prosa.Model.Preemption.Parameter.job_preemptable jlp ρ) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Pi_no_intermediate_preemption_point
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (inst_13 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (t1 : Prosa_Behavior_Time_instant) (jlp : Job) (fpt : Prosa_Behavior_Time_instant),
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
                            inst_6
                            inst_13 jlp)
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
                            inst_6
                            inst_13 jlp)
                         (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))))))
          Bool_true ->
        @eq Bool
          (Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
             inst_3
             inst_13 jlp _UU03c1_)
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
               inst_6
               inst_13 jlp)
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))) ->
       forall _UU03c1_ : Nat,
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
               (LT_lt_inst1 Nat instLTNat _UU03c1_
                  (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Time_instant
                     Prosa_Behavior_Job_work (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                     (Prosa_Behavior_Service_service Job
                        inst_3 PState sched
                        jlp t1)
                     fpt))
               (Nat_decLt _UU03c1_
                  (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Time_instant
                     Prosa_Behavior_Job_work (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                     (Prosa_Behavior_Service_service Job
                        inst_3 PState sched
                        jlp t1)
                     fpt))))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
               inst_3
               inst_13 jlp _UU03c1_))
         Bool_true
```
