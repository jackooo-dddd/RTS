# `clairvoyant_necessity'`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.transfer_schedulability.paper_model.clairvoyant_necessity'`
- Lean: `Prosa.Results.TransferSchedulability.PaperModel.clairvoyant_necessity'`
- Certificate: `clairvoyant_necessity'_correspondence`

## Official Rocq

```coq
clairvoyant_necessity' :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobPredecessors Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall (Omega : Type) {H1 : SystemEvolutions Omega Job} (omega_0 : Omega),
(forall (omega : Omega) (j : Equality.sort Job),
 is_true
   ((fun omega0 : Omega => @job_cost Job (@evo_costs Omega Job H1 omega0)) omega j <=
    (fun omega0 : Omega => @job_cost Job (@evo_costs Omega Job H1 omega0)) omega_0 j)) ->
forall algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1,
@valid_schedule Job H (ideal.processor_state Job) (algA omega_0)
  ((fun omega : Omega => @job_cost Job (@evo_costs Omega Job H1 omega)) omega_0)
  ((fun omega : Omega =>
    @delayed_precedence_ready_instance Job (ideal.processor_state Job) H (@evo_costs Omega Job H1 omega) H0
      (@evo_delays Omega Job H1 omega))
     omega_0)
  arr_seq ->
(forall omega : Omega,
 @valid_schedule Job H (ideal.processor_state Job) (algB omega)
   ((fun omega0 : Omega => @job_cost Job (@evo_costs Omega Job H1 omega0)) omega)
   ((fun omega0 : Omega =>
     @delayed_precedence_ready_instance Job (ideal.processor_state Job) H (@evo_costs Omega Job H1 omega0) H0
       (@evo_delays Omega Job H1 omega0))
      omega)
   arr_seq) ->
forall
  (H_non_starvation : forall j : Equality.sort Job,
                      @arrives_in Job arr_seq j ->
                      {R : duration
                      | is_true
                          (@job_response_time_bound Job (ideal.processor_state Job) 
                             (algA omega_0)
                             ((fun omega : Omega => @job_cost Job (@evo_costs Omega Job H1 omega)) omega_0) H
                             j R)})
  (H_non_starvation' : forall j : Equality.sort Job,
                       @arrives_in Job arr_seq j ->
                       forall omega : Omega,
                       {R : duration
                       | is_true
                           (@job_response_time_bound Job (ideal.processor_state Job) 
                              (algB omega)
                              ((fun omega0 : Omega => @job_cost Job (@evo_costs Omega Job H1 omega0)) omega)
                              H j R)}),
(forall (omega : Omega) (j : Equality.sort Job) (in_arrival_sequence : @arrives_in Job arr_seq j),
 is_true
   (@online_finish_time_bounded' Job H H0 arr_seq Omega H1 omega_0 algA algB H_non_starvation
      H_non_starvation' omega j in_arrival_sequence)) ->
@clairvoyant_criterion Job H H0 arr_seq Omega H1 omega_0 algA algB

clairvoyant_necessity' is not universe polymorphic
Arguments clairvoyant_necessity' {Job H H0} arr_seq H_valid_arrivals Omega%type_scope 
  {H1} omega_0 H_max_cost%function_scope algA algB H_well_formed_A
  (H_well_formed_B H_non_starvation H_non_starvation' H_bounded)%function_scope omega 
  t1 t2 _
clairvoyant_necessity' is opaque
Expands to: Constant prosa.results.transfer_schedulability.paper_model.clairvoyant_necessity'
Declared in library prosa.results.transfer_schedulability.paper_model, line 545, characters 12-34
@clairvoyant_necessity'
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobPredecessors Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall (Omega : Type) (H1 : SystemEvolutions Omega Job) (omega_0 : Omega),
       (forall (omega : Omega) (j : Equality.sort Job),
        is_true
          (@job_cost Job (@evo_costs Omega Job H1 omega) j <=
           @job_cost Job (@evo_costs Omega Job H1 omega_0) j)) ->
       forall algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1,
       @valid_schedule Job H (ideal.processor_state Job) (algA omega_0)
         (@job_cost Job (@evo_costs Omega Job H1 omega_0))
         (@delayed_precedence_ready_instance Job (ideal.processor_state Job) H
            (@evo_costs Omega Job H1 omega_0) H0 (@evo_delays Omega Job H1 omega_0))
         arr_seq ->
       (forall omega : Omega,
        @valid_schedule Job H (ideal.processor_state Job) (algB omega)
          (@job_cost Job (@evo_costs Omega Job H1 omega))
          (@delayed_precedence_ready_instance Job (ideal.processor_state Job) H
             (@evo_costs Omega Job H1 omega) H0 (@evo_delays Omega Job H1 omega))
          arr_seq) ->
       forall
         (H_non_starvation : forall j : Equality.sort Job,
                             @arrives_in Job arr_seq j ->
                             {R : duration
                             | is_true
                                 (@job_response_time_bound Job (ideal.processor_state Job) 
                                    (algA omega_0) (@job_cost Job (@evo_costs Omega Job H1 omega_0)) H j R)})
         (H_non_starvation' : forall j : Equality.sort Job,
                              @arrives_in Job arr_seq j ->
                              forall omega : Omega,
                              {R : duration
                              | is_true
                                  (@job_response_time_bound Job (ideal.processor_state Job) 
                                     (algB omega) (@job_cost Job (@evo_costs Omega Job H1 omega)) H j R)}),
       (forall (omega : Omega) (j : Equality.sort Job) (in_arrival_sequence : @arrives_in Job arr_seq j),
        is_true
          (@online_finish_time_bounded' Job H H0 arr_seq Omega H1 omega_0 algA algB H_non_starvation
             H_non_starvation' omega j in_arrival_sequence)) ->
       @clairvoyant_criterion Job H H0 arr_seq Omega H1 omega_0 algA algB
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.PaperModel.clairvoyant_necessity' : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [hA : Prosa.Behavior.Job.JobArrival Job]
  [hP : Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (Omega : Type) [hE : Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job]
      (omega_0 : Omega),
      (∀ (omega : Omega) (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j) →
        ∀
          (algA algB :
            Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
              (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE),
          Prosa.Behavior.Ready.valid_schedule (algA omega_0) arr_seq →
            (∀ (omega : Omega), Prosa.Behavior.Ready.valid_schedule (algB omega) arr_seq) →
              ∀
                (H_non_starvation :
                  (j : Job) →
                    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                      { R // Prosa.Behavior.Service.job_response_time_bound (algA omega_0) j R = true })
                (H_non_starvation' :
                  (j : Job) →
                    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                      (omega : Omega) →
                        { R // Prosa.Behavior.Service.job_response_time_bound (algB omega) j R = true }),
                (∀ (omega : Omega) (j : Job)
                    (in_arrival_sequence : Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j),
                    Prosa.Results.TransferSchedulability.PaperModel.online_finish_time_bounded' arr_seq Omega omega_0
                        algA algB H_non_starvation H_non_starvation' omega j in_arrival_sequence =
                      true) →
                  Prosa.Results.TransferSchedulability.PaperModel.clairvoyant_criterion arr_seq Omega omega_0 algA algB
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_PaperModel_clairvoyant_necessity'
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (hA : Prosa_Behavior_Job_JobArrival Job
                 inst_3)
         (hP : Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job
                 inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3 hA arr_seq ->
       forall (Omega : Type)
         (hE : Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job
                 inst_3)
         (omega_0 : Omega),
       (forall (omega : Omega) (j : Job),
        LE_le_inst1 Prosa_Behavior_Job_work instLENat
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
                inst_3 hE omega)
             j)
          (Prosa_Behavior_Job_JobCost_job_cost Job
             inst_3
             (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
                inst_3 hE
                omega_0)
             j)) ->
       forall
         algA
          algB : Prosa_Results_TransferSchedulability_PaperModel_Scheduler_inst4 Omega Job
                   inst_3
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_3)
                   hA Job inst_3
                   hP Job inst_3
                   hE,
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_3 hA
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (algA omega_0)
         (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
            inst_3 hE omega_0)
         (Prosa_Results_TransferSchedulability_PaperModel_delayed_precedence_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            hA
            (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
               inst_3 hE omega_0)
            hP
            (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_delays Omega Job
               inst_3 hE omega_0))
         arr_seq ->
       (forall omega : Omega,
        Prosa_Behavior_Ready_valid_schedule_inst4 Job
          inst_3 hA
          (Prosa_Model_Processor_Ideal_processor_state Job
             inst_3)
          (algB omega)
          (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
             inst_3 hE omega)
          (Prosa_Results_TransferSchedulability_PaperModel_delayed_precedence_ready_instance_inst4 Job
             inst_3
             (Prosa_Model_Processor_Ideal_processor_state Job
                inst_3)
             hA
             (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
                inst_3 hE omega)
             hP
             (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_delays Omega Job
                inst_3 hE omega))
          arr_seq) ->
       forall
         (H_non_starvation : forall j : Job,
                             Prosa_Behavior_Arrival_sequence_arrives_in Job
                               inst_3
                               arr_seq j ->
                             Subtype Prosa_Behavior_Time_duration
                               (fun R : Prosa_Behavior_Time_duration =>
                                Prosa_Behavior_Service_job_response_time_bound_inst4 Job
                                  inst_3
                                  (Prosa_Model_Processor_Ideal_processor_state Job
                                     inst_3)
                                  (algA omega_0)
                                  (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs
                                     Omega Job
                                     inst_3
                                     hE omega_0)
                                  hA j R =
                                Bool_true))
         (H_non_starvation' : forall j : Job,
                              Prosa_Behavior_Arrival_sequence_arrives_in Job
                                inst_3
                                arr_seq j ->
                              forall omega : Omega,
                              Subtype Prosa_Behavior_Time_duration
                                (fun R : Prosa_Behavior_Time_duration =>
                                 Prosa_Behavior_Service_job_response_time_bound_inst4 Job
                                   inst_3
                                   (Prosa_Model_Processor_Ideal_processor_state Job
                                      inst_3)
                                   (algB omega)
                                   (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs
                                      Omega Job
                                      inst_3
                                      hE omega)
                                   hA j R =
                                 Bool_true)),
       (forall (omega : Omega) (j : Job)
          (in_arrival_sequence : Prosa_Behavior_Arrival_sequence_arrives_in Job
                                   inst_3
                                   arr_seq j),
        @eq Bool
          (Prosa_Results_TransferSchedulability_PaperModel_online_finish_time_bounded' Job
             inst_3 hA hP
             arr_seq Omega hE omega_0 algA algB H_non_starvation H_non_starvation' omega j
             in_arrival_sequence)
          Bool_true) ->
       Prosa_Results_TransferSchedulability_PaperModel_clairvoyant_criterion Job
         inst_3 hA hP arr_seq
         Omega hE omega_0 algA algB
```
