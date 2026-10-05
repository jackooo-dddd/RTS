# `nonclairvoyant_sufficiency'`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.transfer_schedulability.paper_model.nonclairvoyant_sufficiency'`
- Lean: `Prosa.Results.TransferSchedulability.PaperModel.nonclairvoyant_sufficiency'`
- Certificate: `nonclairvoyant_sufficiency'_correspondence`

## Official Rocq

```coq
nonclairvoyant_sufficiency' :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobPredecessors Job} (arr_seq : arrival_sequence Job)
  (H_valid_arrivals : @valid_arrival_sequence Job H arr_seq) (Omega : Type) {H1 : SystemEvolutions Omega Job}
  (omega_0 : Omega)
  (H_max_cost : forall (omega : Omega) (j : Equality.sort Job),
                is_true
                  ((fun omega0 : Omega => @job_cost Job (@evo_costs Omega Job H1 omega0)) omega j <=
                   (fun omega0 : Omega => @job_cost Job (@evo_costs Omega Job H1 omega0)) omega_0 j))
  (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1)
  (H_well_formed_A : @valid_schedule Job H (ideal.processor_state Job) (algA omega_0)
                       ((fun omega : Omega => @job_cost Job (@evo_costs Omega Job H1 omega)) omega_0)
                       ((fun omega : Omega =>
                         @delayed_precedence_ready_instance Job (ideal.processor_state Job) H
                           (@evo_costs Omega Job H1 omega) H0 (@evo_delays Omega Job H1 omega))
                          omega_0)
                       arr_seq)
  (H_well_formed_B : forall omega : Omega,
                     @valid_schedule Job H (ideal.processor_state Job) (algB omega)
                       ((fun omega0 : Omega => @job_cost Job (@evo_costs Omega Job H1 omega0)) omega)
                       ((fun omega0 : Omega =>
                         @delayed_precedence_ready_instance Job (ideal.processor_state Job) H
                           (@evo_costs Omega Job H1 omega0) H0 (@evo_delays Omega Job H1 omega0))
                          omega)
                       arr_seq)
  (H_non_starvation : forall j : Equality.sort Job,
                      @arrives_in Job arr_seq j ->
                      {R : duration
                      | is_true
                          (@job_response_time_bound Job (ideal.processor_state Job) 
                             (algA omega_0)
                             ((fun omega : Omega => @job_cost Job (@evo_costs Omega Job H1 omega)) omega_0) H
                             j R)})
  (H_criterion : @nonclairvoyant_criterion Job H H0 arr_seq Omega H1 omega_0 algA algB) 
  (omega : Omega) (j : Equality.sort Job) (IN : @arrives_in Job arr_seq j),
is_true
  (@online_finish_time_bounded Job H H0 arr_seq Omega H1 omega_0 algA algB H_non_starvation omega j IN
     (@nonclairvoyant_sufficiency Job H H0 arr_seq H_valid_arrivals Omega H1 omega_0 H_max_cost algA algB
        H_well_formed_A H_well_formed_B H_criterion omega))

nonclairvoyant_sufficiency' is not universe polymorphic
Arguments nonclairvoyant_sufficiency' {Job H H0} arr_seq H_valid_arrivals Omega%type_scope 
  {H1} omega_0 H_max_cost%function_scope algA algB H_well_formed_A
  (H_well_formed_B H_non_starvation)%function_scope H_criterion omega j IN
nonclairvoyant_sufficiency' is opaque
Expands to: Constant prosa.results.transfer_schedulability.paper_model.nonclairvoyant_sufficiency'
Declared in library prosa.results.transfer_schedulability.paper_model, line 467, characters 12-39
@nonclairvoyant_sufficiency'
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobPredecessors Job)
         (arr_seq : arrival_sequence Job) (H_valid_arrivals : @valid_arrival_sequence Job H arr_seq)
         (Omega : Type) (H1 : SystemEvolutions Omega Job) (omega_0 : Omega)
         (H_max_cost : forall (omega : Omega) (j : Equality.sort Job),
                       is_true
                         (@job_cost Job (@evo_costs Omega Job H1 omega) j <=
                          @job_cost Job (@evo_costs Omega Job H1 omega_0) j))
         (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1)
         (H_well_formed_A : @valid_schedule Job H (ideal.processor_state Job) (algA omega_0)
                              (@job_cost Job (@evo_costs Omega Job H1 omega_0))
                              (@delayed_precedence_ready_instance Job (ideal.processor_state Job) H
                                 (@evo_costs Omega Job H1 omega_0) H0 (@evo_delays Omega Job H1 omega_0))
                              arr_seq)
         (H_well_formed_B : forall omega : Omega,
                            @valid_schedule Job H (ideal.processor_state Job) (algB omega)
                              (@job_cost Job (@evo_costs Omega Job H1 omega))
                              (@delayed_precedence_ready_instance Job (ideal.processor_state Job) H
                                 (@evo_costs Omega Job H1 omega) H0 (@evo_delays Omega Job H1 omega))
                              arr_seq)
         (H_non_starvation : forall j : Equality.sort Job,
                             @arrives_in Job arr_seq j ->
                             {R : duration
                             | is_true
                                 (@job_response_time_bound Job (ideal.processor_state Job) 
                                    (algA omega_0) (@job_cost Job (@evo_costs Omega Job H1 omega_0)) H j R)})
         (H_criterion : @nonclairvoyant_criterion Job H H0 arr_seq Omega H1 omega_0 algA algB)
         (omega : Omega) (j : Equality.sort Job) (IN : @arrives_in Job arr_seq j),
       is_true
         (@online_finish_time_bounded Job H H0 arr_seq Omega H1 omega_0 algA algB H_non_starvation omega j IN
            (@nonclairvoyant_sufficiency Job H H0 arr_seq H_valid_arrivals Omega H1 omega_0 H_max_cost algA
               algB H_well_formed_A H_well_formed_B H_criterion omega))
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.PaperModel.nonclairvoyant_sufficiency' : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [hA : Prosa.Behavior.Job.JobArrival Job]
  [hP : Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (H_valid_arrivals : Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq) (Omega : Type)
  [hE : Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] (omega_0 : Omega)
  (H_max_cost : ∀ (omega : Omega) (j : Job), Prosa.Behavior.Job.job_cost j ≤ Prosa.Behavior.Job.job_cost j)
  (algA algB :
    Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
      (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE)
  (H_well_formed_A : Prosa.Behavior.Ready.valid_schedule (algA omega_0) arr_seq)
  (H_well_formed_B : ∀ (omega : Omega), Prosa.Behavior.Ready.valid_schedule (algB omega) arr_seq)
  (H_non_starvation :
    (j : Job) →
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        { R // Prosa.Behavior.Service.job_response_time_bound (algA omega_0) j R = true })
  (H_criterion :
    Prosa.Results.TransferSchedulability.PaperModel.nonclairvoyant_criterion arr_seq Omega omega_0 algA algB)
  (omega : Omega) (j : Job) (IN : Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j),
  Prosa.Results.TransferSchedulability.PaperModel.online_finish_time_bounded arr_seq Omega omega_0 algA algB
      H_non_starvation omega j IN ⋯ =
    true
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_PaperModel_nonclairvoyant_sufficiency'
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (hA : Prosa_Behavior_Job_JobArrival Job
                 inst_3)
         (hP : Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job
                 inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (H_valid_arrivals : Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
                               inst_3
                               hA arr_seq)
         (Omega : Type)
         (hE : Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job
                 inst_3)
         (omega_0 : Omega)
         (H_max_cost : forall (omega : Omega) (j : Job),
                       LE_le_inst1 Prosa_Behavior_Job_work instLENat
                         (Prosa_Behavior_Job_JobCost_job_cost Job
                            inst_3
                            (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega
                               Job
                               inst_3
                               hE omega)
                            j)
                         (Prosa_Behavior_Job_JobCost_job_cost Job
                            inst_3
                            (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega
                               Job
                               inst_3
                               hE omega_0)
                            j))
         (algA
          algB : Prosa_Results_TransferSchedulability_PaperModel_Scheduler_inst4 Omega Job
                   inst_3
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_3)
                   hA Job
                   inst_3 hP
                   Job inst_3
                   hE)
         (H_well_formed_A : Prosa_Behavior_Ready_valid_schedule_inst4 Job
                              inst_3
                              hA
                              (Prosa_Model_Processor_Ideal_processor_state Job
                                 inst_3)
                              (algA omega_0)
                              (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs
                                 Omega Job
                                 inst_3
                                 hE omega_0)
                              (Prosa_Results_TransferSchedulability_PaperModel_delayed_precedence_ready_instance_inst4
                                 Job
                                 inst_3
                                 (Prosa_Model_Processor_Ideal_processor_state Job
                                    inst_3)
                                 hA
                                 (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs
                                    Omega Job
                                    inst_3
                                    hE omega_0)
                                 hP
                                 (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_delays
                                    Omega Job
                                    inst_3
                                    hE omega_0))
                              arr_seq)
         (H_well_formed_B : forall omega : Omega,
                            Prosa_Behavior_Ready_valid_schedule_inst4 Job
                              inst_3
                              hA
                              (Prosa_Model_Processor_Ideal_processor_state Job
                                 inst_3)
                              (algB omega)
                              (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs
                                 Omega Job
                                 inst_3
                                 hE omega)
                              (Prosa_Results_TransferSchedulability_PaperModel_delayed_precedence_ready_instance_inst4
                                 Job
                                 inst_3
                                 (Prosa_Model_Processor_Ideal_processor_state Job
                                    inst_3)
                                 hA
                                 (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs
                                    Omega Job
                                    inst_3
                                    hE omega)
                                 hP
                                 (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_delays
                                    Omega Job
                                    inst_3
                                    hE omega))
                              arr_seq)
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
         (H_criterion : Prosa_Results_TransferSchedulability_PaperModel_nonclairvoyant_criterion Job
                          inst_3
                          hA hP arr_seq Omega hE omega_0 algA algB)
         (omega : Omega) (j : Job)
         (IN : Prosa_Behavior_Arrival_sequence_arrives_in Job
                 inst_3 arr_seq
                 j),
       @eq Bool
         (Prosa_Results_TransferSchedulability_PaperModel_online_finish_time_bounded Job
            inst_3 hA hP
            arr_seq Omega hE omega_0 algA algB H_non_starvation omega j IN
            (Prosa_Results_TransferSchedulability_PaperModel_nonclairvoyant_sufficiency Job
               inst_3 hA hP
               arr_seq H_valid_arrivals Omega hE omega_0 H_max_cost algA algB H_well_formed_A H_well_formed_B
               H_criterion omega))
         Bool_true
```
