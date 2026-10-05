# `clairvoyant_necessity`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.transfer_schedulability.paper_model.clairvoyant_necessity`
- Lean: `Prosa.Results.TransferSchedulability.PaperModel.clairvoyant_necessity`
- Certificate: `clairvoyant_necessity_correspondence`

## Official Rocq

```coq
clairvoyant_necessity :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobPredecessors Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall (Omega : Type) {H1 : SystemEvolutions Omega Job} (omega_0 : Omega)
  (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1),
(forall omega : Omega,
 @valid_schedule Job H (ideal.processor_state Job) (algB omega)
   ((fun omega0 : Omega => @job_cost Job (@evo_costs Omega Job H1 omega0)) omega)
   ((fun omega0 : Omega =>
     @delayed_precedence_ready_instance Job (ideal.processor_state Job) H (@evo_costs Omega Job H1 omega0) H0
       (@evo_delays Omega Job H1 omega0))
      omega)
   arr_seq) ->
(forall omega : Omega, @schedulability_transferred_AB Job H H0 Omega H1 omega_0 algA algB omega) ->
@clairvoyant_criterion Job H H0 arr_seq Omega H1 omega_0 algA algB

clairvoyant_necessity is not universe polymorphic
Arguments clairvoyant_necessity {Job H H0} arr_seq H_valid_arrivals Omega%type_scope 
  {H1} omega_0 algA algB (H_well_formed_B _)%function_scope omega t1 t2 _
clairvoyant_necessity is opaque
Expands to: Constant prosa.results.transfer_schedulability.paper_model.clairvoyant_necessity
Declared in library prosa.results.transfer_schedulability.paper_model, line 288, characters 10-31
@clairvoyant_necessity
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobPredecessors Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall (Omega : Type) (H1 : SystemEvolutions Omega Job) (omega_0 : Omega)
         (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1),
       (forall omega : Omega,
        @valid_schedule Job H (ideal.processor_state Job) (algB omega)
          (@job_cost Job (@evo_costs Omega Job H1 omega))
          (@delayed_precedence_ready_instance Job (ideal.processor_state Job) H
             (@evo_costs Omega Job H1 omega) H0 (@evo_delays Omega Job H1 omega))
          arr_seq) ->
       (forall omega : Omega, @schedulability_transferred_AB Job H H0 Omega H1 omega_0 algA algB omega) ->
       @clairvoyant_criterion Job H H0 arr_seq Omega H1 omega_0 algA algB
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.PaperModel.clairvoyant_necessity : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [hA : Prosa.Behavior.Job.JobArrival Job]
  [hP : Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (Omega : Type) [hE : Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] (omega_0 : Omega)
      (algA algB :
        Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
          (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE),
      (∀ (omega : Omega), Prosa.Behavior.Ready.valid_schedule (algB omega) arr_seq) →
        (∀ (omega : Omega),
            Prosa.Results.TransferSchedulability.PaperModel.schedulability_transferred_AB Omega omega_0 algA algB
              omega) →
          Prosa.Results.TransferSchedulability.PaperModel.clairvoyant_criterion arr_seq Omega omega_0 algA algB
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_PaperModel_clairvoyant_necessity
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
         (omega_0 : Omega)
         (algA
          algB : Prosa_Results_TransferSchedulability_PaperModel_Scheduler_inst4 Omega Job
                   inst_3
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_3)
                   hA Job inst_3
                   hP Job inst_3
                   hE),
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
       (forall omega : Omega,
        Prosa_Results_TransferSchedulability_PaperModel_schedulability_transferred_AB Job
          inst_3 hA hP Omega hE
          omega_0 algA algB omega) ->
       Prosa_Results_TransferSchedulability_PaperModel_clairvoyant_criterion Job
         inst_3 hA hP arr_seq
         Omega hE omega_0 algA algB
```
