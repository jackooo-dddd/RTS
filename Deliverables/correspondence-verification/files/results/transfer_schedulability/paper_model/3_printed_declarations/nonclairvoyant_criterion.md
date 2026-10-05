# `nonclairvoyant_criterion`

- Kind (Rocq): Definition
- Rocq: `prosa.results.transfer_schedulability.paper_model.nonclairvoyant_criterion`
- Lean: `Prosa.Results.TransferSchedulability.PaperModel.nonclairvoyant_criterion`
- Certificate: `nonclairvoyant_criterion_correspondence`

## Official Rocq

```coq
nonclairvoyant_criterion :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobPredecessors Job},
arrival_sequence Job ->
forall (Omega : Type) {H1 : SystemEvolutions Omega Job},
Omega ->
@Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1 ->
@Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1 -> Prop

nonclairvoyant_criterion is not universe polymorphic
Arguments nonclairvoyant_criterion {Job H H0} arr_seq Omega%type_scope {H1} omega_0 algA algB
nonclairvoyant_criterion is transparent
Expands to: Constant prosa.results.transfer_schedulability.paper_model.nonclairvoyant_criterion
Declared in library prosa.results.transfer_schedulability.paper_model, line 305, characters 13-37
@nonclairvoyant_criterion
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobPredecessors Job),
       arrival_sequence Job ->
       forall (Omega : Type) (H1 : SystemEvolutions Omega Job),
       Omega ->
       @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1 ->
       @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1 -> Prop
```

Body:

```coq
nonclairvoyant_criterion =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobPredecessors Job) (arr_seq : arrival_sequence Job)
  (Omega : Type) (H1 : SystemEvolutions Omega Job) =>
let job_cost := fun omega : Omega => @job_cost Job (@evo_costs Omega Job H1 omega) in
fun (omega_0 : Omega) (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1) =>
forall omega : Omega,
@transfer_schedulability_criterion Job (algA omega_0) (algB omega) (job_cost omega_0) 
  (job_cost omega) arr_seq (job_cost omega_0)
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobPredecessors Job},
       arrival_sequence Job ->
       forall (Omega : Type) {H1 : SystemEvolutions Omega Job},
       Omega ->
       @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1 ->
       @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1 -> Prop

Arguments nonclairvoyant_criterion {Job H H0} arr_seq Omega%type_scope {H1} omega_0 algA algB
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.PaperModel.nonclairvoyant_criterion : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [hA : Prosa.Behavior.Job.JobArrival Job] →
      [hP : Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          (Omega : Type) →
            [hE : Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] →
              Omega →
                Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
                    (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE →
                  Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
                      (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE →
                    Prop
```

Body:

```lean
def Prosa.Results.TransferSchedulability.PaperModel.nonclairvoyant_criterion.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [hA : Prosa.Behavior.Job.JobArrival Job] →
      [hP : Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          (Omega : Type) →
            [hE : Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] →
              Omega →
                Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
                    (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE →
                  Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
                      (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE →
                    Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job] arr_seq Omega
    [Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] omega_0 algA algB =>
  ∀ (omega : Omega),
    Prosa.Results.TransferSchedulability.Criterion.transfer_schedulability_criterion (algA omega_0) (algB omega)
      (Prosa.Results.TransferSchedulability.PaperModel.evo_costs omega_0)
      (Prosa.Results.TransferSchedulability.PaperModel.evo_costs omega) arr_seq
      (Prosa.Results.TransferSchedulability.PaperModel.evo_costs omega_0)
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_PaperModel_nonclairvoyant_criterion
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (hA : Prosa_Behavior_Job_JobArrival Job
                 inst_3)
         (hP : Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job
                 inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       forall (Omega : Type)
         (hE : Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job
                 inst_3),
       Omega ->
       Prosa_Results_TransferSchedulability_PaperModel_Scheduler_inst4 Omega Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         hA Job inst_3 hP Job
         inst_3 hE ->
       Prosa_Results_TransferSchedulability_PaperModel_Scheduler_inst4 Omega Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         hA Job inst_3 hP Job
         inst_3 hE ->
       SProp
```

Body:

```coq
Prosa_Results_TransferSchedulability_PaperModel_nonclairvoyant_criterion@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (hA : Prosa_Behavior_Job_JobArrival Job
          inst_3)
  (hP : Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job
          inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (Omega : Type)
  (hE : Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job
          inst_3)
  (omega_0 : Omega)
  (algA
   algB : Prosa_Results_TransferSchedulability_PaperModel_Scheduler_inst4 Omega Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            hA Job inst_3 hP
            Job inst_3 hE) =>
forall omega : Omega,
Prosa_Results_TransferSchedulability_Criterion_transfer_schedulability_criterion Job
  inst_3 
  (algA omega_0) (algB omega)
  (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
     inst_3 hE omega_0)
  (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
     inst_3 hE omega)
  arr_seq
  (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
     inst_3 hE omega_0)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (hA : Prosa_Behavior_Job_JobArrival Job
                 inst_3)
         (hP : Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job
                 inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       forall (Omega : Type)
         (hE : Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions Omega Job
                 inst_3),
       Omega ->
       Prosa_Results_TransferSchedulability_PaperModel_Scheduler_inst4 Omega Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         hA Job inst_3 hP Job
         inst_3 hE ->
       Prosa_Results_TransferSchedulability_PaperModel_Scheduler_inst4 Omega Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         hA Job inst_3 hP Job
         inst_3 hE ->
       SProp

Arguments Prosa_Results_TransferSchedulability_PaperModel_nonclairvoyant_criterion 
  Job inst_3 
  hA hP arr_seq Omega%_type_scope hE omega_0 algA algB
```
