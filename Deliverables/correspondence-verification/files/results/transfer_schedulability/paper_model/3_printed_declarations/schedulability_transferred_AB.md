# `schedulability_transferred_AB`

- Kind (Rocq): Definition
- Rocq: `prosa.results.transfer_schedulability.paper_model.schedulability_transferred_AB`
- Lean: `Prosa.Results.TransferSchedulability.PaperModel.schedulability_transferred_AB`
- Certificate: `schedulability_transferred_AB_correspondence`

## Official Rocq

```coq
schedulability_transferred_AB :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobPredecessors Job} (Omega : Type)
  {H1 : SystemEvolutions Omega Job},
Omega ->
@Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1 ->
@Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1 -> Omega -> Prop

schedulability_transferred_AB is not universe polymorphic
Arguments schedulability_transferred_AB {Job H H0} Omega%type_scope {H1} omega_0 algA algB omega
schedulability_transferred_AB is transparent
Expands to: Constant prosa.results.transfer_schedulability.paper_model.schedulability_transferred_AB
Declared in library prosa.results.transfer_schedulability.paper_model, line 238, characters 13-42
@schedulability_transferred_AB
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobPredecessors Job) (Omega : Type)
         (H1 : SystemEvolutions Omega Job),
       Omega ->
       @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1 ->
       @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1 -> Omega -> Prop
```

Body:

```coq
schedulability_transferred_AB =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobPredecessors Job) (Omega : Type)
  (H1 : SystemEvolutions Omega Job) =>
let job_cost := fun omega : Omega => @job_cost Job (@evo_costs Omega Job H1 omega) in
fun (omega_0 : Omega) (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1)
  (omega : Omega) =>
@schedulability_transferred Job (algA omega_0) (algB omega) (job_cost omega_0) (job_cost omega)
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobPredecessors Job} (Omega : Type)
         {H1 : SystemEvolutions Omega Job},
       Omega ->
       @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1 ->
       @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1 -> Omega -> Prop

Arguments schedulability_transferred_AB {Job H H0} Omega%type_scope {H1} omega_0 algA algB omega
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.PaperModel.schedulability_transferred_AB : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [hA : Prosa.Behavior.Job.JobArrival Job] →
      [hP : Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job] →
        (Omega : Type) →
          [hE : Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] →
            Omega →
              Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
                  (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE →
                Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
                    (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE →
                  Omega → Prop
```

Body:

```lean
def Prosa.Results.TransferSchedulability.PaperModel.schedulability_transferred_AB.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [hA : Prosa.Behavior.Job.JobArrival Job] →
      [hP : Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job] →
        (Omega : Type) →
          [hE : Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] →
            Omega →
              Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
                  (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE →
                Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
                    (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE →
                  Omega → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job] Omega
    [Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] omega_0 algA algB omega =>
  Prosa.Results.TransferSchedulability.Criterion.schedulability_transferred (algA omega_0) (algB omega)
    (Prosa.Results.TransferSchedulability.PaperModel.evo_costs omega_0)
    (Prosa.Results.TransferSchedulability.PaperModel.evo_costs omega)
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_PaperModel_schedulability_transferred_AB
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (hA : Prosa_Behavior_Job_JobArrival Job
                 inst_3)
         (hP : Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job
                 inst_3)
         (Omega : Type)
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
       Omega -> SProp
```

Body:

```coq
Prosa_Results_TransferSchedulability_PaperModel_schedulability_transferred_AB@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (hA : Prosa_Behavior_Job_JobArrival Job
          inst_3)
  (hP : Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job
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
            hA Job inst_3 hP Job
            inst_3 hE)
  (omega : Omega) =>
Prosa_Results_TransferSchedulability_Criterion_schedulability_transferred Job
  inst_3 
  (algA omega_0) (algB omega)
  (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
     inst_3 hE omega_0)
  (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
     inst_3 hE omega)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (hA : Prosa_Behavior_Job_JobArrival Job
                 inst_3)
         (hP : Prosa_Results_TransferSchedulability_PaperModel_JobPredecessors Job
                 inst_3)
         (Omega : Type)
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
       Omega -> SProp

Arguments Prosa_Results_TransferSchedulability_PaperModel_schedulability_transferred_AB 
  Job inst_3 
  hA hP Omega%_type_scope hE omega_0 algA algB a____at____internal__hyg0
```
