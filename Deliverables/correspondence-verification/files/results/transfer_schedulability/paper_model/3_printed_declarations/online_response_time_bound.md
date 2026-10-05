# `online_response_time_bound`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.paper_model.online_response_time_bound`
- Lean: `Prosa.Results.TransferSchedulability.PaperModel.online_response_time_bound`
- Certificate: `online_response_time_bound_correspondence`

## Official Rocq

```coq
online_response_time_bound :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobPredecessors Job} (arr_seq : arrival_sequence Job)
  (Omega : Type) {H1 : SystemEvolutions Omega Job} (omega_0 : Omega)
  (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1)
  (H_non_starvation : forall j : Equality.sort Job,
                      @arrives_in Job arr_seq j ->
                      {R : duration
                      | is_true
                          (@job_response_time_bound Job (ideal.processor_state Job) 
                             (algA omega_0)
                             ((fun omega : Omega => @job_cost Job (@evo_costs Omega Job H1 omega)) omega_0) H
                             j R)})
  (omega : Omega) (jf : Equality.sort Job) (H_arrives : @arrives_in Job arr_seq jf),
@schedulability_transferred_AB Job H H0 Omega H1 omega_0 algA algB omega ->
is_true
  (@job_response_time_bound Job (ideal.processor_state Job) (algB omega)
     ((fun omega0 : Omega => @job_cost Job (@evo_costs Omega Job H1 omega0)) omega) H jf
     (sval (H_non_starvation jf H_arrives)))

online_response_time_bound is not universe polymorphic
Arguments online_response_time_bound {Job H H0} arr_seq Omega%type_scope {H1} omega_0 
  algA algB H_non_starvation%function_scope omega jf H_arrives H_trans
online_response_time_bound is opaque
Expands to: Constant prosa.results.transfer_schedulability.paper_model.online_response_time_bound
Declared in library prosa.results.transfer_schedulability.paper_model, line 402, characters 10-36
@online_response_time_bound
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobPredecessors Job)
         (arr_seq : arrival_sequence Job) (Omega : Type) (H1 : SystemEvolutions Omega Job) 
         (omega_0 : Omega) (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1)
         (H_non_starvation : forall j : Equality.sort Job,
                             @arrives_in Job arr_seq j ->
                             {R : duration
                             | is_true
                                 (@job_response_time_bound Job (ideal.processor_state Job) 
                                    (algA omega_0) (@job_cost Job (@evo_costs Omega Job H1 omega_0)) H j R)})
         (omega : Omega) (jf : Equality.sort Job) (H_arrives : @arrives_in Job arr_seq jf),
       @schedulability_transferred_AB Job H H0 Omega H1 omega_0 algA algB omega ->
       is_true
         (@job_response_time_bound Job (ideal.processor_state Job) (algB omega)
            (@job_cost Job (@evo_costs Omega Job H1 omega)) H jf (sval (H_non_starvation jf H_arrives)))
```

Body:

```coq
online_response_time_bound =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobPredecessors Job) (arr_seq : arrival_sequence Job)
  (Omega : Type) (H1 : SystemEvolutions Omega Job) =>
let job_cost := fun omega : Omega => @job_cost Job (@evo_costs Omega Job H1 omega) in
fun (omega_0 : Omega) (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1)
  (H_non_starvation : forall j : Equality.sort Job,
                      @arrives_in Job arr_seq j ->
                      {R : duration
                      | is_true
                          (@job_response_time_bound Job (ideal.processor_state Job) 
                             (algA omega_0) (job_cost omega_0) H j R)})
  (omega : Omega) (jf : Equality.sort Job) (H_arrives : @arrives_in Job arr_seq jf) =>
let R := sval (H_non_starvation jf H_arrives) in
let ref_response_time_bound :
  (fun R0 : duration =>
   is_true
     (@job_response_time_bound Job (ideal.processor_state Job) (algA omega_0) (job_cost omega_0) H jf R0))
    (sval (H_non_starvation jf H_arrives)) :=
  @proj2_sig duration
    (fun R0 : duration =>
     is_true
       (@job_response_time_bound Job (ideal.processor_state Job) (algA omega_0) (job_cost omega_0) H jf R0))
    (H_non_starvation jf H_arrives)
  in
fun H_trans : @schedulability_transferred_AB Job H H0 Omega H1 omega_0 algA algB omega =>
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobPredecessors Job}
         (arr_seq : arrival_sequence Job) (Omega : Type) {H1 : SystemEvolutions Omega Job} 
         (omega_0 : Omega) (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1)
         (H_non_starvation : forall j : Equality.sort Job,
                             @arrives_in Job arr_seq j ->
                             {R : duration
                             | is_true
                                 (@job_response_time_bound Job (ideal.processor_state Job) 
                                    (algA omega_0)
                                    ((fun omega : Omega => @job_cost Job (@evo_costs Omega Job H1 omega))
                                       omega_0)
                                    H j R)})
         (omega : Omega) (jf : Equality.sort Job) (H_arrives : @arrives_in Job arr_seq jf),
       @schedulability_transferred_AB Job H H0 Omega H1 omega_0 algA algB omega ->
       is_true
         (@job_response_time_bound Job (ideal.processor_state Job) (algB omega)
            ((fun omega0 : Omega => @job_cost Job (@evo_costs Omega Job H1 omega0)) omega) H jf
            (sval (H_non_starvation jf H_arrives)))

Arguments online_response_time_bound {Job H H0} arr_seq Omega%type_scope {H1} omega_0 
  algA algB H_non_starvation%function_scope omega jf H_arrives H_trans
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.PaperModel.online_response_time_bound : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [hA : Prosa.Behavior.Job.JobArrival Job]
  [hP : Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (Omega : Type)
  [hE : Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] (omega_0 : Omega)
  (algA algB :
    Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
      (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE)
  (H_non_starvation :
    (j : Job) →
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        { R // Prosa.Behavior.Service.job_response_time_bound (algA omega_0) j R = true })
  (omega : Omega) (jf : Job) (H_arrives : Prosa.Behavior.Arrival_sequence.arrives_in arr_seq jf),
  Prosa.Results.TransferSchedulability.PaperModel.schedulability_transferred_AB Omega omega_0 algA algB omega →
    Prosa.Behavior.Service.job_response_time_bound (algB omega) jf ↑(H_non_starvation jf H_arrives) = true
```

Body:

```lean
theorem Prosa.Results.TransferSchedulability.PaperModel.online_response_time_bound.{u_1} : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [hA : Prosa.Behavior.Job.JobArrival Job]
  [hP : Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (Omega : Type)
  [hE : Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] (omega_0 : Omega)
  (algA algB :
    Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
      (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE)
  (H_non_starvation :
    (j : Job) →
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        { R // Prosa.Behavior.Service.job_response_time_bound (algA omega_0) j R = true })
  (omega : Omega) (jf : Job) (H_arrives : Prosa.Behavior.Arrival_sequence.arrives_in arr_seq jf),
  Prosa.Results.TransferSchedulability.PaperModel.schedulability_transferred_AB Omega omega_0 algA algB omega →
    Prosa.Behavior.Service.job_response_time_bound (algB omega) jf ↑(H_non_starvation jf H_arrives) = true :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job] arr_seq Omega
    [Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] omega_0 algA algB H_non_starvation
    omega jf H_arrives H_trans =>
  H_trans jf (Prosa.Behavior.Job.job_arrival jf + ↑(H_non_starvation jf H_arrives))
    (H_non_starvation jf H_arrives).property
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_PaperModel_online_response_time_bound
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
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
                   hA Job
                   inst_3 hP
                   Job inst_3
                   hE)
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
         (omega : Omega) (jf : Job)
         (H_arrives : Prosa_Behavior_Arrival_sequence_arrives_in Job
                        inst_3
                        arr_seq jf),
       Prosa_Results_TransferSchedulability_PaperModel_schedulability_transferred_AB Job
         inst_3 hA hP Omega hE
         omega_0 algA algB omega ->
       @eq Bool
         (Prosa_Behavior_Service_job_response_time_bound_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (algB omega)
            (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
               inst_3 hE omega)
            hA jf
            (Subtype_val Prosa_Behavior_Time_duration
               (fun R : Prosa_Behavior_Time_duration =>
                Prosa_Behavior_Service_job_response_time_bound_inst4 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  (algA omega_0)
                  (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
                     inst_3 hE
                     omega_0)
                  hA jf R =
                Bool_true)
               (H_non_starvation jf H_arrives)))
         Bool_true
```

Body:

```coq
Prosa_Results_TransferSchedulability_PaperModel_online_response_time_bound@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
            Job inst_3 hE)
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
                           (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega
                              Job
                              inst_3
                              hE omega_0)
                           hA j R =
                         Bool_true))
  (omega : Omega) (jf : Job)
  (H_arrives : Prosa_Behavior_Arrival_sequence_arrives_in Job
                 inst_3 arr_seq
                 jf)
  (H_trans : Prosa_Results_TransferSchedulability_PaperModel_schedulability_transferred_AB Job
               inst_3 hA hP
               Omega hE omega_0 algA algB omega) =>
H_trans jf
  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
     (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_3 hA jf)
     (Subtype_val Prosa_Behavior_Time_duration
        (fun R : Prosa_Behavior_Time_duration =>
         Prosa_Behavior_Service_job_response_time_bound_inst4 Job
           inst_3
           (Prosa_Model_Processor_Ideal_processor_state Job
              inst_3)
           (algA omega_0)
           (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
              inst_3 hE omega_0)
           hA jf R =
         Bool_true)
        (H_non_starvation jf H_arrives)))
  (Subtype_property Prosa_Behavior_Time_duration
     (fun R : Prosa_Behavior_Time_duration =>
      Prosa_Behavior_Service_job_response_time_bound_inst4 Job
        inst_3
        (Prosa_Model_Processor_Ideal_processor_state Job
           inst_3)
        (algA omega_0)
        (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
           inst_3 hE omega_0)
        hA jf R =
      Bool_true)
     (H_non_starvation jf H_arrives))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
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
                   hA Job
                   inst_3 hP
                   Job inst_3
                   hE)
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
         (omega : Omega) (jf : Job)
         (H_arrives : Prosa_Behavior_Arrival_sequence_arrives_in Job
                        inst_3
                        arr_seq jf),
       Prosa_Results_TransferSchedulability_PaperModel_schedulability_transferred_AB Job
         inst_3 hA hP Omega hE
         omega_0 algA algB omega ->
       @eq Bool
         (Prosa_Behavior_Service_job_response_time_bound_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (algB omega)
            (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
               inst_3 hE omega)
            hA jf
            (Subtype_val Prosa_Behavior_Time_duration
               (fun R : Prosa_Behavior_Time_duration =>
                Prosa_Behavior_Service_job_response_time_bound_inst4 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  (algA omega_0)
                  (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
                     inst_3 hE
                     omega_0)
                  hA jf R =
                Bool_true)
               (H_non_starvation jf H_arrives)))
         Bool_true

Arguments Prosa_Results_TransferSchedulability_PaperModel_online_response_time_bound 
  Job inst_3 
  hA hP arr_seq Omega%_type_scope hE omega_0 algA algB H_non_starvation%_function_scope 
  omega jf H_arrives a____at____internal__hyg0
```
