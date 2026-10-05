# `online_finish_time`

- Kind (Rocq): Definition
- Rocq: `prosa.results.transfer_schedulability.paper_model.online_finish_time`
- Lean: `Prosa.Results.TransferSchedulability.PaperModel.online_finish_time`
- Certificate: `online_finish_time_correspondence`

## Official Rocq

```coq
online_finish_time :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobPredecessors Job} (arr_seq : arrival_sequence Job)
  (Omega : Type) {H1 : SystemEvolutions Omega Job} (omega_0 : Omega)
  (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1),
(forall j : Equality.sort Job,
 @arrives_in Job arr_seq j ->
 {R : duration
 | is_true
     (@job_response_time_bound Job (ideal.processor_state Job) (algA omega_0)
        ((fun omega : Omega => @job_cost Job (@evo_costs Omega Job H1 omega)) omega_0) H j R)}) ->
forall (omega : Omega) (jf : Equality.sort Job),
@arrives_in Job arr_seq jf ->
@schedulability_transferred_AB Job H H0 Omega H1 omega_0 algA algB omega -> instant

online_finish_time is not universe polymorphic
Arguments online_finish_time {Job H H0} arr_seq Omega%type_scope {H1} omega_0 algA 
  algB H_non_starvation%function_scope omega jf H_arrives H_trans
online_finish_time is transparent
Expands to: Constant prosa.results.transfer_schedulability.paper_model.online_finish_time
Declared in library prosa.results.transfer_schedulability.paper_model, line 409, characters 15-33
@online_finish_time
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobPredecessors Job)
         (arr_seq : arrival_sequence Job) (Omega : Type) (H1 : SystemEvolutions Omega Job) 
         (omega_0 : Omega) (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1),
       (forall j : Equality.sort Job,
        @arrives_in Job arr_seq j ->
        {R : duration
        | is_true
            (@job_response_time_bound Job (ideal.processor_state Job) (algA omega_0)
               (@job_cost Job (@evo_costs Omega Job H1 omega_0)) H j R)}) ->
       forall (omega : Omega) (jf : Equality.sort Job),
       @arrives_in Job arr_seq jf ->
       @schedulability_transferred_AB Job H H0 Omega H1 omega_0 algA algB omega -> instant
```

Body:

```coq
online_finish_time =
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
@finish_time Job H (job_cost omega) (ideal.processor_state Job) (algB omega) jf R
  (@online_response_time_bound Job H H0 arr_seq Omega H1 omega_0 algA algB H_non_starvation omega jf
     H_arrives H_trans)
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobPredecessors Job}
         (arr_seq : arrival_sequence Job) (Omega : Type) {H1 : SystemEvolutions Omega Job} 
         (omega_0 : Omega) (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1),
       (forall j : Equality.sort Job,
        @arrives_in Job arr_seq j ->
        {R : duration
        | is_true
            (@job_response_time_bound Job (ideal.processor_state Job) (algA omega_0)
               ((fun omega : Omega => @job_cost Job (@evo_costs Omega Job H1 omega)) omega_0) H j R)}) ->
       forall (omega : Omega) (jf : Equality.sort Job),
       @arrives_in Job arr_seq jf ->
       @schedulability_transferred_AB Job H H0 Omega H1 omega_0 algA algB omega -> instant

Arguments online_finish_time {Job H H0} arr_seq Omega%type_scope {H1} omega_0 algA 
  algB H_non_starvation%function_scope omega jf H_arrives H_trans
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.PaperModel.online_finish_time : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [hA : Prosa.Behavior.Job.JobArrival Job] →
      [hP : Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job] →
        (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) →
          (Omega : Type) →
            [hE : Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] →
              (omega_0 : Omega) →
                (algA algB :
                    Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
                      (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE) →
                  ((j : Job) →
                      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                        { R // Prosa.Behavior.Service.job_response_time_bound (algA omega_0) j R = true }) →
                    (omega : Omega) →
                      (jf : Job) →
                        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq jf →
                          Prosa.Results.TransferSchedulability.PaperModel.schedulability_transferred_AB Omega omega_0
                              algA algB omega →
                            Prosa.Behavior.Time.instant
```

Body:

```lean
def Prosa.Results.TransferSchedulability.PaperModel.online_finish_time.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [hA : Prosa.Behavior.Job.JobArrival Job] →
      [hP : Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job] →
        (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) →
          (Omega : Type) →
            [hE : Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] →
              (omega_0 : Omega) →
                (algA algB :
                    Prosa.Results.TransferSchedulability.PaperModel.Scheduler Omega Job
                      (Prosa.Model.Processor.Ideal.processor_state Job) hA Job hP Job hE) →
                  ((j : Job) →
                      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                        { R // Prosa.Behavior.Service.job_response_time_bound (algA omega_0) j R = true }) →
                    (omega : Omega) →
                      (jf : Job) →
                        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq jf →
                          Prosa.Results.TransferSchedulability.PaperModel.schedulability_transferred_AB Omega omega_0
                              algA algB omega →
                            Prosa.Behavior.Time.instant :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job] arr_seq Omega
    [Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] omega_0 algA algB H_non_starvation
    omega jf H_arrives H_trans =>
  Prosa.Analysis.Definitions.FinishTime.finish_time (algB omega) jf ↑(H_non_starvation jf H_arrives) ⋯
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_PaperModel_online_finish_time
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
                   hE),
       (forall j : Job,
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_3 arr_seq j ->
        Subtype Prosa_Behavior_Time_duration
          (fun R : Prosa_Behavior_Time_duration =>
           Prosa_Behavior_Service_job_response_time_bound_inst4 Job
             inst_3
             (Prosa_Model_Processor_Ideal_processor_state Job
                inst_3)
             (algA omega_0)
             (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
                inst_3 hE
                omega_0)
             hA j R =
           Bool_true)) ->
       forall (omega : Omega) (jf : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq jf ->
       Prosa_Results_TransferSchedulability_PaperModel_schedulability_transferred_AB Job
         inst_3 hA hP Omega hE
         omega_0 algA algB omega ->
       Prosa_Behavior_Time_instant
```

Body:

```coq
Prosa_Results_TransferSchedulability_PaperModel_online_finish_time@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
Prosa_Analysis_Definitions_FinishTime_finish_time_inst4 Job
  inst_3 hA
  (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
     inst_3 hE omega)
  (Prosa_Model_Processor_Ideal_processor_state Job
     inst_3)
  (algB omega) jf
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
     (H_non_starvation jf H_arrives))
  (Prosa_Results_TransferSchedulability_PaperModel_online_response_time_bound Job
     inst_3 hA hP arr_seq Omega
     hE omega_0 algA algB H_non_starvation omega jf H_arrives H_trans)
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
                   hE),
       (forall j : Job,
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_3 arr_seq j ->
        Subtype Prosa_Behavior_Time_duration
          (fun R : Prosa_Behavior_Time_duration =>
           Prosa_Behavior_Service_job_response_time_bound_inst4 Job
             inst_3
             (Prosa_Model_Processor_Ideal_processor_state Job
                inst_3)
             (algA omega_0)
             (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
                inst_3 hE
                omega_0)
             hA j R =
           Bool_true)) ->
       forall (omega : Omega) (jf : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq jf ->
       Prosa_Results_TransferSchedulability_PaperModel_schedulability_transferred_AB Job
         inst_3 hA hP Omega hE
         omega_0 algA algB omega ->
       Prosa_Behavior_Time_instant

Arguments Prosa_Results_TransferSchedulability_PaperModel_online_finish_time Job
  inst_3 
  hA hP arr_seq Omega%_type_scope hE omega_0 algA algB H_non_starvation%_function_scope 
  omega jf H_arrives H_trans
```
