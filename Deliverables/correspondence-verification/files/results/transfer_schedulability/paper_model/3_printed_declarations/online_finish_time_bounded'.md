# `online_finish_time_bounded'`

- Kind (Rocq): Definition
- Rocq: `prosa.results.transfer_schedulability.paper_model.online_finish_time_bounded'`
- Lean: `Prosa.Results.TransferSchedulability.PaperModel.online_finish_time_bounded'`
- Certificate: `online_finish_time_bounded'_correspondence`

## Official Rocq

```coq
online_finish_time_bounded' :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobPredecessors Job} (arr_seq : arrival_sequence Job)
  (Omega : Type) {H1 : SystemEvolutions Omega Job} (omega_0 : Omega)
  (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1),
(forall j : Equality.sort Job,
 @arrives_in Job arr_seq j ->
 {R : duration
 | is_true
     (@job_response_time_bound Job (ideal.processor_state Job) (algA omega_0)
        ((fun omega : Omega => @job_cost Job (@evo_costs Omega Job H1 omega)) omega_0) H j R)}) ->
(forall j : Equality.sort Job,
 @arrives_in Job arr_seq j ->
 forall omega : Omega,
 {R : duration
 | is_true
     (@job_response_time_bound Job (ideal.processor_state Job) (algB omega)
        ((fun omega0 : Omega => @job_cost Job (@evo_costs Omega Job H1 omega0)) omega) H j R)}) ->
Omega -> forall jf : Equality.sort Job, @arrives_in Job arr_seq jf -> bool

online_finish_time_bounded' is not universe polymorphic
Arguments online_finish_time_bounded' {Job H H0} arr_seq Omega%type_scope {H1} omega_0 
  algA algB (H_non_starvation H_non_starvation')%function_scope omega jf H_arrives
online_finish_time_bounded' is transparent
Expands to: Constant prosa.results.transfer_schedulability.paper_model.online_finish_time_bounded'
Declared in library prosa.results.transfer_schedulability.paper_model, line 521, characters 15-42
@online_finish_time_bounded'
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobPredecessors Job)
         (arr_seq : arrival_sequence Job) (Omega : Type) (H1 : SystemEvolutions Omega Job) 
         (omega_0 : Omega) (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1),
       (forall j : Equality.sort Job,
        @arrives_in Job arr_seq j ->
        {R : duration
        | is_true
            (@job_response_time_bound Job (ideal.processor_state Job) (algA omega_0)
               (@job_cost Job (@evo_costs Omega Job H1 omega_0)) H j R)}) ->
       (forall j : Equality.sort Job,
        @arrives_in Job arr_seq j ->
        forall omega : Omega,
        {R : duration
        | is_true
            (@job_response_time_bound Job (ideal.processor_state Job) (algB omega)
               (@job_cost Job (@evo_costs Omega Job H1 omega)) H j R)}) ->
       Omega -> forall jf : Equality.sort Job, @arrives_in Job arr_seq jf -> bool
```

Body:

```coq
online_finish_time_bounded' =
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
  (H_non_starvation' : forall j : Equality.sort Job,
                       @arrives_in Job arr_seq j ->
                       forall omega : Omega,
                       {R : duration
                       | is_true
                           (@job_response_time_bound Job (ideal.processor_state Job) 
                              (algB omega) (job_cost omega) H j R)})
  (omega : Omega) (jf : Equality.sort Job) (H_arrives : @arrives_in Job arr_seq jf) =>
let online_response_time_bound :
  (fun R : duration =>
   is_true (@job_response_time_bound Job (ideal.processor_state Job) (algB omega) (job_cost omega) H jf R))
    (sval (H_non_starvation' jf H_arrives omega)) :=
  @proj2_sig duration
    (fun R : duration =>
     is_true (@job_response_time_bound Job (ideal.processor_state Job) (algB omega) (job_cost omega) H jf R))
    (H_non_starvation' jf H_arrives omega)
  in
@online_finish_time' Job H H0 arr_seq Omega H1 algB H_non_starvation' omega jf H_arrives <=
@ref_finish_time Job H H0 arr_seq Omega H1 omega_0 algA H_non_starvation jf H_arrives
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobPredecessors Job}
         (arr_seq : arrival_sequence Job) (Omega : Type) {H1 : SystemEvolutions Omega Job} 
         (omega_0 : Omega) (algA algB : @Scheduler Omega Job (ideal.processor_state Job) H Job H0 Job H1),
       (forall j : Equality.sort Job,
        @arrives_in Job arr_seq j ->
        {R : duration
        | is_true
            (@job_response_time_bound Job (ideal.processor_state Job) (algA omega_0)
               ((fun omega : Omega => @job_cost Job (@evo_costs Omega Job H1 omega)) omega_0) H j R)}) ->
       (forall j : Equality.sort Job,
        @arrives_in Job arr_seq j ->
        forall omega : Omega,
        {R : duration
        | is_true
            (@job_response_time_bound Job (ideal.processor_state Job) (algB omega)
               ((fun omega0 : Omega => @job_cost Job (@evo_costs Omega Job H1 omega0)) omega) H j R)}) ->
       Omega -> forall jf : Equality.sort Job, @arrives_in Job arr_seq jf -> bool

Arguments online_finish_time_bounded' {Job H H0} arr_seq Omega%type_scope {H1} omega_0 
  algA algB (H_non_starvation H_non_starvation')%function_scope omega jf H_arrives
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.PaperModel.online_finish_time_bounded' : {Job : Prosa.Behavior.Job.JobType} →
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
                    ((j : Job) →
                        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                          (omega : Omega) →
                            { R // Prosa.Behavior.Service.job_response_time_bound (algB omega) j R = true }) →
                      Omega → (jf : Job) → Prosa.Behavior.Arrival_sequence.arrives_in arr_seq jf → Bool
```

Body:

```lean
def Prosa.Results.TransferSchedulability.PaperModel.online_finish_time_bounded'.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
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
                    ((j : Job) →
                        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                          (omega : Omega) →
                            { R // Prosa.Behavior.Service.job_response_time_bound (algB omega) j R = true }) →
                      Omega → (jf : Job) → Prosa.Behavior.Arrival_sequence.arrives_in arr_seq jf → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors Job] arr_seq Omega
    [Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions Omega Job] omega_0 algA algB H_non_starvation
    H_non_starvation' omega jf H_arrives =>
  decide
    (Prosa.Results.TransferSchedulability.PaperModel.online_finish_time' arr_seq Omega algB H_non_starvation' omega jf
        H_arrives ≤
      Prosa.Results.TransferSchedulability.PaperModel.ref_finish_time arr_seq Omega omega_0 algA H_non_starvation jf
        H_arrives)
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_PaperModel_online_finish_time_bounded'
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
       (forall j : Job,
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_3 arr_seq j ->
        forall omega : Omega,
        Subtype Prosa_Behavior_Time_duration
          (fun R : Prosa_Behavior_Time_duration =>
           Prosa_Behavior_Service_job_response_time_bound_inst4 Job
             inst_3
             (Prosa_Model_Processor_Ideal_processor_state Job
                inst_3)
             (algB omega)
             (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
                inst_3 hE omega)
             hA j R =
           Bool_true)) ->
       Omega ->
       forall jf : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq jf ->
       Bool
```

Body:

```coq
Prosa_Results_TransferSchedulability_PaperModel_online_finish_time_bounded'@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
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
                            (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega
                               Job
                               inst_3
                               hE omega)
                            hA j R =
                          Bool_true))
  (omega : Omega) (jf : Job)
  (H_arrives : Prosa_Behavior_Arrival_sequence_arrives_in Job
                 inst_3 arr_seq
                 jf) =>
Decidable_decide
  (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
     (Prosa_Results_TransferSchedulability_PaperModel_online_finish_time' Job
        inst_3 hA hP arr_seq
        Omega hE algB H_non_starvation' omega jf H_arrives)
     (Prosa_Results_TransferSchedulability_PaperModel_ref_finish_time Job
        inst_3 hA hP arr_seq
        Omega hE omega_0 algA H_non_starvation jf H_arrives))
  (Nat_decLe
     (Prosa_Results_TransferSchedulability_PaperModel_online_finish_time' Job
        inst_3 hA hP arr_seq
        Omega hE algB H_non_starvation' omega jf H_arrives)
     (Prosa_Results_TransferSchedulability_PaperModel_ref_finish_time Job
        inst_3 hA hP arr_seq
        Omega hE omega_0 algA H_non_starvation jf H_arrives))
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
       (forall j : Job,
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_3 arr_seq j ->
        forall omega : Omega,
        Subtype Prosa_Behavior_Time_duration
          (fun R : Prosa_Behavior_Time_duration =>
           Prosa_Behavior_Service_job_response_time_bound_inst4 Job
             inst_3
             (Prosa_Model_Processor_Ideal_processor_state Job
                inst_3)
             (algB omega)
             (Prosa_Results_TransferSchedulability_PaperModel_SystemEvolutions_evo_costs Omega Job
                inst_3 hE omega)
             hA j R =
           Bool_true)) ->
       Omega ->
       forall jf : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq jf ->
       Bool

Arguments Prosa_Results_TransferSchedulability_PaperModel_online_finish_time_bounded' 
  Job inst_3 
  hA hP arr_seq Omega%_type_scope hE omega_0 algA algB (H_non_starvation H_non_starvation')%_function_scope
  omega jf H_arrives
```
