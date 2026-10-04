From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import analysis.definitions.finish_time.
From LeanImport Require Import Lean.

(** FoundationCertificates and FoundationImported are Rocq logical namespaces, assigned to directories using -Q. 
For this finish-time case, the original build uses paths relative to Prosa-Shunqi/ 
FoundationCertificates → Validation/.work/experiments/analysis_finish_time/certificates/
FoundationImported     → Validation/.work/experiments/analysis_finish_time/*)
(** What is ImportedFinishTime? It supplies the Lean-side finish_time, response_time, service definitions, and minimum lemmas.
in the correspondence theorem, we compares the imported Lean-side definitions with the original Prosa definitions.
the meaningful declarations in readable Rocq syntax, open (/Users/shunqiwang/CityuHK/Research/Lean/TranslationProof/Prosa-Shunqi/Reports/casestudy/finish_time_import_print.txt),*)
From FoundationImported Require Import ImportedFinishTime.

(** lower-level helpers used to build the final correspondence proof 
 Some helpers define what "correspondence" means, others prove operations perserve correspondence
 "Foundation" means the assumptions needed to express the relations in correspondence. 
 "Relation" defines when a source value and target value represent the same thing.
 SubNatRel nR nL represents the correspondence relation between natural numbers in the source and target, which
 converts Rocq natural number nR to the corresponding Lean natural number nL.
 "Operation Correspondence" A proof showing matching inputs produce matching outputs, or matching propositions
 For example, related numbers remain related after arithmetic operations.
"PropSPropFoundation": Bring assumptions between Prosa's Prop and Lean's SProp.
"SubadditivityNatCorrespondence": Define conversions between Rocq nat and imported Lean.Nat, and proves correspondence for addition, multiplication, comparison
"ServiceBaseAdapter":Connects Rocq and imported Lean Booleans, lists, membership, and decidable equality.
"ServiceJobOperations": Defines matching job costs, arrival times, and deadlines; proves conversions and arrival-related operations preserve those matches.
"ServiceScheduleOperations": Defines matching processor states and schedules; connects core enumeration, finite sums, scheduling observations
"ServiceCorrespondence": Combines the preceding helpers to prove that complete service definitions match, including completed_by, completes_at, and accumulated service.
"FinishTimeMinBridge": Proves that Rocq ex_minn and imported Lean Nat.find return related minimum values when their predicates correspond.

 *)
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ServiceBaseAdapter
  ServiceNatBoolOperations ServiceJobOperations ServiceScheduleOperations
  ServiceCorrespondence FinishTimeMinBridge.

(** The actual v0.6 [ex_minn] definition is related to the compiled Lean
    [Nat.find] body through the independently checked minimum bridge. *)
Section FinishTime.
  
  (** Both sides use this job. svc_decidable_eq Job converts its 
  equality into the DecidableEq interface required by the imported Lean definitions. *)
  Context (Job : eqType).
(** [PStateR] and [PStateL] are processor-state models for the shared job type
    [Job]: [PStateR] is an instance of the official Rocq [ProcessorState] class,
    and [PStateL] is an instance of the imported Lean [ProcessorState] class,
    using the [DecidableEq] instance [svc_decidable_eq Job].  Each provides a
    type of processor states, a finite type of cores, per-core operations saying
    whether a job is scheduled, how much supply a core produces, and how much
    service a job receives, together with the laws "service <= supply" and
    "service only when scheduled".  The two instances are arbitrary and
    independent; they are related only by [Rstate] below. *)
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedFinishTime.Prosa_Behavior_Schedule_ProcessorState Job
      (svc_decidable_eq Job).
  (** Relation between the source and target processor states. 
  Rstate is a record containing the correspondence and its required proofs, for example:
  Conversions between source and target states and cores, Proof that related states give matching
  scheduling and service observations. *)
  Variable Rstate : SvcProcessorStateRel Job PStateR PStateL.

  (** Take any Rocq schedule and any Lean schedule that agree at every time
  sched t is "what the processor is doing at time t": which jobs run on which cores, 
  and how much supply and service there is. 
  schedR is an arbitrary Rocq schedule*)
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  (** schedL is an arbitrary schedule of the imported Lean type: a function Lean.Nat → State of PStateL.
   The extra argument svc_decidable_eq Job is the DecidableEq instance that the Lean schedule requires,*)
  Variable schedL : ImportedFinishTime.Prosa_Behavior_Schedule_schedule Job
    (svc_decidable_eq Job) PStateL.
  (** This assumes the two schedules describe the same behaviour.
  Why it is needed: finish_time depends on the schedule. It's the first time the job is completed_by, and
   that depends on the service the job received, which is read off
    the schedule state by state. To prove the Rocq and Lean finish_time give the same 
    number, the certificate needs both computed from the same schedule. Hsched 
    provides exactly that.
  Why this assumption is reasonable: Hsched is an input condition, not an assumption 
  that the result already holds. It says nothing about finish_time or completion, only that the two inputs match.
  The scheduling matching is proved at certificates/analysis_facts_completes_at/FactsCompletesAtCorrespondence.v*)
  Hypothesis Hsched :
    SvcScheduleRel Job PStateR PStateL Rstate schedR schedL.
  (** Class JobCost (Job : JobType) := job_cost : Job -> work.
  It's a class with a single field: a function giving each job its 
  cost, a natural number. The Lean version has the extra [DecidableEq Job], 
  which is why the imported type takes svc_decidable_eq Job.*)
  (** The following means	an arbitrary Rocq cost assignment / imported Lean cost assignment
  and assume they give every job the same cost*)
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedFinishTime.Prosa_Behavior_Job_JobCost Job
    (svc_decidable_eq Job).
  (** Why the certificate needs it: completed_by compares the service received with 
  job_cost j. finish_time is defined from completed_by. So to show that the Rocq and 
  Lean finish_time agree, both must use the same costs, and Hcost supplies that. 
  *)
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  (** Class JobArrival (Job : JobType) := job_arrival : Job -> instant. A single-field class: each job has an arrival time, 
  a natural number. The Lean version is the same, plus [DecidableEq Job], hence the svc_decidable_eq Job argument.
  The following declares the Rocq and Lean job arrival functions and assumes they give the same arrival time for every job.
  In other words, Harrival says every job arrives at the same time on both sides*)
  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : ImportedFinishTime.Prosa_Behavior_Job_JobArrival Job
    (svc_decidable_eq Job).
  Hypothesis Harrival : SvcJobArrivalRel Job arrivalR arrivalL.

  Lemma finish_time_correspondence (j : Job) (RR : nat) (RL : Lean.Nat)
      (HR : @prosa.behavior.service.job_response_time_bound Job PStateR
        schedR costR arrivalR j RR)
      (HL : Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_job_response_time_bound
          Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j RL)
        ImportedFinishTime.Bool_true) :
    SubNatRel RR RL ->
    SubNatRel
      (@prosa.analysis.definitions.finish_time.finish_time Job arrivalR
        costR PStateR schedR j RR HR)
      (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time
        Job (svc_decidable_eq Job) arrivalL costL PStateL schedL j RL HL).
  Proof.
    intro HRR.
    unfold prosa.analysis.definitions.finish_time.finish_time.
    cbn [ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time].
    eapply minimum_value_correspondence.
    intros nR nL Hn.
    apply svc_bool_truth_correspondence.
    exact (completed_by_correspondence Job PStateR PStateL Rstate
      schedR schedL Hsched costR costL Hcost j nR nL Hn).
  Qed.

  Lemma finished_at_finish_time_statement_correspondence
      (j : Job) (RR : nat) (RL : Lean.Nat)
      (HR : @prosa.behavior.service.job_response_time_bound Job PStateR
        schedR costR arrivalR j RR)
      (HL : Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_job_response_time_bound
          Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j RL)
        ImportedFinishTime.Bool_true) :
    SubNatRel RR RL ->
    PropSPropRel
      (is_true (@prosa.behavior.service.completed_by Job PStateR schedR
        costR j (@prosa.analysis.definitions.finish_time.finish_time Job
          arrivalR costR PStateR schedR j RR HR)))
      (Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_completed_by
          Job (svc_decidable_eq Job) PStateL schedL costL j
          (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time
            Job (svc_decidable_eq Job) arrivalL costL PStateL schedL
            j RL HL))
        ImportedFinishTime.Bool_true).
  Proof.
    intro HRR. apply svc_bool_truth_correspondence.
    exact (completed_by_correspondence Job PStateR PStateL Rstate
      schedR schedL Hsched costR costL Hcost j _ _
      (finish_time_correspondence j RR RL HR HL HRR)).
  Qed.

  Lemma completes_at_finish_time_statement_correspondence
      (j : Job) (RR : nat) (RL : Lean.Nat)
      (HR : @prosa.behavior.service.job_response_time_bound Job PStateR
        schedR costR arrivalR j RR)
      (HL : Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_job_response_time_bound
          Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j RL)
        ImportedFinishTime.Bool_true) :
    SubNatRel RR RL ->
    PropSPropRel
      (is_true (@prosa.behavior.service.completes_at Job PStateR schedR
        costR j (@prosa.analysis.definitions.finish_time.finish_time Job
          arrivalR costR PStateR schedR j RR HR)))
      (Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_completes_at
          Job (svc_decidable_eq Job) PStateL schedL costL j
          (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time
            Job (svc_decidable_eq Job) arrivalL costL PStateL schedL
            j RL HL))
        ImportedFinishTime.Bool_true).
  Proof.
    intro HRR. apply svc_bool_truth_correspondence.
    exact (completes_at_correspondence Job PStateR PStateL Rstate
      schedR schedL Hsched costR costL Hcost j _ _
      (finish_time_correspondence j RR RL HR HL HRR)).
  Qed.

  Lemma earliest_finish_time_statement_correspondence
      (j : Job) (RR : nat) (RL : Lean.Nat)
      (HR : @prosa.behavior.service.job_response_time_bound Job PStateR
        schedR costR arrivalR j RR)
      (HL : Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_job_response_time_bound
          Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j RL)
        ImportedFinishTime.Bool_true) :
    SubNatRel RR RL ->
    PropSPropRel
      (forall tR : nat,
        is_true (@prosa.behavior.service.completed_by Job PStateR
          schedR costR j tR) ->
        is_true ((@prosa.analysis.definitions.finish_time.finish_time
          Job arrivalR costR PStateR schedR j RR HR) <= tR)%N)
      (forall tL : Lean.Nat,
        Lean.eq
          (ImportedFinishTime.Prosa_Behavior_Service_completed_by
            Job (svc_decidable_eq Job) PStateL schedL costL j tL)
          ImportedFinishTime.Bool_true ->
        ImportedFinishTime.LE_le_inst1 Lean.Nat
          ImportedFinishTime.instLENat
          (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time
            Job (svc_decidable_eq Job) arrivalL costL PStateL schedL
            j RL HL) tL).
  Proof.
    intro HRR.
    pose Hfinish := finish_time_correspondence j RR RL HR HL HRR.
    apply prop_sprop_rel_intro.
    - intros Hsource tL HcompL.
      pose tR := sub_nat_to_rocq tL.
      have Ht : SubNatRel tR tL := sub_nat_rel_surjective tL.
      have Hcomp := svc_bool_truth_correspondence _ _
        (completed_by_correspondence Job PStateR PStateL Rstate
          schedR schedL Hsched costR costL Hcost j tR tL Ht).
      have HcompR := sprop_to_prop _ _ Hcomp HcompL.
      exact (prop_to_sprop _ _
        (svc_target_le_related _ _ _ _ Hfinish Ht)
        (Hsource tR HcompR)).
    - intro Htarget. apply strictly_inhabits.
      intros tR HcompR.
      pose tL := sub_nat_to_imported tR.
      have Ht : SubNatRel tR tL := sub_nat_rel_canonical tR.
      have Hcomp := svc_bool_truth_correspondence _ _
        (completed_by_correspondence Job PStateR PStateL Rstate
          schedR schedL Hsched costR costL Hcost j tR tL Ht).
      have HcompL := prop_to_sprop _ _ Hcomp HcompR.
      exact (sprop_to_prop _ _
        (svc_target_le_related _ _ _ _ Hfinish Ht)
        (Htarget tL HcompL)).
  Qed.

  Lemma response_time_correspondence (j : Job)
      (RR : nat) (RL : Lean.Nat)
      (HR : @prosa.behavior.service.job_response_time_bound Job PStateR
        schedR costR arrivalR j RR)
      (HL : Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_job_response_time_bound
          Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j RL)
        ImportedFinishTime.Bool_true) :
    SubNatRel RR RL ->
    SubNatRel
      (@prosa.analysis.definitions.finish_time.response_time Job arrivalR
        costR PStateR schedR j RR HR)
      (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_response_time
        Job (svc_decidable_eq Job) arrivalL costL PStateL schedL j RL HL).
  Proof.
    intro HRR.
    unfold prosa.analysis.definitions.finish_time.response_time.
    cbn [ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_response_time].
    exact (svc_target_sub_related _ _ _ _
      (finish_time_correspondence j RR RL HR HL HRR) (Harrival j)).
  Qed.

End FinishTime.
