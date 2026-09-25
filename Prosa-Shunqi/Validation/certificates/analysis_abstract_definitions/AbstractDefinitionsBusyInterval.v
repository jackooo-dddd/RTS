From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From Coq Require Import Bool.Bool.
From prosa Require Import analysis.abstract.definitions.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedAbstractDefinitions ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  AbstractDefinitionsBaseAdapter AbstractDefinitionsClasses
  AbstractDefinitionsOperations AbstractDefinitionsNatBoolOperations
  AbstractDefinitionsIntervalOperations AbstractDefinitionsSums
  ServiceBaseAdapter ServiceNatBoolOperations ServiceScheduleOperations
  AbstractDefinitionsPendingOperations AbstractDefinitionsLogical
  AbstractDefinitionsArrivalOperations AbstractDefinitionsTaskOperations.

Lemma ad_and_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P /\ Q) (And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p q]. exact (And_intro PL QL
      (prop_to_sprop _ _ HP p) (prop_to_sprop _ _ HQ q)).
  - intros [p q]. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ HP p).
    + exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma ad_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. apply (prop_to_sprop _ _ HQ).
    exact (H (sprop_to_prop _ _ HP p)).
  - intro H. apply strictly_inhabits. intro p.
    exact (sprop_to_prop _ _ HQ (H (prop_to_sprop _ _ HP p))).
Qed.

Lemma ad_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P <-> Q) (ImportedAbstractDefinitions.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [HPQ HQP]. exact (ImportedAbstractDefinitions.Iff_intro PL QL
      (fun p => prop_to_sprop _ _ HQ (HPQ (sprop_to_prop _ _ HP p)))
      (fun q => prop_to_sprop _ _ HP (HQP (sprop_to_prop _ _ HQ q)))).
  - intro H. apply strictly_inhabits. split.
    + intro p. apply (sprop_to_prop _ _ HQ).
      exact (ImportedAbstractDefinitions.mp PL QL H
        (prop_to_sprop _ _ HP p)).
    + intro q. apply (sprop_to_prop _ _ HP).
      exact (ImportedAbstractDefinitions.mpr PL QL H
        (prop_to_sprop _ _ HQ q)).
Qed.

Definition ad_imported_false_to_strict
    (H : ImportedAbstractDefinitions.False) :
    StrictlyInhabited Logic.False := match H with end.

Lemma ad_not_correspondence (P : Prop) (PL : SProp) :
  PropSPropRel P PL ->
  PropSPropRel (Logic.not P) (ImportedAbstractDefinitions.Not PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros Hnot pL. apply ad_coq_false_to_target. apply Hnot.
    exact (sprop_to_prop _ _ HP pL).
  - intro Hnot. apply strictly_inhabits. intro pR.
    exact (interpret_strict Logic.False
      (ad_imported_false_to_strict (Hnot (prop_to_sprop _ _ HP pR)))).
Qed.

Lemma ad_nat_interval_correspondence aR aL bR bL cR cL :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel cR cL ->
  PropSPropRel (is_true (andb (leq aR bR) (ltn bR cR)))
    (And
      (sub_imported_le aL bL) (sub_imported_lt bL cL)).
Proof.
  intros Ha Hb Hc.
  have Hle := sub_nat_le_correspondence aR aL bR bL Ha Hb.
  have Hlt := sub_nat_lt_correspondence bR bL cR cL Hb Hc.
  apply prop_sprop_rel_intro.
  - intro H. apply Bool.andb_true_iff in H. destruct H as [H1 H2].
    exact (And_intro _ _
      (prop_to_sprop _ _ Hle H1) (prop_to_sprop _ _ Hlt H2)).
  - intros [H1 H2]. apply strictly_inhabits.
    apply Bool.andb_true_iff. split.
    + exact (sprop_to_prop _ _ Hle H1).
    + exact (sprop_to_prop _ _ Hlt H2).
Qed.

Lemma ad_nat_open_interval_correspondence aR aL bR bL cR cL :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel cR cL ->
  PropSPropRel (is_true (andb (ltn aR bR) (ltn bR cR)))
    (And
      (sub_imported_lt aL bL) (sub_imported_lt bL cL)).
Proof.
  intros Ha Hb Hc.
  have Hlt1 := sub_nat_lt_correspondence aR aL bR bL Ha Hb.
  have Hlt2 := sub_nat_lt_correspondence bR bL cR cL Hb Hc.
  apply prop_sprop_rel_intro.
  - intro H. apply Bool.andb_true_iff in H. destruct H as [H1 H2].
    exact (And_intro _ _
      (prop_to_sprop _ _ Hlt1 H1) (prop_to_sprop _ _ Hlt2 H2)).
  - intros [H1 H2]. apply strictly_inhabits.
    apply Bool.andb_true_iff. split.
    + exact (sprop_to_prop _ _ Hlt1 H1).
    + exact (sprop_to_prop _ _ Hlt2 H2).
Qed.

Section BusyIntervalCorrespondence.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedAbstractDefinitions.Prosa_Behavior_Schedule_ProcessorState Job
      (ad_decidable_eq Job).
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedAbstractDefinitions.Prosa_Behavior_Schedule_schedule
    Job (ad_decidable_eq Job) PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : ImportedAbstractDefinitions.Prosa_Behavior_Job_JobArrival Job
    (ad_decidable_eq Job).
  Hypothesis Harrival : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job arrivalR j)
      (ImportedAbstractDefinitions.Prosa_Behavior_Job_JobArrival_job_arrival Job
        (ad_decidable_eq Job) arrivalL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedAbstractDefinitions.Prosa_Behavior_Job_JobCost Job
    (ad_decidable_eq Job).
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (ImportedAbstractDefinitions.Prosa_Behavior_Job_JobCost_job_cost Job
        (ad_decidable_eq Job) costL j).
  Variable interR : prosa.analysis.abstract.definitions.Interference Job.
  Variable interL :
    ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_Interference
      Job (ad_decidable_eq Job).
  Hypothesis Hinter : AdInterferenceRel Job interR interL.
  Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
  Variable workloadL :
    ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_InterferingWorkload
      Job (ad_decidable_eq Job).
  Hypothesis Hworkload :
    AdInterferingWorkloadRel Job workloadR workloadL.

  Lemma ad_quiet_time_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    AdBoolRel
      (@prosa.analysis.abstract.definitions.quiet_time
        Job arrivalR costR PStateR schedR interR workloadR j tR)
      (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_quiet_time
        Job (ad_decidable_eq Job) interL workloadL arrivalL costL
        PStateL schedL j tL).
  Proof.
    intro Ht.
    cbn [prosa.analysis.abstract.definitions.quiet_time
      ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_quiet_time].
    apply ad_bool_and_related.
    - apply ad_decide_nat_eq_related.
      + exact (cumulative_interference_correspondence Job interR interL
          j O tR Lean.Nat_zero tL Hinter
          (sub_nat_rel_canonical O) Ht).
      + exact (cumulative_interfering_workload_correspondence Job
          workloadR workloadL Hworkload j O tR Lean.Nat_zero tL
          (sub_nat_rel_canonical O) Ht).
    - apply svc_bool_not_related.
      exact (ad_pending_earlier_and_at_related Job PStateR PStateL R
        schedR schedL Hsched costR costL Hcost arrivalR arrivalL Harrival
        j tR tL Ht).
  Qed.

  Lemma ad_busy_interval_prefix_correspondence (j : Job)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    PropSPropRel
      (@prosa.analysis.abstract.definitions.busy_interval_prefix
        Job arrivalR costR PStateR schedR interR workloadR j t1R t2R)
      (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_busy_interval_prefix
        Job (ad_decidable_eq Job) interL workloadL arrivalL costL
        PStateL schedL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    cbn [prosa.analysis.abstract.definitions.busy_interval_prefix
      ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_busy_interval_prefix].
    apply ad_and_correspondence.
    - exact (ad_nat_interval_correspondence t1R t1L
        (@prosa.behavior.job.job_arrival Job arrivalR j)
        (ImportedAbstractDefinitions.Prosa_Behavior_Job_JobArrival_job_arrival
          Job (ad_decidable_eq Job) arrivalL j) t2R t2L
        Ht1 (Harrival j) Ht2).
    - apply ad_and_correspondence.
      + exact (ad_bool_truth_correspondence _ _
          (ad_quiet_time_correspondence j t1R t1L Ht1)).
      + apply ad_forall_nat_correspondence. intros tR tL Ht.
        apply ad_imp_correspondence.
        * exact (ad_nat_open_interval_correspondence
            t1R t1L tR tL t2R t2L Ht1 Ht Ht2).
        * apply ad_not_correspondence.
          exact (ad_bool_truth_correspondence _ _
            (ad_quiet_time_correspondence j tR tL Ht)).
  Qed.

  Lemma ad_busy_interval_correspondence (j : Job)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    PropSPropRel
      (@prosa.analysis.abstract.definitions.busy_interval
        Job arrivalR costR PStateR schedR interR workloadR j t1R t2R)
      (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_busy_interval
        Job (ad_decidable_eq Job) interL workloadL arrivalL costL
        PStateL schedL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    cbn [prosa.analysis.abstract.definitions.busy_interval
      ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_busy_interval].
    apply ad_and_correspondence.
    - exact (ad_busy_interval_prefix_correspondence j
        t1R t2R t1L t2L Ht1 Ht2).
    - exact (ad_bool_truth_correspondence _ _
        (ad_quiet_time_correspondence j t2R t2L Ht2)).
  Qed.

  Local Definition ad_source_uniqueness_statement : Prop :=
    forall (j : Job) (t1 t2 t1' t2' : nat),
      @prosa.analysis.abstract.definitions.busy_interval
        Job arrivalR costR PStateR schedR interR workloadR j t1 t2 ->
      @prosa.analysis.abstract.definitions.busy_interval
        Job arrivalR costR PStateR schedR interR workloadR j t1' t2' ->
      Logic.eq t1 t1' /\ Logic.eq t2 t2'.

  Local Definition ad_target_uniqueness_statement : SProp :=
    forall (j : Job) (t1 t2 t1' t2' : Lean.Nat),
      ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_busy_interval
        Job (ad_decidable_eq Job) interL workloadL arrivalL costL
        PStateL schedL j t1 t2 ->
      ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_busy_interval
        Job (ad_decidable_eq Job) interL workloadL arrivalL costL
        PStateL schedL j t1' t2' ->
      And (Lean.eq t1 t1') (Lean.eq t2 t2').

  (** These guards are intentionally separate from the correspondence proof:
      neither theorem proof term occurs in the certificate dependency graph. *)
  Check (@prosa.analysis.abstract.definitions.busy_interval_is_unique
    Job arrivalR costR PStateR schedR interR workloadR
    : ad_source_uniqueness_statement).
  Check (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_busy_interval_is_unique
    Job (ad_decidable_eq Job) interL workloadL arrivalL costL PStateL schedL
    : ad_target_uniqueness_statement).

  Lemma ad_busy_interval_unique_statement_correspondence :
    PropSPropRel ad_source_uniqueness_statement
      ad_target_uniqueness_statement.
  Proof.
    unfold ad_source_uniqueness_statement,
      ad_target_uniqueness_statement.
    apply ad_forall_identity_correspondence. intro j.
    apply ad_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ad_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ad_forall_nat_correspondence. intros t1R' t1L' Ht1'.
    apply ad_forall_nat_correspondence. intros t2R' t2L' Ht2'.
    apply ad_imp_correspondence.
    - exact (ad_busy_interval_correspondence j t1R t2R t1L t2L
        Ht1 Ht2).
    - apply ad_imp_correspondence.
      + exact (ad_busy_interval_correspondence j t1R' t2R' t1L' t2L'
          Ht1' Ht2').
      + apply ad_and_correspondence.
        * exact (sub_nat_eq_correspondence t1R t1L t1R' t1L' Ht1 Ht1').
        * exact (sub_nat_eq_correspondence t2R t2L t2R' t2L' Ht2 Ht2').
  Qed.

  Lemma ad_interference_related_general (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    AdBoolRel (@prosa.analysis.abstract.definitions.interference
        Job interR j tR)
      (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_Interference_interference
        Job (ad_decidable_eq Job) interL j tL).
  Proof.
    intro Ht. unfold AdBoolRel.
    exact (sub_imported_eq_trans _ _ _ (Hinter j tR)
      (sub_imported_eq_congr
        (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_Interference_interference
          Job (ad_decidable_eq Job) interL j) _ _ Ht)).
  Qed.

  Variable arrSeqR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrSeqL :
    ImportedAbstractDefinitions.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job (ad_decidable_eq Job).
  Hypothesis HarrSeq : AdArrivalSequenceRel Job arrSeqR arrSeqL.

  Lemma ad_work_conserving_correspondence :
    PropSPropRel
      (@prosa.analysis.abstract.definitions.work_conserving
        Job arrivalR costR PStateR arrSeqR schedR interR workloadR)
      (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_work_conserving
        Job (ad_decidable_eq Job) interL workloadL arrivalL costL
        PStateL arrSeqL schedL).
  Proof.
    cbn [prosa.analysis.abstract.definitions.work_conserving
      ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_work_conserving].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ad_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ad_forall_nat_correspondence. intros tR tL Ht.
    apply ad_imp_correspondence.
    - exact (ad_arrives_in_related Job arrSeqR arrSeqL j HarrSeq).
    - apply ad_imp_correspondence.
      + exact (sub_nat_lt_correspondence 0 Lean.Nat_zero
          (@prosa.behavior.job.job_cost Job costR j)
          (ImportedAbstractDefinitions.Prosa_Behavior_Job_JobCost_job_cost
            Job (ad_decidable_eq Job) costL j)
          (sub_nat_rel_canonical 0) (Hcost j)).
      + apply ad_imp_correspondence.
        * exact (ad_busy_interval_prefix_correspondence j
            t1R t2R t1L t2L Ht1 Ht2).
        * apply ad_imp_correspondence.
          -- exact (ad_nat_interval_correspondence
               t1R t1L tR tL t2R t2L Ht1 Ht Ht2).
          -- apply ad_iff_correspondence.
             ++ apply ad_not_correspondence.
                exact (ad_bool_truth_correspondence _ _
                  (ad_interference_related_general j tR tL Ht)).
             ++ exact (ad_bool_truth_correspondence _ _
                  (ad_receives_service_at_related Job PStateR PStateL R
                    schedR schedL Hsched j tR tL Ht)).
  Qed.

  Variable Task : eqType.
  Variable jobTaskR : prosa.model.task.concept.JobTask Job Task.
  Variable jobTaskL :
    ImportedAbstractDefinitions.Prosa_Model_Task_Concept_JobTask
      Job (ad_decidable_eq Job) Task (ad_decidable_eq Task).
  Hypothesis HjobTask : AdJobTaskRel Job Task jobTaskR jobTaskL.
  Variable tsk : Task.

  Lemma ad_busy_intervals_bounded_correspondence
      (LR : nat) (LL : Lean.Nat) :
    SubNatRel LR LL ->
    PropSPropRel
      (@prosa.analysis.abstract.definitions.busy_intervals_are_bounded_by
        Job Task jobTaskR arrivalR costR PStateR arrSeqR schedR tsk
        interR workloadR LR)
      (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by
        Job (ad_decidable_eq Job) interL workloadL arrivalL costL
        PStateL arrSeqL schedL Task (ad_decidable_eq Task)
        jobTaskL tsk LL).
  Proof.
    intro HL.
    cbn [prosa.analysis.abstract.definitions.busy_intervals_are_bounded_by
      ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence.
    - exact (ad_arrives_in_related Job arrSeqR arrSeqL j HarrSeq).
    - apply ad_imp_correspondence.
      + exact (ad_bool_truth_correspondence _ _
          (ad_job_of_task_related Job Task jobTaskR jobTaskL
            tsk j HjobTask)).
      + apply ad_imp_correspondence.
        * exact (sub_nat_lt_correspondence 0 Lean.Nat_zero
            (@prosa.behavior.job.job_cost Job costR j)
            (ImportedAbstractDefinitions.Prosa_Behavior_Job_JobCost_job_cost
              Job (ad_decidable_eq Job) costL j)
            (sub_nat_rel_canonical 0) (Hcost j)).
        * apply ad_exists_nat_correspondence. intros t1R t1L Ht1.
          apply ad_exists_nat_correspondence. intros t2R t2L Ht2.
          apply ad_and_correspondence.
          -- exact (ad_nat_interval_correspondence t1R t1L
               (@prosa.behavior.job.job_arrival Job arrivalR j)
               (ImportedAbstractDefinitions.Prosa_Behavior_Job_JobArrival_job_arrival
                 Job (ad_decidable_eq Job) arrivalL j)
               t2R t2L Ht1 (Harrival j) Ht2).
          -- apply ad_and_correspondence.
             ++ apply sub_nat_le_correspondence.
                ** exact Ht2.
                ** exact (svc_target_add_related t1R t1L LR LL Ht1 HL).
             ++ exact (ad_busy_interval_correspondence j
                  t1R t2R t1L t2L Ht1 Ht2).
  Qed.

  Variable IBFR : nat -> nat -> nat.
  Variable IBFL : Lean.Nat -> Lean.Nat -> Lean.Nat.
  Hypothesis HIBF : forall xR xL dR dL,
    SubNatRel xR xL -> SubNatRel dR dL ->
    SubNatRel (IBFR xR dR) (IBFL xL dL).
  Variable ParamSemR : Job -> nat -> Prop.
  Variable ParamSemL : Job -> Lean.Nat -> SProp.
  Hypothesis HParamSem : forall j xR xL,
    SubNatRel xR xL ->
    PropSPropRel (ParamSemR j xR) (ParamSemL j xL).
  Variable CondR : Job -> nat -> bool.
  Variable CondL : Job -> Lean.Nat -> ImportedAbstractDefinitions.Bool.
  Hypothesis HCond : AdBoolPredRel Job CondR CondL.

  Lemma ad_cond_interference_bounded_correspondence :
    PropSPropRel
      (@prosa.analysis.abstract.definitions.cond_interference_is_bounded_by
        Job Task jobTaskR arrivalR costR PStateR arrSeqR schedR tsk
        interR workloadR IBFR ParamSemR CondR)
      (ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_cond_interference_is_bounded_by
        Job (ad_decidable_eq Job) interL workloadL arrivalL costL
        PStateL arrSeqL schedL Task (ad_decidable_eq Task)
        jobTaskL tsk IBFL ParamSemL CondL).
  Proof.
    cbn [prosa.analysis.abstract.definitions.cond_interference_is_bounded_by
      ImportedAbstractDefinitions.Prosa_Analysis_Abstract_Definitions_cond_interference_is_bounded_by].
    apply ad_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ad_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ad_forall_nat_correspondence. intros dR dL Hd.
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence.
    - exact (ad_arrives_in_related Job arrSeqR arrSeqL j HarrSeq).
    - apply ad_imp_correspondence.
      + exact (ad_bool_truth_correspondence _ _
          (ad_job_of_task_related Job Task jobTaskR jobTaskL tsk j HjobTask)).
      + apply ad_imp_correspondence.
        * exact (ad_busy_interval_correspondence j
            t1R t2R t1L t2L Ht1 Ht2).
        * apply ad_imp_correspondence.
          -- exact (sub_nat_lt_correspondence
               (t1R + dR) (svc_target_add t1L dL) t2R t2L
               (svc_target_add_related t1R t1L dR dL Ht1 Hd) Ht2).
          -- apply ad_imp_correspondence.
             ++ exact (ad_bool_truth_correspondence _ _
                  (svc_bool_not_related _ _
                    (ad_completed_by_related Job PStateR PStateL R
                      schedR schedL Hsched costR costL Hcost j
                      (t1R + dR) (svc_target_add t1L dL)
                      (svc_target_add_related t1R t1L dR dL Ht1 Hd)))).
             ++ apply ad_forall_nat_correspondence. intros xR xL Hx.
                apply ad_imp_correspondence.
                ** exact (HParamSem j xR xL Hx).
                ** apply sub_nat_le_correspondence.
                   --- exact (cumul_cond_interference_correspondence
                         Job interR interL Hinter CondR CondL HCond j
                         t1R (t1R + dR) t1L (svc_target_add t1L dL)
                         Ht1 (svc_target_add_related t1R t1L dR dL Ht1 Hd)).
                   --- exact (HIBF xR xL dR dL Hx Hd).
  Qed.

End BusyIntervalCorrespondence.

Print Assumptions ad_quiet_time_correspondence.
Print Assumptions ad_busy_interval_prefix_correspondence.
Print Assumptions ad_busy_interval_correspondence.
Print Assumptions ad_busy_interval_unique_statement_correspondence.
Print Assumptions ad_work_conserving_correspondence.
Print Assumptions ad_busy_intervals_bounded_correspondence.
Print Assumptions ad_cond_interference_bounded_correspondence.
