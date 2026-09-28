From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From mathcomp Require Import ssralg ssrnum ssrint.
From prosa Require Import GeneralityGelSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties
  model.priority.classes model.task.sequentiality util.int model.priority.gel
  model.task.absolute_deadline model.priority.edf model.priority.fifo.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedGeneralityGel ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityGelHelpers.

Module I := ImportedGeneralityGel.
Module S := GeneralityGelSemanticSource.GeneralityGelSemanticSource.
Module PDS := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.

Import GRing.Theory Num.Theory.

(** Correspondences for [results/generality/gel.v].

    Source side: the extracted definition [S.pp_delta] and the extracted
    statements [S.statement_X] specialised at their leading inputs (task and
    job types, the priority-point and job-task classes, the processor model,
    the arrival, cost, preemption and readiness models, and the task
    deadlines resp. the FP policy where the statement takes them); target
    side: the compiled Lean definition and the imported Lean theorem types.
    Inputs as in the accepted ELF-generality certificate (processor states by
    the accepted two-sided [SvcProcessorStateRel]; [job_task] by [Lean.eq];
    task priority points by the accepted [GelPriorityPointRel]; [job_arrival]
    and [job_cost] pointwise; [JobPreemptable] by the accepted
    [PpJobPreemptableRel]; the readiness model pointwise on Booleans at
    related schedules; the FP policy by the accepted [PdFPRel]), plus task
    deadlines pointwise by [SubNatRel].  Schedules (through the state
    relation), arrival sequences, tasks, jobs and instants are covered in both
    directions.

    Integers: MathComp [int] and Lean [Int] are related constructor-wise by
    the accepted [GelIntRel]; subtraction, [`|_|] and the literal zero
    through kernel-checked Lean constructor equations exported with the
    artifact (subtraction as in the accepted ELF workload-bound certificate);
    equality through the accepted integer roundtrips.  [GEL] is the accepted
    GEL certificate, [EDF] (over task deadlines) and [FIFO] are related
    pointwise from the arrival and deadline inputs, the JLFP and FP policies
    at preemption points are the accepted priority-driven certificate,
    backlogged jobs, completion and scheduling the accepted observations;
    schedule validity and sequential tasks are related by unfolding (as in
    the accepted ELF-generality certificate).  No source or target theorem
    is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Notation P_sub_oo_le := I.Prosa_Validation_GeneralityGelInterface_production_int_sub_ofNat_ofNat_le.
Notation P_sub_oo_gt := I.Prosa_Validation_GeneralityGelInterface_production_int_sub_ofNat_ofNat_gt.
Notation P_sub_on := I.Prosa_Validation_GeneralityGelInterface_production_int_sub_ofNat_negSucc.
Notation P_sub_no := I.Prosa_Validation_GeneralityGelInterface_production_int_sub_negSucc_ofNat.
Notation P_sub_nn_le := I.Prosa_Validation_GeneralityGelInterface_production_int_sub_negSucc_negSucc_le.
Notation P_sub_nn_gt := I.Prosa_Validation_GeneralityGelInterface_production_int_sub_negSucc_negSucc_gt.
Notation P_abs_o := I.Prosa_Validation_GeneralityGelInterface_production_int_natAbs_ofNat.
Notation P_abs_n := I.Prosa_Validation_GeneralityGelInterface_production_int_natAbs_negSucc.
Notation P_zero := I.Prosa_Validation_GeneralityGelInterface_production_int_zero_eq.

(** ** Target operations, read off the exported equations *)

Definition gg_target_sub (x y : I.Int) : I.Int :=
  ltac:(let T := type of (P_sub_on (sub_nat_to_imported 0) (sub_nat_to_imported 0)) in
        match T with @Lean.eq _ (?f (I.Int_ofNat _) (I.Int_negSucc _)) _ => exact (f x y) end).

Definition gg_target_abs (z : I.Int) : Lean.Nat :=
  ltac:(let T := type of (P_abs_o (sub_nat_to_imported 0)) in
        match T with @Lean.eq _ (?g (I.Int_ofNat _)) _ => exact (g z) end).

(** ** Source facts on MathComp integers (as in the accepted ELF workload-bound certificate) *)

Lemma gg_subz_pp_le (m n : nat) : (n <= m)%N -> (Posz m - Posz n)%R = Posz (m - n).
Proof. by move=> h; rewrite subzn. Qed.

Lemma gg_subz_pp_gt (m n : nat) : ~~ (n <= m)%N -> (Posz m - Posz n)%R = Negz (n - m - 1).
Proof.
  rewrite -ltnNge => h. rewrite NegzE subn1 prednK ?subn_gt0 //.
  by rewrite -subzn ?opprB // ltnW.
Qed.

Lemma gg_subz_pn (m n : nat) : (Posz m - Negz n)%R = Posz (m + n + 1).
Proof. by rewrite NegzE opprK -!PoszD addn1 addnS. Qed.

Lemma gg_subz_np (m n : nat) : (Negz m - Posz n)%R = Negz (m + n).
Proof. by rewrite !NegzE -opprD -PoszD addSn. Qed.

Lemma gg_subz_nn_le (m n : nat) : (m <= n)%N -> (Negz m - Negz n)%R = Posz (n - m).
Proof. by move=> h; rewrite !NegzE opprK addrC subzn. Qed.

Lemma gg_subz_nn_gt (m n : nat) : ~~ (m <= n)%N -> (Negz m - Negz n)%R = Negz (m - n - 1).
Proof.
  rewrite -ltnNge => h. rewrite !NegzE opprK subn1 prednK ?subn_gt0 //.
  rewrite -subzn ?(ltnW h) // opprB addrC -(addn1 n) -(addn1 m) !PoszD opprD addrACA subrr addr0.
  by [].
Qed.

(** ** Nat helpers *)

Lemma gg_sub1_related (a b : nat) :
  SubNatRel (a - b - 1) (nat_target_sub (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported 1)).
Proof.
  exact (nat_target_sub_correspondence _ _ _ _
    (nat_target_sub_correspondence _ _ _ _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b))
    (sub_nat_rel_canonical 1)).
Qed.

Lemma gg_add1_related (a b : nat) :
  SubNatRel (a + b + 1) (nat_target_add (nat_target_add (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported 1)).
Proof.
  exact (nat_target_add_correspondence _ _ _ _
    (nat_target_add_correspondence _ _ _ _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b))
    (sub_nat_rel_canonical 1)).
Qed.

(** ** Integer subtraction *)

Lemma gg_sub_canonical (x y : int) :
  GelIntRel (x - y)%R (gg_target_sub (gel_int_to_imported x) (gel_int_to_imported y)).
Proof.
  unfold GelIntRel, gg_target_sub.
  destruct x as [m|m], y as [n|n]; cbn [gel_int_to_imported].
  - have Hle := sub_nat_le_correspondence n (sub_nat_to_imported n) m (sub_nat_to_imported m)
      (sub_nat_rel_canonical n) (sub_nat_rel_canonical m).
    destruct (leq n m) eqn:E.
    + rewrite (gg_subz_pp_le m n E). cbn [gel_int_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (P_sub_oo_le _ _ (prop_to_sprop _ _ Hle isT)))).
      exact (sub_imported_eq_congr I.Int_ofNat _ _
        (nat_target_sub_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical n))).
    + rewrite (gg_subz_pp_gt m n (negbT E)). cbn [gel_int_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (P_sub_oo_gt _ _ (fun H => gel_coq_false_to_target
          (Bool.diff_false_true (sprop_to_prop _ _ Hle H)))))).
      exact (sub_imported_eq_congr I.Int_negSucc _ _ (gg_sub1_related n m)).
  - rewrite gg_subz_pn. cbn [gel_int_to_imported].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (P_sub_on _ _))).
    exact (sub_imported_eq_congr I.Int_ofNat _ _ (gg_add1_related m n)).
  - rewrite gg_subz_np. cbn [gel_int_to_imported].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (P_sub_no _ _))).
    exact (sub_imported_eq_congr I.Int_negSucc _ _
      (nat_target_add_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical n))).
  - have Hle := sub_nat_le_correspondence m (sub_nat_to_imported m) n (sub_nat_to_imported n)
      (sub_nat_rel_canonical m) (sub_nat_rel_canonical n).
    destruct (leq m n) eqn:E.
    + rewrite (gg_subz_nn_le m n E). cbn [gel_int_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (P_sub_nn_le _ _ (prop_to_sprop _ _ Hle isT)))).
      exact (sub_imported_eq_congr I.Int_ofNat _ _
        (nat_target_sub_correspondence _ _ _ _ (sub_nat_rel_canonical n) (sub_nat_rel_canonical m))).
    + rewrite (gg_subz_nn_gt m n (negbT E)). cbn [gel_int_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (P_sub_nn_gt _ _ (fun H => gel_coq_false_to_target
          (Bool.diff_false_true (sprop_to_prop _ _ Hle H)))))).
      exact (sub_imported_eq_congr I.Int_negSucc _ _ (gg_sub1_related m n)).
Qed.

Lemma gg_sub_related xR xL yR yL :
  GelIntRel xR xL -> GelIntRel yR yL -> GelIntRel (xR - yR)%R (gg_target_sub xL yL).
Proof.
  intros Hx Hy. unfold GelIntRel.
  exact (sub_imported_eq_trans _ _ _ (gg_sub_canonical xR yR)
    (sub_imported_eq_congr2 gg_target_sub _ _ _ _ Hx Hy)).
Qed.

(** ** [`|_|] *)

Lemma gg_abs_canonical (z : int) :
  SubNatRel `|z| (gg_target_abs (gel_int_to_imported z)).
Proof.
  unfold gg_target_abs.
  destruct z as [n|n]; cbn [gel_int_to_imported].
  - change (SubNatRel n (gg_target_abs (I.Int_ofNat (sub_nat_to_imported n)))).
    exact (sub_imported_eq_trans _ _ _ (sub_nat_rel_canonical n) (sub_imported_eq_sym _ _ (P_abs_o _))).
  - change (SubNatRel n.+1 (gg_target_abs (I.Int_negSucc (sub_nat_to_imported n)))).
    rewrite -addn1.
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (P_abs_n _))).
    exact (nat_target_add_correspondence _ _ _ _ (sub_nat_rel_canonical n) (sub_nat_rel_canonical 1)).
Qed.

Lemma gg_abs_related zR zL :
  GelIntRel zR zL -> SubNatRel `|zR| (gg_target_abs zL).
Proof.
  intro Hz.
  exact (sub_imported_eq_trans _ _ _ (gg_abs_canonical zR)
    (sub_imported_eq_congr gg_target_abs _ _ Hz)).
Qed.

(** ** The literal zero and the Nat cast *)

Lemma gg_zero_related : GelIntRel 0%R (ltac:(let T := type of P_zero in
    match T with @Lean.eq _ ?z _ => exact z end)).
Proof. exact (sub_imported_eq_sym _ _ P_zero). Qed.

Lemma gg_cast_related nR nL :
  SubNatRel nR nL -> GelIntRel (Posz nR)
    (ltac:(let T := type of (P_cast nL) in match T with @Lean.eq _ ?z _ => exact z end)).
Proof.
  intro Hn. unfold GelIntRel. cbn [gel_int_to_imported].
  exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_congr I.Int_ofNat _ _ Hn)
    (sub_imported_eq_sym _ _ (P_cast nL))).
Qed.

(** ** Integer equality *)

Lemma gg_int_eq_correspondence xR xL yR yL :
  GelIntRel xR xL -> GelIntRel yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hx) Hy).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (gel_int_to_imported xR) (gel_int_to_imported yR) :=
      sub_imported_eq_trans _ _ _ Hx (sub_imported_eq_trans _ _ _ Heq (sub_imported_eq_sym _ _ Hy)).
    have Hdecoded := f_equal gel_int_to_rocq (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (offset_rocq_roundtrip_certificate xR) (offset_rocq_roundtrip_certificate yR) in Hdecoded.
    exact Hdecoded.
Qed.

(** The iff connective (as in the accepted ELF-generality certificate). *)
Lemma gg_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [Hpq Hqp]. apply I.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ (Hpq (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP (Hqp (sprop_to_prop _ _ HQ q))).
  - intros [Hpq Hqp]. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ (Hpq (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP (Hqp (prop_to_sprop _ _ HQ q))).
Qed.

(** ** The definition *)

Section Delta.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable ppR : prosa.model.priority.gel.PriorityPoint Task.
  Variable ppL : I.Prosa_Model_Priority_Gel_PriorityPoint Task dT.
  Hypothesis Hpp : GelPriorityPointRel Task ppR ppL.

  Theorem pp_delta_correspondence (x y : Task) :
    GelIntRel (@S.pp_delta Task ppR x y) (I.Prosa_Results_Generality_Gel_pp_delta Task dT ppL x y).
  Proof.
    unfold S.pp_delta. cbn [I.Prosa_Results_Generality_Gel_pp_delta].
    exact (gg_sub_related _ _ _ _ (Hpp y) (Hpp x)).
  Qed.
End Delta.

(** ** The statements *)

Section Generality.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable ppR : prosa.model.priority.gel.PriorityPoint Task.
  Variable ppL : I.Prosa_Model_Priority_Gel_PriorityPoint Task dT.
  Hypothesis Hpp : GelPriorityPointRel Task ppR ppL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jpR : PP.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.
  Variable jrR : @prosa.behavior.ready.JobReady Job PStateR costR jaR.
  Variable jrL : I.Prosa_Behavior_Ready_JobReady Job dJ PStateL costL jaL.
  Hypothesis Hjr : forall schedR schedL, SvcScheduleRel Job PStateR PStateL R schedR schedL ->
    forall (j : Job) (tR : nat) (tL : Lean.Nat), SubNatRel tR tL ->
      ArBoolRel (@prosa.behavior.ready.job_ready Job PStateR costR jaR jrR schedR j tR)
        (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PStateL costL jaL jrL schedL j tL).

  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Let GR := @prosa.model.priority.gel.GEL Job Task ppR jaR jtR.
  Let GL := I.Prosa_Model_Priority_Gel_GEL Job dJ Task dT ppL jaL jtL.

  Lemma gg_jt (j : Job) :
    Logic.eq (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)
      (@prosa.model.task.concept.job_task Job Task jtR j).
  Proof. exact (esym (imported_eq_to_coq_eq _ _ (Hjt j))). Qed.

  (** *** Covers *)

  Definition gg_sched_to_target (sR : SchedR) : SchedL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (sR (sub_nat_to_rocq tL)).
  Definition gg_sched_to_source (sL : SchedL) : SchedR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (sL (sub_nat_to_imported tR)).

  Lemma gg_forall_sched (PR : SchedR -> Prop) (PL : SchedL -> SProp) :
    (forall sR sL, SvcScheduleRel Job PStateR PStateL R sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    apply (isj_forall_cover_sprop _ _ (SvcScheduleRel Job PStateR PStateL R)
      gg_sched_to_target gg_sched_to_source).
    - intros sR tR tL Ht. unfold gg_sched_to_target. rewrite (isj_nat_input _ _ Ht).
      exact (svc_ps_state_rel_canonical Job PStateR PStateL R _).
    - intros sL tR tL Ht. destruct Ht.
      exact (svc_ps_state_rel_surjective Job PStateR PStateL R _).
  Qed.

  (** *** Policies and observations *)

  Lemma gg_gel_rel (x y : Job) :
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job GR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ GL x y).
  Proof. exact (GEL_correspondence Job Task ppR ppL Hpp jaR jaL Hja jtR jtL Hjt x y). Qed.

  Lemma gg_same_task_related (x y : Job) :
    ArBoolRel (@prosa.model.task.concept.same_task Job Task jtR x y)
      (I.Prosa_Model_Task_Concept_same_task Job dJ Task dT jtL x y).
  Proof.
    unfold prosa.model.task.concept.same_task. cbn [I.Prosa_Model_Task_Concept_same_task].
    exact (pd_eq_observation_transport Task _ _ _ _ (Hjt x) (Hjt y)).
  Qed.

  Lemma gg_pp_delta_jobs (x y : Job) :
    GelIntRel (@S.pp_delta Task ppR (@prosa.model.task.concept.job_task Job Task jtR x)
        (@prosa.model.task.concept.job_task Job Task jtR y))
      (I.Prosa_Results_Generality_Gel_pp_delta Task dT ppL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL x)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y)).
  Proof. rewrite !gg_jt. exact (pp_delta_correspondence Task ppR ppL Hpp _ _). Qed.

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : SvcScheduleRel Job PStateR PStateL R sR sL.

    Let Hsa := pp_scheduled_at_related Job PStateR PStateL R sR sL Hs.

    Lemma gg_rtb_related (j : Job) dR dL :
      SubNatRel dR dL ->
      ArBoolRel (@prosa.behavior.service.job_response_time_bound Job PStateR sR costR jaR j dR)
        (I.Prosa_Behavior_Service_job_response_time_bound Job dJ PStateL sL costL jaL j dL).
    Proof.
      intro Hd. unfold prosa.behavior.service.job_response_time_bound.
      cbn [I.Prosa_Behavior_Service_job_response_time_bound].
      exact (pp_completed_by_related Job costR costL Hcost PStateR PStateL R sR sL Hs j _ _
        (svc_target_add_related _ _ _ _ (Hja j) Hd)).
    Qed.

    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Lemma gg_respects_gel_rel :
      PropSPropRel (@PDS.respects_JLFP_policy_at_preemption_point Job jaR costR PStateR jpR jrR arrR sR GR)
        (I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point
          Job dJ jaL costL PStateL jpL jrL arrL sL GL).
    Proof.
      exact (respects_JLFP_policy_at_preemption_point_correspondence Job jaR jaL costR costL PStateR PStateL R
        jpR jpL Hjp jrR jrL Hjr arrR arrL Harr sR sL Hs GR GL gg_gel_rel).
    Qed.

    Lemma gg_valid_schedule_rel :
      PropSPropRel (@prosa.behavior.ready.valid_schedule Job jaR PStateR sR costR jrR arrR)
        (I.Prosa_Behavior_Ready_valid_schedule Job dJ jaL PStateL sL costL jrL arrL).
    Proof.
      unfold prosa.behavior.ready.valid_schedule, prosa.behavior.ready.jobs_must_be_ready_to_execute,
        prosa.behavior.ready.jobs_come_from_arrival_sequence.
      cbn [I.Prosa_Behavior_Ready_valid_schedule I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute
        I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence].
      apply ar_and_correspondence.
      - apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j _ _ Ht))|].
        exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      - apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j _ _ Ht))|].
        exact (ar_bool_truth_correspondence _ _ (Hjr sR sL Hs j tR tL Ht)).
    Qed.

    Lemma gg_sequential_tasks_rel :
      PropSPropRel (@prosa.model.task.sequentiality.sequential_tasks Job Task jtR jaR costR PStateR arrR sR)
        (I.Prosa_Model_Task_Sequentiality_sequential_tasks Job dJ Task dT jtL jaL costL PStateL arrL sL).
    Proof.
      unfold prosa.model.task.sequentiality.sequential_tasks.
      cbn [I.Prosa_Model_Task_Sequentiality_sequential_tasks].
      apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j1 Harr)|].
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j2 Harr)|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (gg_same_task_related j1 j2))|].
      apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j2 _ _ Ht))|].
      exact (ar_bool_truth_correspondence _ _
        (pp_completed_by_related Job costR costL Hcost PStateR PStateL R sR sL Hs j1 tR tL Ht)).
    Qed.
  End Sched.

  (** *** gel_generalizes_edf *)

  Section Edf.
    Variable tdR : prosa.model.task.concept.TaskDeadline Task.
    Variable tdL : I.Prosa_Model_Task_Concept_TaskDeadline Task dT.
    Hypothesis Htd : forall tsk : Task,
      SubNatRel (@prosa.model.task.concept.task_deadline Task tdR tsk)
        (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL tsk).

    Lemma gg_deadline_related (j : Job) :
      SubNatRel (@prosa.behavior.job.job_arrival Job jaR j
          + @prosa.model.task.concept.task_deadline Task tdR (@prosa.model.task.concept.job_task Job Task jtR j))
        (nat_target_add (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j)
          (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL
            (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j))).
    Proof. rewrite gg_jt. exact (nat_target_add_correspondence _ _ _ _ (Hja j) (Htd _)). Qed.

    Definition src_gel_generalizes_edf : Prop :=
      ltac:(body_of (fun s : S.statement_gel_generalizes_edf => s Task ppR Job jtR PStateR jaR costR jpR jrR tdR)).
    Definition tgt_gel_generalizes_edf : SProp :=
      ltac:(type_of_term (@I.Prosa_Results_Generality_Gel_gel_generalizes_edf
        Task dT Job dJ ppL jtL PStateL jaL costL jpL jrL tdL)).

    Theorem gel_generalizes_edf_correspondence : PropSPropRel src_gel_generalizes_edf tgt_gel_generalizes_edf.
    Proof.
      unfold src_gel_generalizes_edf, tgt_gel_generalizes_edf.
      apply ar_imp_correspondence.
      - apply ar_forall_identity_correspondence. intro tsk.
        exact (gg_int_eq_correspondence _ _ _ _ (Hpp tsk) (gg_cast_related _ _ (Htd tsk))).
      - apply gg_forall_sched. intros sR sL Hs.
        apply fpre_forall_arr. intros arrR arrL Harr.
        refine (gg_iff_correspondence _ _ _ _ (gg_respects_gel_rel sR sL Hs arrR arrL Harr)
          (respects_JLFP_policy_at_preemption_point_correspondence Job jaR jaL costR costL PStateR PStateL R
            jpR jpL Hjp jrR jrL Hjr arrR arrL Harr sR sL Hs _ _ _)).
        intros x y.
        exact (pd_decide_le_related _ _ _ _ (gg_deadline_related x) (gg_deadline_related y)).
    Qed.
  End Edf.

  (** *** gel_generalizes_fifo *)

  Definition src_gel_generalizes_fifo : Prop :=
    ltac:(body_of (fun s : S.statement_gel_generalizes_fifo => s Task ppR Job jtR PStateR jaR costR jpR jrR)).
  Definition tgt_gel_generalizes_fifo : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Generality_Gel_gel_generalizes_fifo
      Task dT Job dJ ppL jtL PStateL jaL costL jpL jrL)).

  Theorem gel_generalizes_fifo_correspondence : PropSPropRel src_gel_generalizes_fifo tgt_gel_generalizes_fifo.
  Proof.
    unfold src_gel_generalizes_fifo, tgt_gel_generalizes_fifo.
    apply ar_imp_correspondence.
    - apply ar_forall_identity_correspondence. intro tsk.
      exact (gg_int_eq_correspondence _ _ _ _ (Hpp tsk) gg_zero_related).
    - apply gg_forall_sched. intros sR sL Hs.
      apply fpre_forall_arr. intros arrR arrL Harr.
      refine (gg_iff_correspondence _ _ _ _ (gg_respects_gel_rel sR sL Hs arrR arrL Harr)
        (respects_JLFP_policy_at_preemption_point_correspondence Job jaR jaL costR costL PStateR PStateL R
          jpR jpL Hjp jrR jrL Hjr arrR arrL Harr sR sL Hs _ _ _)).
      intros x y.
      exact (pd_decide_le_related _ _ _ _ (Hja x) (Hja y)).
  Qed.

  (** *** backlogged_job_has_lower_gel_prio *)

  Definition src_backlogged_job_has_lower_gel_prio : Prop :=
    ltac:(body_of (fun s : S.statement_backlogged_job_has_lower_gel_prio =>
      s Task ppR Job jtR PStateR jaR costR jrR)).
  Definition tgt_backlogged_job_has_lower_gel_prio : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Generality_Gel_backlogged_job_has_lower_gel_prio
      Task dT Job dJ ppL jtL PStateL jaL costL jrL)).

  Theorem backlogged_job_has_lower_gel_prio_correspondence :
    PropSPropRel src_backlogged_job_has_lower_gel_prio tgt_backlogged_job_has_lower_gel_prio.
  Proof.
    unfold src_backlogged_job_has_lower_gel_prio, tgt_backlogged_job_has_lower_gel_prio.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j'.
    apply gg_forall_sched. intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    have HD := gg_pp_delta_jobs j j'.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (gel_le_related _ _ _ _ gg_zero_related HD))|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (gg_rtb_related sR sL Hs j' _ _ (gg_abs_related _ _ HD)))|].
    apply ar_imp_correspondence.
    { unfold prosa.behavior.arrival_sequence.has_arrived.
      cbn [I.Prosa_Behavior_Arrival_sequence_has_arrived].
      exact (ar_bool_truth_correspondence _ _ (svc_decide_le_related _ _ _ _ (Hja j) Ht)). }
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _
        (pdrv_backlogged_related Job jaR jaL costR costL PStateR PStateL R jrR jrL Hjr sR sL Hs j' _ _ Ht))|].
    exact (ar_bool_truth_correspondence _ _ (gg_gel_rel j j')).
  Qed.

  (** *** gel_conditionally_generalizes_fp *)

  Variable fpR : prosa.model.priority.definitions.FP_policy Task.
  Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hfp : PdFPRel Task fpR fpL.

  Lemma gg_hep_task_jobs (x y : Job) :
    ArBoolRel (@prosa.model.priority.definitions.hep_task Task fpR
        (@prosa.model.task.concept.job_task Job Task jtR x) (@prosa.model.task.concept.job_task Job Task jtR y))
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL x)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y)).
  Proof. rewrite !gg_jt. exact (Hfp _ _). Qed.

  Lemma gg_hp_task_jobs (x y : Job) :
    ArBoolRel (@prosa.model.priority.definitions.hp_task Task fpR
        (@prosa.model.task.concept.job_task Job Task jtR x) (@prosa.model.task.concept.job_task Job Task jtR y))
      (I.Prosa_Model_Priority_Definitions_hp_task Task dT fpL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL x)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y)).
  Proof.
    rewrite !gg_jt. unfold prosa.model.priority.definitions.hp_task.
    cbn [I.Prosa_Model_Priority_Definitions_hp_task].
    exact (pd_bool_and_related _ _ _ _ (Hfp _ _) (pd_bool_not_related _ _ (Hfp _ _))).
  Qed.

  Definition src_gel_conditionally_generalizes_fp : Prop :=
    ltac:(body_of (fun s : S.statement_gel_conditionally_generalizes_fp =>
      s Task ppR Job jtR PStateR jaR costR jpR jrR fpR)).
  Definition tgt_gel_conditionally_generalizes_fp : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Generality_Gel_gel_conditionally_generalizes_fp
      Task dT Job dJ ppL jtL PStateL jaL costL jpL jrL fpL)).

  Theorem gel_conditionally_generalizes_fp_correspondence :
    PropSPropRel src_gel_conditionally_generalizes_fp tgt_gel_conditionally_generalizes_fp.
  Proof.
    unfold src_gel_conditionally_generalizes_fp, tgt_gel_conditionally_generalizes_fp.
    apply ar_imp_correspondence; [exact (pd_reflexive_task_priorities_certificate Task fpR fpL Hfp)|].
    apply ar_imp_correspondence; [exact (pd_total_task_priorities_certificate Task fpR fpL Hfp)|].
    apply fpre_forall_arr. intros arrR arrL Harr.
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_identity_correspondence. intro j'.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j' Harr)|].
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (pd_bool_not_related _ _ (gg_same_task_related j j')))|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (gg_hep_task_jobs j j'))|].
      exact (ar_bool_truth_correspondence _ _ (gg_hp_task_jobs j j')). }
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_identity_correspondence. intro j'.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j' Harr)|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (gg_hp_task_jobs j j'))|].
      exact (ar_bool_truth_correspondence _ _ (gel_le_related _ _ _ _ gg_zero_related (gg_pp_delta_jobs j j'))). }
    apply gg_forall_sched. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (gg_valid_schedule_rel sR sL Hs arrR arrL Harr)|].
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_identity_correspondence. intro j'.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j' Harr)|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (gg_hp_task_jobs j j'))|].
      exact (ar_bool_truth_correspondence _ _
        (gg_rtb_related sR sL Hs j' _ _ (gg_abs_related _ _ (gg_pp_delta_jobs j j')))). }
    apply ar_imp_correspondence; [exact (gg_sequential_tasks_rel sR sL Hs arrR arrL Harr)|].
    exact (gg_iff_correspondence _ _ _ _ (gg_respects_gel_rel sR sL Hs arrR arrL Harr)
      (respects_FP_policy_at_preemption_point_correspondence Job jaR jaL costR costL PStateR PStateL R
        jpR jpL Hjp jrR jrL Hjr arrR arrL Harr sR sL Hs Task jtR jtL Hjt fpR fpL Hfp)).
  Qed.
End Generality.
