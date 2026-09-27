From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import AbstractRtaSemanticSource.
From prosa Require Import analysis.abstract.definitions analysis.abstract.search_space model.job.properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedAbstractRta ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  WorkloadCorrespondence
  AbstractDefinitionsBaseAdapter ServiceBaseAdapter ServiceNatBoolOperations
  AbstractDefinitionsArrivalOperations AbstractDefinitionsClasses AbstractDefinitionsNatBoolOperations
  AbstractDefinitionsIntervalOperations AbstractDefinitionsOperations AbstractDefinitionsSums
  AbstractDefinitionsLogical ServiceIntervalOperations ServiceScheduleOperations
  AbstractDefinitionsPendingOperations AbstractDefinitionsTaskOperations
  AbstractDefinitionsBusyIntervalHelpers.

Module I := ImportedAbstractRta.
Module S := AbstractRtaSemanticSource.AbstractRtaSemanticSource.
Module SSO := FoundationCertificates.ServiceScheduleOperations.
Module TPP := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module SCH := SchedulabilitySemanticSource.SchedulabilitySemanticSource.

(** Correspondences for [analysis/abstract/abstract_rta.v].

    Source side: the two extracted definition blocks and the extracted
    statements [S.statement_X] specialised at their leading inputs; target
    side: the compiled Lean definitions and the imported Lean theorem types.
    Inputs: processor states by the accepted two-sided [SvcProcessorStateRel]
    of the abstract-definitions family and schedules through it;
    [job_arrival] and [job_cost] pointwise by [SubNatRel]; [JobTask] by the
    accepted [AdJobTaskRel]; [task_cost] and [task_rtct] pointwise by
    [SubNatRel]; arrival sequences by the accepted [ArArrivalSequenceRel]
    (the abstract family's relation is the same one, by conversion).
    Inputs quantified inside a statement are covered in both directions by
    explicit conversions: task sets ([ArListRel]), [Interference] and
    [InterferingWorkload] (accepted abstract relations), interference-bound
    functions (pointwise [SubNatRel] on related arguments), jobs and tasks
    (identity), instants and durations ([SubNatRel]).  The abstract
    busy-interval notions, work conservation, bounded busy intervals and the
    job interference bound are related by the accepted abstract-definitions
    certificates; service and completion by the accepted service
    certificates; task-set membership by the accepted arrival certificate.
    The search-space predicate (pinned source), the schedulability and
    job-cost-validity definitions are related by unfolding both sides.  No
    source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators *)

Lemma arta_forall_cover (A B : Type) (Rel : A -> B -> SProp)
    (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b)
    (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a.
    exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma arta_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intros [].
  - intro H. apply strictly_inhabits. exact (interpret_strict _ (ar_target_false_to_strict H)).
Qed.

Lemma arta_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p | q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intros [p | q]; apply strictly_inhabits.
    + left. exact (sprop_to_prop _ _ HP p).
    + right. exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma arta_and3_correspondence (b1 b2 : bool) (P : Prop) (Q1 Q2 PL : SProp) :
  PropSPropRel (is_true b1) Q1 -> PropSPropRel (is_true b2) Q2 -> PropSPropRel P PL ->
  PropSPropRel (is_true (b1 && b2) /\ P) (And Q1 (And Q2 PL)).
Proof.
  intros H1 H2 HP.
  have R := ad_and_correspondence _ _ _ _ H1 (ad_and_correspondence _ _ _ _ H2 HP).
  apply prop_sprop_rel_intro.
  - intros [Hb Hp]. apply (prop_to_sprop _ _ R).
    move/andP: Hb => [h1 h2]. by split; [|split].
  - intro HL. apply strictly_inhabits.
    move: (sprop_to_prop _ _ R HL) => [h1 [h2 hp]].
    split; [apply/andP; split|]; assumption.
Qed.

Lemma arta_nat_neq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (aR <> bR) (I.Ne Lean.Nat aL bL).
Proof.
  intros Ha Hb. unfold I.Ne, I.Not.
  apply ad_imp_correspondence.
  - exact (sub_nat_eq_correspondence aR aL bR bL Ha Hb).
  - exact arta_false_correspondence.
Qed.

Lemma arta_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma arta_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma arta_add_related (aR : nat) (aL : Lean.Nat) (bR : nat) (bL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Lemma arta_sub_related (aR : nat) (aL : Lean.Nat) (bR : nat) (bL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat) aL bL).
Proof. exact (svc_target_sub_related aR aL bR bL). Qed.

(** Interference-bound functions, related pointwise on related arguments. *)
Definition ArtaFunRel (fR : nat -> nat -> nat) (fL : Lean.Nat -> Lean.Nat -> Lean.Nat) : SProp :=
  forall xR xL dR dL, SubNatRel xR xL -> SubNatRel dR dL -> SubNatRel (fR xR dR) (fL xL dL).

Definition arta_fun_to_target (fR : nat -> nat -> nat) : Lean.Nat -> Lean.Nat -> Lean.Nat :=
  fun xL dL => sub_nat_to_imported (fR (sub_nat_to_rocq xL) (sub_nat_to_rocq dL)).
Definition arta_fun_to_source (fL : Lean.Nat -> Lean.Nat -> Lean.Nat) : nat -> nat -> nat :=
  fun xR dR => sub_nat_to_rocq (fL (sub_nat_to_imported xR) (sub_nat_to_imported dR)).

Lemma arta_fun_to_target_rel fR : ArtaFunRel fR (arta_fun_to_target fR).
Proof.
  intros xR xL dR dL Hx Hd. unfold arta_fun_to_target.
  rewrite (arta_nat_input _ _ Hx) (arta_nat_input _ _ Hd).
  exact (sub_nat_rel_canonical _).
Qed.

Lemma arta_fun_to_source_rel fL : ArtaFunRel (arta_fun_to_source fL) fL.
Proof.
  intros xR xL dR dL Hx Hd. destruct Hx. destruct Hd.
  exact (sub_nat_imported_roundtrip _).
Qed.

Lemma arta_forall_fun (PR : (nat -> nat -> nat) -> Prop) (PL : (Lean.Nat -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, ArtaFunRel fR fL -> PropSPropRel (PR fR) (PL fL)) ->
  PropSPropRel (forall f, PR f) (forall f, PL f).
Proof.
  exact (arta_forall_cover _ _ ArtaFunRel arta_fun_to_target arta_fun_to_source
    arta_fun_to_target_rel arta_fun_to_source_rel PR PL).
Qed.

(** Task sets. *)
Lemma arta_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xsR xsL, ArListRel xsR xsL -> PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (forall xs, PR xs) (forall xs, PL xs).
Proof.
  apply (arta_forall_cover _ _ ArListRel ar_list_to_imported ar_list_to_rocq).
  - intro xs. exact (@Lean.eq_refl _ _).
  - intro xs. exact (ar_list_target_roundtrip xs).
Qed.

(** The search-space predicate and bounded equivalence (pinned source). *)
Lemma arta_equivalent_rel (fR gR : nat -> nat) (fL gL : Lean.Nat -> Lean.Nat) BR BL :
  (forall xR xL, SubNatRel xR xL -> SubNatRel (fR xR) (fL xL)) ->
  (forall xR xL, SubNatRel xR xL -> SubNatRel (gR xR) (gL xL)) ->
  SubNatRel BR BL ->
  PropSPropRel (@prosa.analysis.abstract.search_space.are_equivalent_at_values_less_than _ fR gR BR)
    (I.Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than_inst1 Lean.Nat
      I.instDecidableEqNat fL gL BL).
Proof.
  intros Hf Hg HB.
  unfold prosa.analysis.abstract.search_space.are_equivalent_at_values_less_than.
  cbn [I.Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than_inst1].
  apply ad_forall_nat_correspondence. intros xR xL Hx.
  apply ad_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Hx HB)|].
  exact (sub_nat_eq_correspondence _ _ _ _ (Hf _ _ Hx) (Hg _ _ Hx)).
Qed.

Lemma arta_search_space_rel (fR : nat -> nat -> nat) (fL : Lean.Nat -> Lean.Nat -> Lean.Nat) BR BL AR AL :
  ArtaFunRel fR fL -> SubNatRel BR BL -> SubNatRel AR AL ->
  PropSPropRel (@prosa.analysis.abstract.search_space.is_in_search_space BR fR AR)
    (I.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space BL fL AL).
Proof.
  intros Hf HB HA.
  unfold prosa.analysis.abstract.search_space.is_in_search_space,
    prosa.analysis.abstract.search_space.are_not_equivalent_at_values_less_than.
  cbn [I.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
    I.Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than_inst1].
  apply arta_or_correspondence;
    [exact (sub_nat_eq_correspondence _ _ _ _ HA (sub_nat_rel_canonical O))|].
  apply arta_and3_correspondence.
  - exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HA).
  - exact (sub_nat_lt_correspondence _ _ _ _ HA HB).
  - apply ad_exists_nat_correspondence. intros xR xL Hx.
    apply ad_and_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Hx HB)|].
    have HA1 := arta_sub_related _ _ _ _ HA (sub_nat_rel_canonical (S O)).
    exact (arta_nat_neq_correspondence _ _ _ _ (Hf _ _ _ _ HA1 Hx) (Hf _ _ _ _ HA Hx)).
Qed.

Section AbstractRta.
  Context (Task Job : eqType).
  Let dT := ad_decidable_eq Task.
  Let dJ := ad_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SSO.SvcProcessorStateRel Job PStateR PStateL.
  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.

  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable rtcR : TPP.TaskRunToCompletionThreshold Task.
  Variable rtcL : I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task dT.
  Hypothesis Hrtc : forall tsk : Task,
    SubNatRel (@TPP.task_rtct Task rtcR tsk)
      (I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task dT rtcL tsk).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : AdJobTaskRel Job Task jtR jtL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).

  Variable sR : SchedR.
  Variable sL : SchedL.
  Hypothesis Hs : SSO.SvcScheduleRel Job PStateR PStateL R sR sL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma arta_arr_ad : AdArrivalSequenceRel Job arrR arrL.
  Proof. exact Harr. Qed.

  (** *** Covers for instances quantified inside a statement *)

  Definition arta_inter_to_target (iR : prosa.analysis.abstract.definitions.Interference Job) :
      I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ :=
    I.Prosa_Analysis_Abstract_Definitions_Interference_mk Job dJ
      (fun j tL => ad_bool_to_imported (@prosa.analysis.abstract.definitions.interference Job iR j
        (sub_nat_to_rocq tL))).
  Definition arta_inter_to_source (iL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ) :
      prosa.analysis.abstract.definitions.Interference Job :=
    ((fun j tR => ad_bool_to_rocq
      (I.Prosa_Analysis_Abstract_Definitions_Interference_interference Job dJ iL j (sub_nat_to_imported tR)))
      : prosa.analysis.abstract.definitions.Interference Job).

  Lemma arta_forall_inter (PR : prosa.analysis.abstract.definitions.Interference Job -> Prop)
      (PL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ -> SProp) :
    (forall iR iL, AdInterferenceRel Job iR iL -> PropSPropRel (PR iR) (PL iL)) ->
    PropSPropRel (forall i, PR i) (forall i, PL i).
  Proof.
    apply (arta_forall_cover _ _ (AdInterferenceRel Job) arta_inter_to_target arta_inter_to_source).
    - intros iR j t. unfold AdBoolRel. cbn. rewrite sub_nat_rocq_roundtrip. exact (@Lean.eq_refl _ _).
    - intros iL j t. exact (ad_bool_target_roundtrip _).
  Qed.

  Definition arta_iw_to_target (wR : prosa.analysis.abstract.definitions.InterferingWorkload Job) :
      I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ :=
    I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload_mk Job dJ
      (fun j tL => sub_nat_to_imported (@prosa.analysis.abstract.definitions.interfering_workload Job wR j
        (sub_nat_to_rocq tL))).
  Definition arta_iw_to_source (wL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ) :
      prosa.analysis.abstract.definitions.InterferingWorkload Job :=
    ((fun j tR => sub_nat_to_rocq
      (I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload_interfering_workload Job dJ wL j
        (sub_nat_to_imported tR)))
      : prosa.analysis.abstract.definitions.InterferingWorkload Job).

  Lemma arta_forall_iw (PR : prosa.analysis.abstract.definitions.InterferingWorkload Job -> Prop)
      (PL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ -> SProp) :
    (forall wR wL, AdInterferingWorkloadRel Job wR wL -> PropSPropRel (PR wR) (PL wL)) ->
    PropSPropRel (forall w, PR w) (forall w, PL w).
  Proof.
    apply (arta_forall_cover _ _ (AdInterferingWorkloadRel Job) arta_iw_to_target arta_iw_to_source).
    - intros wR j t. unfold SubNatRel. cbn. rewrite sub_nat_rocq_roundtrip. exact (@Lean.eq_refl _ _).
    - intros wL j t. exact (sub_nat_imported_roundtrip _).
  Qed.

  (** *** Observations that do not depend on the abstract model *)

  Lemma arta_cost_positive_related (j : Job) :
    SvcBoolRel (@prosa.model.job.properties.job_cost_positive Job costR j)
      (I.Prosa_Model_Job_Properties_job_cost_positive Job dJ costL j).
  Proof.
    unfold prosa.model.job.properties.job_cost_positive.
    exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost j)).
  Qed.

  Lemma arta_task_cost_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (arta_lean_transport
      (fun x => SubNatRel (@prosa.model.task.concept.task_cost Task tcR
          (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL x))
      _ _ (Hjt j) (Htc (@prosa.model.task.concept.job_task Job Task jtR j))).
  Qed.

  Lemma arta_valid_job_costs_rel :
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
  Proof.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs, prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs I.Prosa_Model_Task_Concept_valid_job_cost].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j arta_arr_ad)|].
    exact (ad_bool_truth_correspondence _ _
      (svc_decide_le_related _ _ _ _ (Hcost j) (arta_task_cost_of_job_related j))).
  Qed.

  Lemma arta_response_time_bound_rel (tsk : Task) RR RL :
    SubNatRel RR RL ->
    PropSPropRel (@SCH.task_response_time_bound Task Job jaR costR jtR PStateR arrR sR tsk RR)
      (I.Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task dT Job dJ jaL costL jtL
        PStateL arrL sL tsk RL).
  Proof.
    intro HR. unfold SCH.task_response_time_bound, prosa.behavior.service.job_response_time_bound.
    cbn [I.Prosa_Analysis_Definitions_Schedulability_task_response_time_bound
      I.Prosa_Behavior_Service_job_response_time_bound].
    apply ad_forall_identity_correspondence. intro j.
    apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j arta_arr_ad)|].
    apply ad_imp_correspondence;
      [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
    exact (ad_bool_truth_correspondence _ _
      (ad_completed_by_related Job PStateR PStateL R sR sL Hs costR costL Hcost j _ _
        (arta_add_related _ _ _ _ (Hja j) HR))).
  Qed.

  (** *** Model-dependent notions, for any related abstract model *)

  Section Model.
    Variable interR : prosa.analysis.abstract.definitions.Interference Job.
    Variable interL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ.
    Hypothesis Hinter : AdInterferenceRel Job interR interL.
    Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
    Variable workloadL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ.
    Hypothesis Hworkload : AdInterferingWorkloadRel Job workloadR workloadL.

    Lemma arta_bi_rel j t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
      PropSPropRel (@prosa.analysis.abstract.definitions.busy_interval Job jaR costR PStateR sR
          interR workloadR j t1R t2R)
        (I.Prosa_Analysis_Abstract_Definitions_busy_interval Job dJ interL workloadL jaL costL
          PStateL sL j t1L t2L).
    Proof.
      exact (ad_busy_interval_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
        interR interL Hinter workloadR workloadL Hworkload j t1R t2R t1L t2L H1 H2).
    Qed.

    Lemma arta_wc_rel :
      PropSPropRel (@prosa.analysis.abstract.definitions.work_conserving Job jaR costR PStateR arrR sR
          interR workloadR)
        (I.Prosa_Analysis_Abstract_Definitions_work_conserving Job dJ interL workloadL jaL costL
          PStateL arrL sL).
    Proof.
      exact (ad_work_conserving_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR costL Hcost
        interR interL Hinter workloadR workloadL Hworkload arrR arrL arta_arr_ad).
    Qed.

    Lemma arta_bounded_rel (tsk : Task) LR LL (HL : SubNatRel LR LL) :
      PropSPropRel (@prosa.analysis.abstract.definitions.busy_intervals_are_bounded_by Job Task jtR jaR
          costR PStateR arrR sR tsk interR workloadR LR)
        (I.Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by Job dJ interL workloadL jaL
          costL PStateL arrL sL Task dT jtL tsk LL).
    Proof.
      exact (ad_busy_intervals_bounded_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja costR
        costL Hcost interR interL Hinter workloadR workloadL Hworkload arrR arrL arta_arr_ad Task jtR jtL
        Hjt tsk LR LL HL).
    Qed.

    Lemma arta_job_interference_bounded_rel (tsk : Task) IBFR IBFL (HIBF : ArtaFunRel IBFR IBFL)
        (ParamR : Job -> nat -> Prop) (ParamL : Job -> Lean.Nat -> SProp)
        (HParam : forall j xR xL, SubNatRel xR xL -> PropSPropRel (ParamR j xR) (ParamL j xL)) :
      PropSPropRel (@prosa.analysis.abstract.definitions.job_interference_is_bounded_by Job Task jtR jaR
          costR PStateR arrR sR tsk interR workloadR IBFR ParamR)
        (I.Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by Job dJ interL workloadL jaL
          costL PStateL arrL sL Task dT jtL tsk IBFL ParamL).
    Proof.
      unfold prosa.analysis.abstract.definitions.job_interference_is_bounded_by.
      cbn [I.Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by].
      refine (ad_cond_interference_bounded_correspondence Job PStateR PStateL R sR sL Hs jaR jaL Hja
        costR costL Hcost interR interL Hinter workloadR workloadL Hworkload arrR arrL arta_arr_ad Task
        jtR jtL Hjt tsk IBFR IBFL HIBF ParamR ParamL HParam _ _ _).
      intros j t. exact (@Lean.eq_refl _ _).
    Qed.

    (** *** The two definitions *)

    Theorem relative_arrival_time_of_job_is_A_correspondence (j : Job) AR AL :
      SubNatRel AR AL ->
      PropSPropRel (@S.relative_arrival_time_of_job_is_A Job jaR costR PStateR sR interR workloadR j AR)
        (I.Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A Job dJ jaL costL PStateL sL
          interL workloadL j AL).
    Proof.
      intro HA. unfold S.relative_arrival_time_of_job_is_A.
      cbn [I.Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A].
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (arta_bi_rel j _ _ _ _ H1 H2)|].
      exact (sub_nat_eq_correspondence _ _ _ _ HA (arta_sub_related _ _ _ _ (Hja j) H1)).
    Qed.

    Theorem relative_time_to_reach_rtct_correspondence (tsk : Task) IBFR IBFL (HIBF : ArtaFunRel IBFR IBFL)
        (j : Job) FR FL :
      SubNatRel FR FL ->
      PropSPropRel (@S.relative_time_to_reach_rtct Task rtcR Job jaR costR PStateR sR tsk interR workloadR
          IBFR j FR)
        (I.Prosa_Analysis_Abstract_AbstractRta_relative_time_to_reach_rtct Task dT rtcL Job dJ jaL costL
          PStateL sL tsk interL workloadL IBFL j FL).
    Proof.
      intro HF. unfold S.relative_time_to_reach_rtct.
      cbn [I.Prosa_Analysis_Abstract_AbstractRta_relative_time_to_reach_rtct].
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (arta_bi_rel j _ _ _ _ H1 H2)|].
      apply ad_and_correspondence.
      - exact (sub_nat_le_correspondence _ _ _ _
          (arta_add_related _ _ _ _ (Hrtc tsk) (HIBF _ _ _ _ (arta_sub_related _ _ _ _ (Hja j) H1) HF)) HF).
      - exact (sub_nat_le_correspondence _ _ _ _ (Hrtc tsk)
          (ad_service_related Job PStateR PStateL R sR sL Hs j _ _ (arta_add_related _ _ _ _ H1 HF))).
    Qed.

    Let RelA j AR AL (HA : SubNatRel AR AL) := relative_arrival_time_of_job_is_A_correspondence j AR AL HA.

    (** *** Shared statement fragments *)

    Lemma arta_ibfp_bounded_rel (tsk : Task) IBFR IBFL (HIBF : ArtaFunRel IBFR IBFL) :
      PropSPropRel (@prosa.analysis.abstract.definitions.job_interference_is_bounded_by Job Task jtR jaR
          costR PStateR arrR sR tsk interR workloadR IBFR
          (@S.relative_arrival_time_of_job_is_A Job jaR costR PStateR sR interR workloadR))
        (I.Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by Job dJ interL workloadL jaL
          costL PStateL arrL sL Task dT jtL tsk IBFL
          (I.Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A Job dJ jaL costL PStateL
            sL interL workloadL)).
    Proof. exact (arta_job_interference_bounded_rel tsk IBFR IBFL HIBF _ _ RelA). Qed.

    Lemma arta_ibfnp_bounded_rel (tsk : Task) IBFPR IBFPL (HP : ArtaFunRel IBFPR IBFPL)
        IBFR IBFL (HIBF : ArtaFunRel IBFR IBFL) :
      PropSPropRel (@prosa.analysis.abstract.definitions.job_interference_is_bounded_by Job Task jtR jaR
          costR PStateR arrR sR tsk interR workloadR IBFR
          (@S.relative_time_to_reach_rtct Task rtcR Job jaR costR PStateR sR tsk interR workloadR IBFPR))
        (I.Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by Job dJ interL workloadL jaL
          costL PStateL arrL sL Task dT jtL tsk IBFL
          (I.Prosa_Analysis_Abstract_AbstractRta_relative_time_to_reach_rtct Task dT rtcL Job dJ jaL costL
            PStateL sL tsk interL workloadL IBFPL)).
    Proof.
      exact (arta_job_interference_bounded_rel tsk IBFR IBFL HIBF _ _
        (fun j xR xL Hx => relative_time_to_reach_rtct_correspondence tsk IBFPR IBFPL HP j xR xL Hx)).
    Qed.
  End Model.

  (** ** Statement correspondences *)

  Let BI iR iL Hi wR wL Hw j t1R t1L t2R t2L H1 H2 := arta_bi_rel iR iL Hi wR wL Hw j t1R t1L t2R t2L H1 H2.
  Let SUB := arta_sub_related.
  Let ADD := arta_add_related.
  Let LE := sub_nat_le_correspondence.
  Let LT := sub_nat_lt_correspondence.

  Section LeadingModel.
    Variable interR : prosa.analysis.abstract.definitions.Interference Job.
    Variable interL : I.Prosa_Analysis_Abstract_Definitions_Interference Job dJ.
    Hypothesis Hinter : AdInterferenceRel Job interR interL.
    Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
    Variable workloadL : I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job dJ.
    Hypothesis Hworkload : AdInterferingWorkloadRel Job workloadR workloadL.

    Let BIm j t1R t1L t2R t2L H1 H2 := BI interR interL Hinter workloadR workloadL Hworkload j t1R t1L t2R t2L H1 H2.

    (** *** job_arrival_eq_t1_plus_A *)

    Definition src_job_arrival_eq_t1_plus_A : Prop :=
      ltac:(body_of (fun s : S.statement_job_arrival_eq_t1_plus_A =>
        s Job jaR costR PStateR sR interR workloadR)).
    Definition tgt_job_arrival_eq_t1_plus_A : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_AbstractRta_job_arrival_eq_t1_plus_A
        Job dJ jaL costL PStateL sL interL workloadL)).

    Theorem job_arrival_eq_t1_plus_A_correspondence :
      PropSPropRel src_job_arrival_eq_t1_plus_A tgt_job_arrival_eq_t1_plus_A.
    Proof.
      unfold src_job_arrival_eq_t1_plus_A, tgt_job_arrival_eq_t1_plus_A.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BIm j _ _ _ _ H1 H2)|].
      exact (sub_nat_eq_correspondence _ _ _ _ (Hja j) (ADD _ _ _ _ H1 (SUB _ _ _ _ (Hja j) H1))).
    Qed.

    (** *** relative_arrival_is_bounded *)

    Definition src_relative_arrival_is_bounded (tsk : Task) : Prop :=
      ltac:(body_of (fun s : S.statement_relative_arrival_is_bounded =>
        s Task Job jtR jaR costR PStateR arrR sR tsk interR workloadR)).
    Definition tgt_relative_arrival_is_bounded (tsk : Task) : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_AbstractRta_relative_arrival_is_bounded
        Task dT Job dJ jtL jaL costL PStateL arrL sL tsk interL workloadL)).

    Theorem relative_arrival_is_bounded_correspondence (tsk : Task) :
      PropSPropRel (src_relative_arrival_is_bounded tsk) (tgt_relative_arrival_is_bounded tsk).
    Proof.
      unfold src_relative_arrival_is_bounded, tgt_relative_arrival_is_bounded.
      apply ad_forall_nat_correspondence. intros LR LL HL.
      apply ad_imp_correspondence;
        [exact (arta_bounded_rel interR interL Hinter workloadR workloadL Hworkload tsk LR LL HL)|].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j arta_arr_ad)|].
      apply ad_imp_correspondence;
        [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (arta_cost_positive_related j))|].
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BIm j _ _ _ _ H1 H2)|].
      exact (LT _ _ _ _ (SUB _ _ _ _ (Hja j) H1) HL).
    Qed.

    (** *** t2_le_arrival_plus_R_1 and job_completed_by_arrival_plus_R_1 *)

    Definition src_t2_le_arrival_plus_R_1 (tsk : Task) : Prop :=
      ltac:(body_of (fun s : S.statement_t2_le_arrival_plus_R_1 =>
        s Task tcR Job jaR costR PStateR sR tsk interR workloadR)).
    Definition tgt_t2_le_arrival_plus_R_1 (tsk : Task) : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_AbstractRta_t2_le_arrival_plus_R_1
        Task dT tcL Job dJ jaL costL PStateL sL tsk interL workloadL)).

    Theorem t2_le_arrival_plus_R_1_correspondence (tsk : Task) :
      PropSPropRel (src_t2_le_arrival_plus_R_1 tsk) (tgt_t2_le_arrival_plus_R_1 tsk).
    Proof.
      unfold src_t2_le_arrival_plus_R_1, tgt_t2_le_arrival_plus_R_1.
      apply arta_forall_fun. intros NPR NPL HNP.
      apply ad_imp_correspondence.
      { apply ad_forall_nat_correspondence. intros FR FL HF.
        apply ad_forall_nat_correspondence. intros dR dL Hd.
        exact (LE _ _ _ _ HF (ADD _ _ _ _ (Htc tsk) (HNP _ _ _ _ HF Hd))). }
      apply ad_forall_nat_correspondence. intros RR RL HR.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BIm j _ _ _ _ H1 H2)|].
      apply ad_forall_nat_correspondence. intros AR AL HA.
      apply ad_imp_correspondence; [exact (LE _ _ _ _ HA (SUB _ _ _ _ (Hja j) H1))|].
      apply ad_forall_nat_correspondence. intros FR FL HF.
      have HAR := ADD _ _ _ _ HA HR.
      apply ad_imp_correspondence;
        [exact (LE _ _ _ _ (ADD _ _ _ _ (Htc tsk) (HNP _ _ _ _ HF HAR)) HAR)|].
      apply ad_imp_correspondence; [exact (LE _ _ _ _ H2 (ADD _ _ _ _ H1 HF))|].
      exact (LE _ _ _ _ H2 (ADD _ _ _ _ (Hja j) HR)).
    Qed.

    Definition src_job_completed_by_arrival_plus_R_1 (tsk : Task) : Prop :=
      ltac:(body_of (fun s : S.statement_job_completed_by_arrival_plus_R_1 =>
        s Task tcR Job jaR costR PStateR sR tsk interR workloadR)).
    Definition tgt_job_completed_by_arrival_plus_R_1 (tsk : Task) : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_AbstractRta_job_completed_by_arrival_plus_R_1
        Task dT tcL Job dJ jaL costL PStateL sL tsk interL workloadL)).

    Theorem job_completed_by_arrival_plus_R_1_correspondence (tsk : Task) :
      PropSPropRel (src_job_completed_by_arrival_plus_R_1 tsk) (tgt_job_completed_by_arrival_plus_R_1 tsk).
    Proof.
      unfold src_job_completed_by_arrival_plus_R_1, tgt_job_completed_by_arrival_plus_R_1.
      apply arta_forall_fun. intros NPR NPL HNP.
      apply ad_imp_correspondence.
      { apply ad_forall_nat_correspondence. intros FR FL HF.
        apply ad_forall_nat_correspondence. intros dR dL Hd.
        exact (LE _ _ _ _ HF (ADD _ _ _ _ (Htc tsk) (HNP _ _ _ _ HF Hd))). }
      apply ad_forall_nat_correspondence. intros RR RL HR.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BIm j _ _ _ _ H1 H2)|].
      apply ad_forall_nat_correspondence. intros AR AL HA.
      apply ad_imp_correspondence; [exact (LE _ _ _ _ HA (SUB _ _ _ _ (Hja j) H1))|].
      apply ad_forall_nat_correspondence. intros FR FL HF.
      have HAR := ADD _ _ _ _ HA HR.
      apply ad_imp_correspondence;
        [exact (LE _ _ _ _ (ADD _ _ _ _ (Htc tsk) (HNP _ _ _ _ HF HAR)) HAR)|].
      apply ad_imp_correspondence; [exact (LE _ _ _ _ H2 (ADD _ _ _ _ H1 HF))|].
      exact (ad_bool_truth_correspondence _ _
        (ad_completed_by_related Job PStateR PStateL R sR sL Hs costR costL Hcost j _ _
          (ADD _ _ _ _ (Hja j) HR))).
    Qed.

    (** *** t2_le_arrival_plus_R_2 and job_completed_by_arrival_plus_R_2 *)

    Definition src_t2_le_arrival_plus_R_2 : Prop :=
      ltac:(body_of (fun s : S.statement_t2_le_arrival_plus_R_2 =>
        s Job jaR costR PStateR sR interR workloadR)).
    Definition tgt_t2_le_arrival_plus_R_2 : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_AbstractRta_t2_le_arrival_plus_R_2
        Job dJ jaL costL PStateL sL interL workloadL)).

    Theorem t2_le_arrival_plus_R_2_correspondence :
      PropSPropRel src_t2_le_arrival_plus_R_2 tgt_t2_le_arrival_plus_R_2.
    Proof.
      unfold src_t2_le_arrival_plus_R_2, tgt_t2_le_arrival_plus_R_2.
      apply ad_forall_nat_correspondence. intros RR RL HR.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BIm j _ _ _ _ H1 H2)|].
      apply ad_forall_nat_correspondence. intros AR AL HA.
      apply ad_imp_correspondence; [exact (LE _ _ _ _ HA (SUB _ _ _ _ (Hja j) H1))|].
      apply ad_imp_correspondence; [exact (LE _ _ _ _ H2 (ADD _ _ _ _ H1 (ADD _ _ _ _ HA HR)))|].
      exact (LE _ _ _ _ H2 (ADD _ _ _ _ (Hja j) HR)).
    Qed.

    Definition src_job_completed_by_arrival_plus_R_2 : Prop :=
      ltac:(body_of (fun s : S.statement_job_completed_by_arrival_plus_R_2 =>
        s Job jaR costR PStateR sR interR workloadR)).
    Definition tgt_job_completed_by_arrival_plus_R_2 : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_AbstractRta_job_completed_by_arrival_plus_R_2
        Job dJ jaL costL PStateL sL interL workloadL)).

    Theorem job_completed_by_arrival_plus_R_2_correspondence :
      PropSPropRel src_job_completed_by_arrival_plus_R_2 tgt_job_completed_by_arrival_plus_R_2.
    Proof.
      unfold src_job_completed_by_arrival_plus_R_2, tgt_job_completed_by_arrival_plus_R_2.
      apply ad_forall_nat_correspondence. intros RR RL HR.
      apply ad_forall_identity_correspondence. intro j.
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BIm j _ _ _ _ H1 H2)|].
      apply ad_forall_nat_correspondence. intros AR AL HA.
      apply ad_imp_correspondence; [exact (LE _ _ _ _ HA (SUB _ _ _ _ (Hja j) H1))|].
      apply ad_imp_correspondence; [exact (LE _ _ _ _ H2 (ADD _ _ _ _ H1 (ADD _ _ _ _ HA HR)))|].
      exact (ad_bool_truth_correspondence _ _
        (ad_completed_by_related Job PStateR PStateL R sR sL Hs costR costL Hcost j _ _
          (ADD _ _ _ _ (Hja j) HR))).
    Qed.

    (** *** relative_rtc_time_is_bounded *)

    Definition src_relative_rtc_time_is_bounded (tsk : Task) : Prop :=
      ltac:(body_of (fun s : S.statement_relative_rtc_time_is_bounded =>
        s Task Job jtR jaR costR PStateR arrR sR tsk interR workloadR)).
    Definition tgt_relative_rtc_time_is_bounded (tsk : Task) : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Abstract_AbstractRta_relative_rtc_time_is_bounded
        Task dT Job dJ jtL jaL costL PStateL arrL sL tsk interL workloadL)).

    Theorem relative_rtc_time_is_bounded_correspondence (tsk : Task) :
      PropSPropRel (src_relative_rtc_time_is_bounded tsk) (tgt_relative_rtc_time_is_bounded tsk).
    Proof.
      unfold src_relative_rtc_time_is_bounded, tgt_relative_rtc_time_is_bounded.
      apply ad_forall_nat_correspondence. intros LR LL HL.
      apply ad_imp_correspondence;
        [exact (arta_bounded_rel interR interL Hinter workloadR workloadL Hworkload tsk LR LL HL)|].
      apply ad_forall_identity_correspondence. intro j.
      apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j arta_arr_ad)|].
      apply ad_imp_correspondence;
        [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|].
      apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (arta_cost_positive_related j))|].
      apply ad_forall_nat_correspondence. intros t1R t1L H1.
      apply ad_forall_nat_correspondence. intros t2R t2L H2.
      apply ad_imp_correspondence; [exact (BIm j _ _ _ _ H1 H2)|].
      apply ad_forall_nat_correspondence. intros FR FL HF.
      apply ad_imp_correspondence; [exact (LT _ _ _ _ (ADD _ _ _ _ H1 HF) H2)|].
      exact (LT _ _ _ _ HF HL).
    Qed.
  End LeadingModel.

  (** *** The fixpoint-inside-the-busy-interval lemmas and the main theorem:
      [Interference] / [InterferingWorkload], task sets and interference-bound
      functions are quantified inside the statements and covered. *)

    (** The common tail of [job_receives_enough_service_1/2/3] and
        [job_is_completed_by_arrival_plus_R], from the job onwards; it leaves
        the conclusion, with the job, [t1], [A_sp], [F] and their relations
        ([H1], [HA], [HF], [HR]) in context. *)
    Ltac arta_tail interR interL Hinter workloadR workloadL Hworkload tsk HL HP HNP HR :=
      apply ad_forall_identity_correspondence;
      let j := fresh "j" in intro j;
      (apply ad_imp_correspondence; [exact (ad_arrives_in_related Job arrR arrL j arta_arr_ad)|]);
      (apply ad_imp_correspondence;
        [exact (ad_bool_truth_correspondence _ _ (ad_job_of_task_related Job Task jtR jtL tsk j Hjt))|]);
      (apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (arta_cost_positive_related j))|]);
      apply ad_forall_nat_correspondence;
      let t1R := fresh "t1R" in let t1L := fresh "t1L" in let H1 := fresh "H1" in
      intros t1R t1L H1;
      apply ad_forall_nat_correspondence;
      let t2R := fresh "t2R" in let t2L := fresh "t2L" in let H2 := fresh "H2" in
      intros t2R t2L H2;
      (apply ad_imp_correspondence;
        [exact (BI interR interL Hinter workloadR workloadL Hworkload j _ _ _ _ H1 H2)|]);
      apply ad_forall_nat_correspondence;
      let AR := fresh "AR" in let AL := fresh "AL" in let HA := fresh "HA" in
      intros AR AL HA;
      let Hrel := fresh "Hrel" in
      have Hrel := SUB _ _ _ _ (Hja j) H1;
      (apply ad_imp_correspondence; [exact (LE _ _ _ _ HA Hrel)|]);
      (apply ad_imp_correspondence;
        [exact (arta_equivalent_rel _ _ _ _ _ _ (fun xR xL Hx => HP _ _ _ _ Hrel Hx)
          (fun xR xL Hx => HP _ _ _ _ HA Hx) HL)|]);
      apply ad_forall_nat_correspondence;
      let FR := fresh "FR" in let FL := fresh "FL" in let HF := fresh "HF" in
      intros FR FL HF;
      let HAR := fresh "HAR" in
      have HAR := ADD _ _ _ _ HA HR;
      (apply ad_imp_correspondence; [exact (LE _ _ _ _ (ADD _ _ _ _ (Hrtc tsk) (HP _ _ _ _ HA HF)) HF)|]);
      (apply ad_imp_correspondence;
        [exact (LE _ _ _ _ (ADD _ _ _ _ (Htc tsk) (HNP _ _ _ _ HF HAR)) HAR)|]);
      (apply ad_imp_correspondence; [exact (LT _ _ _ _ (ADD _ _ _ _ H1 HF) H2)|]);
      (apply ad_imp_correspondence; [exact (LT _ _ _ _ (ADD _ _ _ _ H1 HAR) H2)|]).

    (** Prefix up to the first interference-bound function, for a fixed
        task set, task and abstract model. *)
    Ltac arta_prefix interR interL Hinter workloadR workloadL Hworkload tsk :=
      apply ad_imp_correspondence;
        [exact (arta_wc_rel interR interL Hinter workloadR workloadL Hworkload)|];
      apply ad_forall_nat_correspondence;
      let LR := fresh "LR" in let LL := fresh "LL" in let HL := fresh "HL" in
      intros LR LL HL;
      (apply ad_imp_correspondence;
        [exact (arta_bounded_rel interR interL Hinter workloadR workloadL Hworkload tsk LR LL HL)|]);
      apply arta_forall_fun;
      let PR := fresh "PR" in let PL := fresh "PL" in let HP := fresh "HP" in
      intros PR PL HP;
      (apply ad_imp_correspondence;
        [exact (arta_ibfp_bounded_rel interR interL Hinter workloadR workloadL Hworkload tsk PR PL HP)|]).

    Lemma arta_ge_param_rel (tsk : Task) NPR NPL (HNP : ArtaFunRel NPR NPL) :
      PropSPropRel (forall F D : nat, is_true (leq F (addn (@prosa.model.task.concept.task_cost Task tcR tsk) (NPR F D))))
        (forall F D : Lean.Nat, sub_imported_le F
          (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
            (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk) (NPL F D))).
    Proof.
      apply ad_forall_nat_correspondence. intros FR FL HF.
      apply ad_forall_nat_correspondence. intros dR dL Hd.
      exact (LE _ _ _ _ HF (ADD _ _ _ _ (Htc tsk) (HNP _ _ _ _ HF Hd))).
    Qed.


  (** *** job_receives_enough_service_1 / _2 *)

  Definition src_job_receives_enough_service_1 : Prop :=
    ltac:(body_of (fun s : S.statement_job_receives_enough_service_1 =>
      s Task tcR rtcR Job jtR jaR costR PStateR arrR sR)).
  Definition tgt_job_receives_enough_service_1 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_AbstractRta_job_receives_enough_service_1
      Task dT tcL rtcL Job dJ jtL jaL costL PStateL arrL sL)).

  Theorem job_receives_enough_service_1_correspondence :
    PropSPropRel src_job_receives_enough_service_1 tgt_job_receives_enough_service_1.
  Proof.
    unfold src_job_receives_enough_service_1, tgt_job_receives_enough_service_1.
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    apply arta_forall_inter. intros interR interL Hinter.
    apply arta_forall_iw. intros workloadR workloadL Hworkload.
    arta_prefix interR interL Hinter workloadR workloadL Hworkload tsk.
    apply arta_forall_fun. intros NPR NPL HNP.
    apply ad_forall_nat_correspondence. intros RR RL HR.
    arta_tail interR interL Hinter workloadR workloadL Hworkload tsk HL HP HNP HR.
    apply ad_imp_correspondence; [exact (LE _ _ _ _ (Hcost j) (Hrtc tsk))|].
    exact (LE _ _ _ _ (Hcost j) (ad_service_related Job PStateR PStateL R sR sL Hs j _ _ (ADD _ _ _ _ H1 HF))).
  Qed.

  Definition src_job_receives_enough_service_2 : Prop :=
    ltac:(body_of (fun s : S.statement_job_receives_enough_service_2 =>
      s Task tcR rtcR Job jtR jaR costR PStateR arrR sR)).
  Definition tgt_job_receives_enough_service_2 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_AbstractRta_job_receives_enough_service_2
      Task dT tcL rtcL Job dJ jtL jaL costL PStateL arrL sL)).

  Theorem job_receives_enough_service_2_correspondence :
    PropSPropRel src_job_receives_enough_service_2 tgt_job_receives_enough_service_2.
  Proof.
    unfold src_job_receives_enough_service_2, tgt_job_receives_enough_service_2.
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    apply arta_forall_inter. intros interR interL Hinter.
    apply arta_forall_iw. intros workloadR workloadL Hworkload.
    arta_prefix interR interL Hinter workloadR workloadL Hworkload tsk.
    apply arta_forall_fun. intros NPR NPL HNP.
    apply ad_forall_nat_correspondence. intros RR RL HR.
    arta_tail interR interL Hinter workloadR workloadL Hworkload tsk HL HP HNP HR.
    apply ad_imp_correspondence; [exact (LE _ _ _ _ (Hrtc tsk) (Hcost j))|].
    exact (LE _ _ _ _ (Hrtc tsk) (ad_service_related Job PStateR PStateL R sR sL Hs j _ _ (ADD _ _ _ _ H1 HF))).
  Qed.

  (** *** job_receives_enough_service_3 and job_is_completed_by_arrival_plus_R *)

  Definition src_job_receives_enough_service_3 : Prop :=
    ltac:(body_of (fun s : S.statement_job_receives_enough_service_3 =>
      s Task tcR rtcR Job jtR jaR costR PStateR arrR sR)).
  Definition tgt_job_receives_enough_service_3 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_AbstractRta_job_receives_enough_service_3
      Task dT tcL rtcL Job dJ jtL jaL costL PStateL arrL sL)).

  Theorem job_receives_enough_service_3_correspondence :
    PropSPropRel src_job_receives_enough_service_3 tgt_job_receives_enough_service_3.
  Proof.
    unfold src_job_receives_enough_service_3, tgt_job_receives_enough_service_3.
    apply ad_imp_correspondence; [exact arta_valid_job_costs_rel|].
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    apply arta_forall_inter. intros interR interL Hinter.
    apply arta_forall_iw. intros workloadR workloadL Hworkload.
    arta_prefix interR interL Hinter workloadR workloadL Hworkload tsk.
    apply arta_forall_fun. intros NPR NPL HNP.
    apply ad_imp_correspondence;
      [exact (arta_ibfnp_bounded_rel interR interL Hinter workloadR workloadL Hworkload tsk PR PL HP NPR NPL HNP)|].
    apply ad_forall_nat_correspondence. intros RR RL HR.
    arta_tail interR interL Hinter workloadR workloadL Hworkload tsk HL HP HNP HR.
    apply ad_imp_correspondence; [exact (LE _ _ _ _ (Hrtc tsk) (Hcost j))|].
    exact (LE _ _ _ _ (Hcost j)
      (ad_service_related Job PStateR PStateL R sR sL Hs j _ _ (ADD _ _ _ _ H1 (ADD _ _ _ _ HA HR)))).
  Qed.

  Definition src_job_is_completed_by_arrival_plus_R : Prop :=
    ltac:(body_of (fun s : S.statement_job_is_completed_by_arrival_plus_R =>
      s Task tcR rtcR Job jtR jaR costR PStateR arrR sR)).
  Definition tgt_job_is_completed_by_arrival_plus_R : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_AbstractRta_job_is_completed_by_arrival_plus_R
      Task dT tcL rtcL Job dJ jtL jaL costL PStateL arrL sL)).

  Theorem job_is_completed_by_arrival_plus_R_correspondence :
    PropSPropRel src_job_is_completed_by_arrival_plus_R tgt_job_is_completed_by_arrival_plus_R.
  Proof.
    unfold src_job_is_completed_by_arrival_plus_R, tgt_job_is_completed_by_arrival_plus_R.
    apply ad_imp_correspondence; [exact arta_valid_job_costs_rel|].
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    apply arta_forall_inter. intros interR interL Hinter.
    apply arta_forall_iw. intros workloadR workloadL Hworkload.
    arta_prefix interR interL Hinter workloadR workloadL Hworkload tsk.
    apply arta_forall_fun. intros NPR NPL HNP.
    apply ad_imp_correspondence;
      [exact (arta_ibfnp_bounded_rel interR interL Hinter workloadR workloadL Hworkload tsk PR PL HP NPR NPL HNP)|].
    apply ad_imp_correspondence; [exact (arta_ge_param_rel tsk NPR NPL HNP)|].
    apply ad_forall_nat_correspondence. intros RR RL HR.
    arta_tail interR interL Hinter workloadR workloadL Hworkload tsk HL HP HNP HR.
    exact (ad_bool_truth_correspondence _ _
      (ad_completed_by_related Job PStateR PStateL R sR sL Hs costR costL Hcost j _ _
        (ADD _ _ _ _ (Hja j) HR))).
  Qed.

  (** *** uniprocessor_response_time_bound *)

  Definition src_uniprocessor_response_time_bound : Prop :=
    ltac:(body_of (fun s : S.statement_uniprocessor_response_time_bound =>
      s Task tcR rtcR Job jtR jaR costR PStateR arrR sR)).
  Definition tgt_uniprocessor_response_time_bound : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Abstract_AbstractRta_uniprocessor_response_time_bound
      Task dT tcL rtcL Job dJ jtL jaL costL PStateL arrL sL)).

  Theorem uniprocessor_response_time_bound_correspondence :
    PropSPropRel src_uniprocessor_response_time_bound tgt_uniprocessor_response_time_bound.
  Proof.
    unfold src_uniprocessor_response_time_bound, tgt_uniprocessor_response_time_bound.
    apply ad_imp_correspondence; [exact arta_valid_job_costs_rel|].
    apply arta_forall_list. intros tsR tsL Hts.
    apply ad_forall_identity_correspondence. intro tsk.
    apply ad_imp_correspondence; [exact (ad_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    apply arta_forall_inter. intros interR interL Hinter.
    apply arta_forall_iw. intros workloadR workloadL Hworkload.
    arta_prefix interR interL Hinter workloadR workloadL Hworkload tsk.
    apply arta_forall_fun. intros NPR NPL HNP.
    apply ad_imp_correspondence;
      [exact (arta_ibfnp_bounded_rel interR interL Hinter workloadR workloadL Hworkload tsk PR PL HP NPR NPL HNP)|].
    apply ad_imp_correspondence; [exact (arta_ge_param_rel tsk NPR NPL HNP)|].
    apply ad_forall_nat_correspondence. intros RR RL HR.
    apply ad_imp_correspondence.
    - apply ad_forall_nat_correspondence. intros AR AL HA.
      apply ad_imp_correspondence; [exact (arta_search_space_rel _ _ _ _ _ _ HP HL HA)|].
      apply ad_exists_nat_correspondence. intros FR FL HF.
      have HAR := ADD _ _ _ _ HA HR.
      apply ad_and_correspondence.
      + exact (LE _ _ _ _ (ADD _ _ _ _ (Hrtc tsk) (HP _ _ _ _ HA HF)) HF).
      + exact (LE _ _ _ _ (ADD _ _ _ _ (Htc tsk) (HNP _ _ _ _ HF HAR)) HAR).
    - exact (arta_response_time_bound_rel tsk RR RL HR).
  Qed.
End AbstractRta.
