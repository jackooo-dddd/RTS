(* Helper-only copy of the accepted certificates/analysis_abstract_restricted_supply_search_space_elf/SearchSpaceElfCorrespondence.v (re-bound to this export),
   without its statement correspondence search_space_sub_correspondence (whose target statement is not
   part of this export); every other helper definition and lemma is unchanged. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop order.
From mathcomp Require Import ssralg ssrnum ssrint.
From prosa Require Import SearchSpaceElfSemanticSource.
From prosa Require Import util.int model.priority.gel model.priority.elf.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaRsElfFullyNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  WorkloadCorrespondence CurvesCorrespondence RequestBoundFunctionCorrespondence
  WorkloadBoundedCorrespondence EdfAthepBoundCorrespondence
  NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityGelHelpers PriorityElfHelpers ElfAthepBoundCorrespondence
  TaskPreemptionParametersCorrespondence BlockingBoundElfCorrespondence.

Module I := ImportedRtaRsElfFullyNonpreemptive.
Module S := SearchSpaceElfSemanticSource.SearchSpaceElfSemanticSource.

Import GRing.Theory Num.Theory Order.TTheory.

(** Correspondences for [analysis/abstract/restricted_supply/search_space/elf.v].

    Source side: the extracted definition block (with its section-local
    Lets) and the extracted statement [S.statement_search_space_sub]
    specialised at its leading inputs (task type, [task_cost],
    [task_max_nonpreemptive_segment], priority points, the task set and
    [max_arrivals]); target side: the compiled Lean definition and the
    imported Lean theorem type at related inputs ([SubNatRel] on
    [task_cost], the accepted [TppMaxSegmentRel], the accepted
    [GelPriorityPointRel], [ArListRel], the accepted [CvMaxArrivalsRel]);
    the FP policy pointwise on Booleans ([PdFPRel]) and covered in both
    directions in the statement (the accepted [pco_forall_fp]).  Tasks are
    identity carriers and Nats are covered in both directions.  The
    definition is related as Booleans: [has] through kernel-checked Lean
    [List.any] equations exported with the artifact (as in the accepted EDF
    search space), [!=] on Nat through the Lean [decide (¬ P) = !decide P]
    observation, [!=] on [int] through the order ([eq_le] on the source
    side, a kernel-checked Lean equation on the target side) and the
    accepted GEL order relation.  The abstract search-space predicate
    (pinned source) is related by unfolding both sides, as for the accepted
    EDF search space.  RBFs, the ELF blocking bound, the ELF interval length
    and the ELF athep bound are closed by the accepted certificates
    re-instantiated at this artifact.  No source or target theorem is
    used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Notation P_any_nil := I.Prosa_Validation_SearchSpaceElfInterface_production_any_nil.
Notation P_any_cons := I.Prosa_Validation_SearchSpaceElfInterface_production_any_cons.
Notation P_int_ne := I.Prosa_Validation_SearchSpaceElfInterface_production_int_decide_ne.

Lemma ssel_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma ssel_nat_neq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (aR <> bR) (I.Ne Lean.Nat aL bL).
Proof.
  intros Ha Hb. unfold I.Ne, I.Not.
  apply ar_imp_correspondence.
  - exact (sub_nat_eq_correspondence aR aL bR bL Ha Hb).
  - exact ssel_false_correspondence.
Qed.

Lemma ssel_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p|q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intro H. destruct H as [p|q].
    + exact (strictly_inhabits (or_introl _ (sprop_to_prop _ _ HP p))).
    + exact (strictly_inhabits (or_intror _ (sprop_to_prop _ _ HQ q))).
Qed.

Lemma ssel_and3_correspondence (b1 b2 : bool) (P : Prop) (Q1 Q2 PL : SProp) :
  PropSPropRel (is_true b1) Q1 -> PropSPropRel (is_true b2) Q2 -> PropSPropRel P PL ->
  PropSPropRel (is_true (b1 && b2) /\ P) (Lean.And Q1 (Lean.And Q2 PL)).
Proof.
  intros H1 H2 HP.
  have R := ar_and_correspondence _ _ _ _ H1 (ar_and_correspondence _ _ _ _ H2 HP).
  apply prop_sprop_rel_intro.
  - intros [Hb Hp]. apply (prop_to_sprop _ _ R).
    move/andP: Hb => [h1 h2]. by split; [|split].
  - intro HL. apply strictly_inhabits.
    move: (sprop_to_prop _ _ R HL) => [h1 [h2 hp]].
    split; [apply/andP; split|]; assumption.
Qed.

Lemma ssel_decide_not (P : SProp) (d : I.Decidable P) :
  Lean.eq (I.Decidable_decide (I.Not P) (I.instDecidableNot P d))
    (I.Bool_not (I.Decidable_decide P d)).
Proof. destruct d; exact (@Lean.eq_refl _ _). Qed.

Lemma ssel_nat_neqb_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SvcBoolRel (aR != bR)
    (I.Decidable_decide (I.Ne Lean.Nat aL bL)
      (I.instDecidableNot (Lean.eq aL bL) (I.instDecidableEqNat aL bL))).
Proof.
  intros Ha Hb. unfold SvcBoolRel.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (ssel_decide_not _ _))).
  exact (svc_bool_not_related _ _ (svc_decide_eq_related _ _ _ _ Ha Hb)).
Qed.

(** ** Integer disequality through the order *)

Definition ssel_target_int_ne (a b : I.Int) : I.Bool :=
  ltac:(let T := type of (P_int_ne a b) in match T with @Lean.eq _ ?L _ => exact L end).

Lemma ssel_int_neq_le (x y : int) : (x != y) = ~~ ((x <= y)%R && (y <= x)%R).
Proof. by rewrite eq_le. Qed.

Lemma ssel_int_neq_related xR xL yR yL :
  GelIntRel xR xL -> GelIntRel yR yL -> ArBoolRel (xR != yR) (ssel_target_int_ne xL yL).
Proof.
  intros Hx Hy. rewrite ssel_int_neq_le. unfold ArBoolRel, ssel_target_int_ne.
  exact (sub_imported_eq_trans _ _ _
    (pd_bool_not_related _ _ (pd_bool_and_related _ _ _ _ (gel_le_related _ _ _ _ Hx Hy)
      (gel_le_related _ _ _ _ Hy Hx)))
    (sub_imported_eq_sym _ _ (P_int_ne xL yL))).
Qed.

(** ** [has] against [List.any] *)

Section Any.
  Context (X : Type).
  Variable PR : X -> bool.
  Variable PL : X -> I.Bool.
  Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).

  Lemma ssel_has_canonical (xs : seq X) :
    ArBoolRel (has PR xs) (I.List_any X (ar_list_to_imported xs) PL).
  Proof.
    induction xs as [|x xs IH].
    - exact (sub_imported_eq_sym _ _ (P_any_nil X PL)).
    - cbn [has ar_list_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (P_any_cons X PL x (ar_list_to_imported xs)))).
      exact (pp_bool_or_related _ _ _ _ (HP x) IH).
  Qed.

  Lemma ssel_has_related (xsR : seq X) (xsL : I.List X) :
    ArListRel xsR xsL -> ArBoolRel (has PR xsR) (I.List_any X xsL PL).
  Proof.
    intro Hxs.
    exact (sub_imported_eq_trans _ _ _ (ssel_has_canonical xsR)
      (sub_imported_eq_congr (fun l => I.List_any X l PL) _ _ Hxs)).
  Qed.
End Any.

Section SearchSpace.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable mR : TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.TaskMaxNonpreemptiveSegment Task.
  Variable mL : I.Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task dT.
  Hypothesis Hm : TppMaxSegmentRel Task mR mL.
  Variable ppR : prosa.model.priority.gel.PriorityPoint Task.
  Variable ppL : I.Prosa_Model_Priority_Gel_PriorityPoint Task dT.
  Hypothesis Hpp : GelPriorityPointRel Task ppR ppL.
  Variable tsR : seq Task.
  Variable tsL : I.List Task.
  Hypothesis Hts : ArListRel tsR tsL.
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : CvMaxArrivalsRel Task maR maL.

  Let RBF tsk := task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk.
  Let BB fR fL Hf tsk := blocking_bound_correspondence Task tcR tcL Htc mR mL Hm ppR ppL Hpp
    tsR tsL Hts maR maL Hma fR fL Hf tsk.
  Let LEN tsk tsk_o := ep_task_interfering_interval_length_correspondence Task ppR ppL Hpp tsk tsk_o.
  Let ONE := sub_nat_rel_canonical (S O).

  Lemma ssel_ep_task_related fR fL (Hf : PdFPRel Task fR fL) (x y : Task) :
    ArBoolRel (@prosa.model.priority.definitions.ep_task Task fR x y)
      (I.Prosa_Model_Priority_Definitions_ep_task Task dT fL x y).
  Proof.
    unfold prosa.model.priority.definitions.ep_task. cbn [I.Prosa_Model_Priority_Definitions_ep_task].
    exact (pd_bool_and_related _ _ _ _ (Hf x y) (Hf y x)).
  Qed.

  (** *** The ELF search-space definition *)

  Theorem is_in_search_space_correspondence fR fL (Hf : PdFPRel Task fR fL)
      (tsk : Task) (LR AR : nat) (LL AL : Lean.Nat) :
    SubNatRel LR LL -> SubNatRel AR AL ->
    SvcBoolRel (@S.is_in_search_space Task tcR mR ppR tsR maR fR tsk LR AR)
      (I.Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Elf_is_in_search_space
        Task dT tcL mL ppL tsL maL fL tsk LL AL).
  Proof.
    intros HL HA. unfold S.is_in_search_space. cbv zeta.
    cbn [I.Prosa_Analysis_Abstract_RestrictedSupply_SearchSpace_Elf_is_in_search_space].
    have HA1 := svc_target_sub_related _ _ _ _ HA ONE.
    refine (ar_bool_and_related _ _ _ _ (svc_decide_lt_related _ _ _ _ HA HL) _).
    refine (pp_bool_or_related _ _ _ _ (pp_bool_or_related _ _ _ _ _ _) _).
    - exact (ssel_nat_neqb_related _ _ _ _ (BB fR fL Hf tsk _ _ HA1) (BB fR fL Hf tsk _ _ HA)).
    - exact (ssel_nat_neqb_related _ _ _ _ (RBF tsk _ _ HA)
        (RBF tsk _ _ (svc_target_add_related _ _ _ _ HA ONE))).
    - apply ssel_has_related; [|exact Hts]. intro tsko.
      exact (ar_bool_and_related _ _ _ _
        (ar_bool_and_related _ _ _ _ (ssel_ep_task_related fR fL Hf tsk tsko) (rbf_neq_related Task tsko tsk))
        (ssel_int_neq_related _ _ _ _ (LEN tsk tsko _ _ HA1) (LEN tsk tsko _ _ HA))).
  Qed.

  (** *** The statement *)

  Let IBF fR fL Hf tsk aR aL (Ha : SubNatRel aR aL) xR xL (Hx : SubNatRel xR xL) :=
    svc_target_add_related _ _ _ _
      (svc_target_sub_related _ _ _ _
        (RBF tsk _ _ (svc_target_add_related _ _ _ _ Ha ONE)) (Htc tsk))
      (svc_target_add_related _ _ _ _ (BB fR fL Hf tsk _ _ Ha)
        (bound_on_athep_workload_correspondence Task tcR tcL Htc maR maL Hma ppR ppL Hpp tsR tsL Hts
          fR fL Hf tsk aR xR aL xL Ha Hx)).
End SearchSpace.
