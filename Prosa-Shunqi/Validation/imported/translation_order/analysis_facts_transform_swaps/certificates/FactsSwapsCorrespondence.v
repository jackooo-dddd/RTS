From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsSwapsSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsSwaps ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedFactsSwaps.
Module S := FactsSwapsSemanticSource.FactsSwapsSemanticSource.

(** Statement correspondences for [analysis/facts/transform/swaps.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (job type, [job_cost], [job_deadline], processor
    state, schedule); target side: the imported Lean theorem types at
    related inputs ([SvcJobCostRel], [SubNatRel] on [job_deadline], the
    accepted two-sided [SvcProcessorStateRel] with the schedules related
    through the state conversion, as in the accepted replace-at
    certificate).  Instants and jobs quantified inside the statements are
    covered in both directions (Nats) or are identity carriers (jobs);
    arrival sequences through the list conversion, processor states through
    the accepted state conversion.  [replace_at] (hence [swapped]) is related
    by replaying the accepted replace-at proof with this artifact's
    kernel-checked [replace_at] equations; service, scheduling and completion
    use the accepted primitive relations.  No source or target theorem is
    used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma swp_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Lemma swp_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma swp_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma swp_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma swp_nat_neq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (aR <> bR) (I.Ne Lean.Nat aL bL).
Proof.
  intros Ha Hb. unfold I.Ne, I.Not.
  apply ar_imp_correspondence.
  - exact (sub_nat_eq_correspondence aR aL bR bL Ha Hb).
  - exact swp_false_correspondence.
Qed.

Lemma swp_or_correspondence (P Q : Prop) (PL QL : SProp) :
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

Lemma swp_bool_eq_correspondence (bR cR : bool) (bL cL : I.Bool) :
  SvcBoolRel bR bL -> SvcBoolRel cR cL -> PropSPropRel (bR = cR) (Lean.eq bL cL).
Proof.
  intros Hb Hc. apply prop_sprop_rel_intro.
  - intro E. destruct E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hb) Hc).
  - intro E. apply strictly_inhabits.
    have EL := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hb (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hc))).
    destruct bR, cR; cbn in EL; solve [reflexivity | discriminate EL].
Qed.

Lemma swp_exists_identity (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma swp_decide_not (P : SProp) (d : I.Decidable P) :
  Lean.eq (I.Decidable_decide (I.Not P) (I.instDecidableNot P d))
    (I.Bool_not (I.Decidable_decide P d)).
Proof. destruct d; exact (@Lean.eq_refl _ _). Qed.

Lemma swp_nat_neqb_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SvcBoolRel (aR != bR)
    (I.Decidable_decide (I.Ne Lean.Nat aL bL)
      (I.instDecidableNot (Lean.eq aL bL) (I.instDecidableEqNat aL bL))).
Proof.
  intros Ha Hb. unfold SvcBoolRel.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (swp_decide_not _ _))).
  exact (svc_bool_not_related _ _ (svc_decide_eq_related _ _ _ _ Ha Hb)).
Qed.

Section Swaps.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let StateR := @prosa.behavior.schedule.State Job PStateR.
  Let StateL := I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PStateL.
  Let toL := svc_ps_state_to_target Job PStateR PStateL R.

  (** Schedules related through the processor-state conversion (replayed
      from the accepted replace-at certificate). *)
  Definition SwpScheduleFunRel (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) : SProp :=
    forall tR tL, SubNatRel tR tL -> Lean.eq (toL (schedR tR)) (schedL tL).

  Lemma swp_state_rel (sR : StateR) (sL : StateL) :
    Lean.eq (toL sR) sL -> svc_ps_state_rel Job PStateR PStateL R sR sL.
  Proof.
    intro H.
    exact (swp_lean_transport (fun x => svc_ps_state_rel Job PStateR PStateL R sR x)
      _ _ H (svc_ps_state_rel_canonical Job PStateR PStateL R sR)).
  Qed.

  Lemma swp_state_eq_correspondence (sR sR' : StateR) (sL sL' : StateL) :
    Lean.eq (toL sR) sL -> Lean.eq (toL sR') sL' ->
    PropSPropRel (sR = sR') (Lean.eq sL sL').
  Proof.
    intros H H'. apply prop_sprop_rel_intro.
    - intro E.
      exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ H)
        (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (f_equal toL E)) H')).
    - intro EL. apply strictly_inhabits.
      have ET := imported_eq_to_coq_eq _ _
        (sub_imported_eq_trans _ _ _ H
          (sub_imported_eq_trans _ _ _ EL (sub_imported_eq_sym _ _ H'))).
      have ES := f_equal (svc_ps_state_to_source Job PStateR PStateL R) ET.
      rewrite !(svc_ps_state_source_roundtrip Job PStateR PStateL R) in ES.
      exact ES.
  Qed.

  Section Replace.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SwpScheduleFunRel schedR schedL.
    Variable t'R : nat.
    Variable t'L : Lean.Nat.
    Hypothesis Ht' : SubNatRel t'R t'L.
    Variable nsR : StateR.
    Variable nsL : StateL.
    Hypothesis Hns : Lean.eq (toL nsR) nsL.

    Let replR := @prosa.analysis.transform.swap.replace_at Job PStateR schedR t'R nsR.
    Let replL := I.Prosa_Analysis_Transform_Swap_replace_at Job dJ PStateL schedL t'L nsL.

    Lemma swp_nat_not_eq (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL -> t'R <> tR -> I.Not (Lean.eq tL t'L).
    Proof.
      intros Ht NE. unfold I.Not. intro EL.
      refine (match NE _ return I.False with end).
      rewrite -(swp_nat_input _ _ Ht) -(swp_nat_input _ _ Ht').
      exact (Logic.eq_sym (f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ EL))).
    Qed.

    Lemma swp_src_same (tR : nat) : t'R = tR -> replR tR = nsR.
    Proof. move=> <-. by rewrite /replR /prosa.analysis.transform.swap.replace_at eqxx. Qed.

    Lemma swp_src_other (tR : nat) : t'R <> tR -> replR tR = schedR tR.
    Proof.
      move=> /eqP NE.
      by rewrite /replR /prosa.analysis.transform.swap.replace_at (negbTE NE).
    Qed.

    Lemma swp_replace_at_fun : SwpScheduleFunRel replR replL.
    Proof.
      intros tR tL Ht.
      destruct (@eqP nat t'R tR) as [E|NE].
      - refine (sub_imported_eq_trans _ _ _
          (coq_eq_to_imported_eq _ _ (f_equal toL (swp_src_same tR E))) _).
        subst tR.
        exact (sub_imported_eq_trans _ _ _ Hns (sub_imported_eq_sym _ _
          (I.Prosa_Validation_ReplaceAtInterface_production_replace_at_same
            Job dJ PStateL schedL t'L nsL tL
            (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Ht) Ht')))).
      - refine (sub_imported_eq_trans _ _ _
          (coq_eq_to_imported_eq _ _ (f_equal toL (swp_src_other tR NE))) _).
        exact (sub_imported_eq_trans _ _ _ (Hsched tR tL Ht) (sub_imported_eq_sym _ _
          (I.Prosa_Validation_ReplaceAtInterface_production_replace_at_other
            Job dJ PStateL schedL t'L nsL tL (swp_nat_not_eq tR tL Ht NE)))).
    Qed.
  End Replace.

  Lemma swp_swapped_fun schedR schedL (Hsched : SwpScheduleFunRel schedR schedL)
      t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
    SwpScheduleFunRel (@prosa.analysis.transform.swap.swapped Job PStateR schedR t1R t2R)
      (I.Prosa_Analysis_Transform_Swap_swapped Job dJ PStateL schedL t1L t2L).
  Proof.
    unfold prosa.analysis.transform.swap.swapped.
    cbn [I.Prosa_Analysis_Transform_Swap_swapped].
    exact (swp_replace_at_fun _ _
      (swp_replace_at_fun schedR schedL Hsched t1R t1L H1 _ _ (Hsched t2R t2L H2))
      t2R t2L H2 _ _ (Hsched t1R t1L H1)).
  Qed.

  Section Observations.
    Variable schR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis H : SwpScheduleFunRel schR schL.

    Lemma swp_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schR j tR)
        (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.scheduled_at.
      cbn [I.Prosa_Behavior_Service_scheduled_at].
      exact (svc_scheduled_in_related Job PStateR PStateL R j _ _ (swp_state_rel _ _ (H tR tL Ht))).
    Qed.

    Lemma swp_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service_at Job PStateR schR j tR)
        (I.Prosa_Behavior_Service_service_at Job dJ PStateL schL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.service_at.
      cbn [I.Prosa_Behavior_Service_service_at].
      exact (svc_service_in_related Job PStateR PStateL R j _ _ (swp_state_rel _ _ (H tR tL Ht))).
    Qed.

    Lemma swp_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service Job PStateR schR j tR)
        (I.Prosa_Behavior_Service_service Job dJ PStateL schL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.service.
      cbn [I.Prosa_Behavior_Service_service].
      have Hsum := svc_interval_sum_related O tR Lean.Nat_zero tL
        (fun t => @prosa.behavior.service.service_at Job PStateR schR j t)
        (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schL j t)
        (sub_nat_rel_canonical O) Ht (fun xR xL Hx => swp_service_at_related j xR xL Hx).
      change (SubNatRel
        (@prosa.behavior.service.service_during Job PStateR schR j O tR)
        (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
          Job dJ PStateL schL j Lean.Nat_zero tL)) in Hsum.
      exact Hsum.
    Qed.

    Section Cost.
      Variable costR : prosa.behavior.job.JobCost Job.
      Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
      Hypothesis Hcost : SvcJobCostRel Job costR costL.

      Lemma swp_completed_jobs_dont_execute_related :
        PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PStateR schR costR)
          (I.Prosa_Behavior_Ready_completed_jobs_dont_execute Job dJ PStateL schL costL).
      Proof.
        unfold prosa.behavior.ready.completed_jobs_dont_execute.
        cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (swp_scheduled_at_related j tR tL Ht))|].
        exact (sub_nat_lt_correspondence _ _ _ _ (swp_service_related j _ _ Ht) (Hcost j)).
      Qed.

      Lemma swp_service_bound_related :
        PropSPropRel (forall (j : Job) (t : nat), is_true (leq (@prosa.behavior.service.service Job PStateR schR j t)
            (@prosa.behavior.job.job_cost Job costR j)))
          (forall (j : Job) (t : Lean.Nat),
            svc_target_le (I.Prosa_Behavior_Service_service Job dJ PStateL schL j t)
              (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j)).
      Proof.
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        exact (sub_nat_le_correspondence _ _ _ _ (swp_service_related j _ _ Ht) (Hcost j)).
      Qed.

      Variable dlR : prosa.behavior.job.JobDeadline Job.
      Variable dlL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
      Hypothesis Hdl : forall j : Job,
        SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
          (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).

      Lemma swp_job_meets_deadline_related (j : Job) :
        SvcBoolRel (@prosa.behavior.service.job_meets_deadline Job PStateR schR costR dlR j)
          (I.Prosa_Behavior_Service_job_meets_deadline Job dJ PStateL schL costL dlL j).
      Proof.
        unfold prosa.behavior.service.job_meets_deadline, prosa.behavior.service.completed_by.
        cbn [I.Prosa_Behavior_Service_job_meets_deadline I.Prosa_Behavior_Service_completed_by].
        exact (svc_decide_le_related _ _ _ _ (Hcost j) (swp_service_related j _ _ (Hdl j))).
      Qed.
    End Cost.
  End Observations.

  Let cover_state :=
    swp_forall_cover_sprop _ _ (svc_ps_state_rel Job PStateR PStateL R)
      (svc_ps_state_to_target Job PStateR PStateL R) (svc_ps_state_to_source Job PStateR PStateL R)
      (svc_ps_state_rel_canonical Job PStateR PStateL R) (svc_ps_state_rel_surjective Job PStateR PStateL R).

  Lemma swp_unit_service_related :
    PropSPropRel (@prosa.model.processor.platform_properties.unit_service_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.unit_service_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model].
    apply ar_forall_identity_correspondence. intro j'.
    apply cover_state. intros sR sL Hs.
    exact (sub_nat_le_correspondence _ _ _ _ (svc_service_in_related Job PStateR PStateL R j' sR sL Hs)
      (sub_nat_rel_canonical 1)).
  Qed.

  Lemma swp_ideal_progress_related :
    PropSPropRel (@prosa.model.processor.platform_properties.ideal_progress_proc_model Job PStateR)
      (I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job dJ PStateL).
  Proof.
    unfold prosa.model.processor.platform_properties.ideal_progress_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model].
    apply ar_forall_identity_correspondence. intro j'.
    apply cover_state. intros sR sL Hs.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (svc_scheduled_in_related Job PStateR PStateL R j' sR sL Hs))|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O)
      (svc_service_in_related Job PStateR PStateL R j' sR sL Hs)).
  Qed.

  Definition swp_arrival_sequence_to_source
      (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ) :
      prosa.behavior.arrival_sequence.arrival_sequence Job :=
    fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

  Lemma swp_arrival_sequence_to_source_rel arrL :
    ArArrivalSequenceRel Job (swp_arrival_sequence_to_source arrL) arrL.
  Proof.
    intros tR tL Ht. unfold ArListRel, swp_arrival_sequence_to_source.
    exact (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _)
      (sub_imported_eq_congr arrL _ _ Ht)).
  Qed.

  Let cover_arr :=
    swp_forall_cover_sprop _ _ (ArArrivalSequenceRel Job)
      (ar_arrival_sequence_to_imported Job) swp_arrival_sequence_to_source
      (ar_arrival_sequence_canonical Job) swp_arrival_sequence_to_source_rel.

  (** *** Statements over a leading schedule *)

  Section Sched.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SwpScheduleFunRel schedR schedL.

    Let SW t1R t1L H1 t2R t2L H2 := swp_swapped_fun schedR schedL Hsched t1R t1L H1 t2R t2L H2.

    Ltac swp_t12 :=
      apply ar_forall_nat_correspondence; let t1R := fresh "t1R" in let t1L := fresh "t1L" in
        let H1 := fresh "H1" in intros t1R t1L H1;
      apply ar_forall_nat_correspondence; let t2R := fresh "t2R" in let t2L := fresh "t2L" in
        let H2 := fresh "H2" in intros t2R t2L H2.

    Definition src_trivial_swap : Prop :=
      ltac:(body_of (fun s : S.statement_trivial_swap => s Job PStateR schedR)).
    Definition tgt_trivial_swap : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_trivial_swap Job dJ PStateL schedL)).
    Theorem trivial_swap_correspondence : PropSPropRel src_trivial_swap tgt_trivial_swap.
    Proof.
      swp_t12.
      apply ar_imp_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ H1 H2)|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      exact (swp_state_eq_correspondence _ _ _ _ (Hsched tR tL Ht) (SW _ _ H1 _ _ H2 tR tL Ht)).
    Qed.

    Definition src_trivial_swap_service_invariant : Prop :=
      ltac:(body_of (fun s : S.statement_trivial_swap_service_invariant => s Job PStateR schedR)).
    Definition tgt_trivial_swap_service_invariant : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_trivial_swap_service_invariant
        Job dJ PStateL schedL)).
    Theorem trivial_swap_service_invariant_correspondence :
      PropSPropRel src_trivial_swap_service_invariant tgt_trivial_swap_service_invariant.
    Proof.
      swp_t12.
      apply ar_imp_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ H1 H2)|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_identity_correspondence. intro j.
      exact (sub_nat_eq_correspondence _ _ _ _ (swp_service_related _ _ Hsched j _ _ Ht)
        (swp_service_related _ _ (SW _ _ H1 _ _ H2) j _ _ Ht)).
    Qed.

    Definition src_swap_other_times_invariant : Prop :=
      ltac:(body_of (fun s : S.statement_swap_other_times_invariant => s Job PStateR schedR)).
    Definition tgt_swap_other_times_invariant : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_swap_other_times_invariant
        Job dJ PStateL schedL)).
    Theorem swap_other_times_invariant_correspondence :
      PropSPropRel src_swap_other_times_invariant tgt_swap_other_times_invariant.
    Proof.
      swp_t12.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (swp_nat_neq_correspondence _ _ _ _ Ht H1)|].
      apply ar_imp_correspondence; [exact (swp_nat_neq_correspondence _ _ _ _ Ht H2)|].
      exact (swp_state_eq_correspondence _ _ _ _ (Hsched tR tL Ht) (SW _ _ H1 _ _ H2 tR tL Ht)).
    Qed.

    Definition src_swap_job_scheduled_t1 : Prop :=
      ltac:(body_of (fun s : S.statement_swap_job_scheduled_t1 => s Job PStateR schedR)).
    Definition tgt_swap_job_scheduled_t1 : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_swap_job_scheduled_t1
        Job dJ PStateL schedL)).
    Theorem swap_job_scheduled_t1_correspondence :
      PropSPropRel src_swap_job_scheduled_t1 tgt_swap_job_scheduled_t1.
    Proof.
      swp_t12.
      apply ar_forall_identity_correspondence. intro j.
      exact (swp_bool_eq_correspondence _ _ _ _
        (swp_scheduled_at_related _ _ (SW _ _ H1 _ _ H2) j _ _ H1)
        (swp_scheduled_at_related _ _ Hsched j _ _ H2)).
    Qed.

    Definition src_swap_job_scheduled_t2 : Prop :=
      ltac:(body_of (fun s : S.statement_swap_job_scheduled_t2 => s Job PStateR schedR)).
    Definition tgt_swap_job_scheduled_t2 : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_swap_job_scheduled_t2
        Job dJ PStateL schedL)).
    Theorem swap_job_scheduled_t2_correspondence :
      PropSPropRel src_swap_job_scheduled_t2 tgt_swap_job_scheduled_t2.
    Proof.
      swp_t12.
      apply ar_forall_identity_correspondence. intro j.
      exact (swp_bool_eq_correspondence _ _ _ _
        (swp_scheduled_at_related _ _ (SW _ _ H1 _ _ H2) j _ _ H2)
        (swp_scheduled_at_related _ _ Hsched j _ _ H1)).
    Qed.

    Definition src_swap_job_scheduled_other_times : Prop :=
      ltac:(body_of (fun s : S.statement_swap_job_scheduled_other_times => s Job PStateR schedR)).
    Definition tgt_swap_job_scheduled_other_times : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_swap_job_scheduled_other_times
        Job dJ PStateL schedL)).
    Theorem swap_job_scheduled_other_times_correspondence :
      PropSPropRel src_swap_job_scheduled_other_times tgt_swap_job_scheduled_other_times.
    Proof.
      swp_t12.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (swp_nat_neqb_related _ _ _ _ H1 Ht))|].
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (swp_nat_neqb_related _ _ _ _ H2 Ht))|].
      exact (swp_bool_eq_correspondence _ _ _ _
        (swp_scheduled_at_related _ _ (SW _ _ H1 _ _ H2) j _ _ Ht)
        (swp_scheduled_at_related _ _ Hsched j _ _ Ht)).
    Qed.

    Section Cases.
      Variables (t1R t2R : nat) (t1L t2L : Lean.Nat).
      Hypotheses (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L).
      Let SWc := SW _ _ H1 _ _ H2.
      Let SA' j tR tL (Ht : SubNatRel tR tL) := swp_scheduled_at_related _ _ SWc j tR tL Ht.
      Let SA j tR tL (Ht : SubNatRel tR tL) := swp_scheduled_at_related _ _ Hsched j tR tL Ht.

      Lemma swp_cases_related (j : Job) (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
        PropSPropRel
          (@prosa.behavior.service.scheduled_at Job PStateR
              (@prosa.analysis.transform.swap.swapped Job PStateR schedR t1R t2R) j tR =
             @prosa.behavior.service.scheduled_at Job PStateR schedR j tR
           \/ (tR = t1R /\ @prosa.behavior.service.scheduled_at Job PStateR
                 (@prosa.analysis.transform.swap.swapped Job PStateR schedR t1R t2R) j tR =
               @prosa.behavior.service.scheduled_at Job PStateR schedR j t2R)
           \/ (tR = t2R /\ @prosa.behavior.service.scheduled_at Job PStateR
                 (@prosa.analysis.transform.swap.swapped Job PStateR schedR t1R t2R) j tR =
               @prosa.behavior.service.scheduled_at Job PStateR schedR j t1R))
          (Lean.Or
            (Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL
                (I.Prosa_Analysis_Transform_Swap_swapped Job dJ PStateL schedL t1L t2L) j tL)
              (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL))
            (Lean.Or
              (Lean.And (Lean.eq tL t1L)
                (Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL
                    (I.Prosa_Analysis_Transform_Swap_swapped Job dJ PStateL schedL t1L t2L) j tL)
                  (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j t2L)))
              (Lean.And (Lean.eq tL t2L)
                (Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL
                    (I.Prosa_Analysis_Transform_Swap_swapped Job dJ PStateL schedL t1L t2L) j tL)
                  (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j t1L))))).
      Proof.
        apply swp_or_correspondence;
          [exact (swp_bool_eq_correspondence _ _ _ _ (SA' j _ _ Ht) (SA j _ _ Ht))|].
        apply swp_or_correspondence.
        - apply ar_and_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ Ht H1)|].
          exact (swp_bool_eq_correspondence _ _ _ _ (SA' j _ _ Ht) (SA j _ _ H2)).
        - apply ar_and_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ Ht H2)|].
          exact (swp_bool_eq_correspondence _ _ _ _ (SA' j _ _ Ht) (SA j _ _ H1)).
      Qed.

      Lemma swp_original_cases_related (j : Job) (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
        PropSPropRel
          (@prosa.behavior.service.scheduled_at Job PStateR
              (@prosa.analysis.transform.swap.swapped Job PStateR schedR t1R t2R) j tR =
             @prosa.behavior.service.scheduled_at Job PStateR schedR j tR
           \/ (tR = t1R /\ @prosa.behavior.service.scheduled_at Job PStateR
                 (@prosa.analysis.transform.swap.swapped Job PStateR schedR t1R t2R) j t2R =
               @prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
           \/ (tR = t2R /\ @prosa.behavior.service.scheduled_at Job PStateR
                 (@prosa.analysis.transform.swap.swapped Job PStateR schedR t1R t2R) j t1R =
               @prosa.behavior.service.scheduled_at Job PStateR schedR j tR))
          (Lean.Or
            (Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL
                (I.Prosa_Analysis_Transform_Swap_swapped Job dJ PStateL schedL t1L t2L) j tL)
              (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL))
            (Lean.Or
              (Lean.And (Lean.eq tL t1L)
                (Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL
                    (I.Prosa_Analysis_Transform_Swap_swapped Job dJ PStateL schedL t1L t2L) j t2L)
                  (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL)))
              (Lean.And (Lean.eq tL t2L)
                (Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL
                    (I.Prosa_Analysis_Transform_Swap_swapped Job dJ PStateL schedL t1L t2L) j t1L)
                  (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL))))).
      Proof.
        apply swp_or_correspondence;
          [exact (swp_bool_eq_correspondence _ _ _ _ (SA' j _ _ Ht) (SA j _ _ Ht))|].
        apply swp_or_correspondence.
        - apply ar_and_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ Ht H1)|].
          exact (swp_bool_eq_correspondence _ _ _ _ (SA' j _ _ H2) (SA j _ _ Ht)).
        - apply ar_and_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ Ht H2)|].
          exact (swp_bool_eq_correspondence _ _ _ _ (SA' j _ _ H1) (SA j _ _ Ht)).
      Qed.
    End Cases.

    Definition src_swap_job_scheduled_cases : Prop :=
      ltac:(body_of (fun s : S.statement_swap_job_scheduled_cases => s Job PStateR schedR)).
    Definition tgt_swap_job_scheduled_cases : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_swap_job_scheduled_cases
        Job dJ PStateL schedL)).
    Theorem swap_job_scheduled_cases_correspondence :
      PropSPropRel src_swap_job_scheduled_cases tgt_swap_job_scheduled_cases.
    Proof.
      swp_t12.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _
          (swp_scheduled_at_related _ _ (SW _ _ H1 _ _ H2) j _ _ Ht))|].
      exact (swp_cases_related _ _ _ _ H1 H2 j _ _ Ht).
    Qed.

    Definition src_swap_job_scheduled : Prop :=
      ltac:(body_of (fun s : S.statement_swap_job_scheduled => s Job PStateR schedR)).
    Definition tgt_swap_job_scheduled : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_swap_job_scheduled
        Job dJ PStateL schedL)).
    Theorem swap_job_scheduled_correspondence :
      PropSPropRel src_swap_job_scheduled tgt_swap_job_scheduled.
    Proof.
      swp_t12.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _
          (swp_scheduled_at_related _ _ (SW _ _ H1 _ _ H2) j _ _ Ht))|].
      apply ar_exists_nat_correspondence. intros sR sL Hs.
      exact (svc_bool_truth_correspondence _ _ (swp_scheduled_at_related _ _ Hsched j _ _ Hs)).
    Qed.

    Definition src_swap_job_scheduled_original_cases : Prop :=
      ltac:(body_of (fun s : S.statement_swap_job_scheduled_original_cases => s Job PStateR schedR)).
    Definition tgt_swap_job_scheduled_original_cases : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_swap_job_scheduled_original_cases
        Job dJ PStateL schedL)).
    Theorem swap_job_scheduled_original_cases_correspondence :
      PropSPropRel src_swap_job_scheduled_original_cases tgt_swap_job_scheduled_original_cases.
    Proof.
      swp_t12.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (swp_scheduled_at_related _ _ Hsched j _ _ Ht))|].
      exact (swp_original_cases_related _ _ _ _ H1 H2 j _ _ Ht).
    Qed.

    Definition src_swap_job_scheduled_original : Prop :=
      ltac:(body_of (fun s : S.statement_swap_job_scheduled_original => s Job PStateR schedR)).
    Definition tgt_swap_job_scheduled_original : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_swap_job_scheduled_original
        Job dJ PStateL schedL)).
    Theorem swap_job_scheduled_original_correspondence :
      PropSPropRel src_swap_job_scheduled_original tgt_swap_job_scheduled_original.
    Proof.
      swp_t12.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (swp_scheduled_at_related _ _ Hsched j _ _ Ht))|].
      apply ar_exists_nat_correspondence. intros sR sL Hs.
      exact (svc_bool_truth_correspondence _ _
        (swp_scheduled_at_related _ _ (SW _ _ H1 _ _ H2) j _ _ Hs)).
    Qed.

    Ltac swp_ordered :=
      swp_t12;
      apply ar_imp_correspondence;
        [exact (sub_nat_le_correspondence _ _ _ _ ltac:(assumption) ltac:(assumption))|].

    Definition src_swap_before_invariant : Prop :=
      ltac:(body_of (fun s : S.statement_swap_before_invariant => s Job PStateR schedR)).
    Definition tgt_swap_before_invariant : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_swap_before_invariant
        Job dJ PStateL schedL)).
    Theorem swap_before_invariant_correspondence :
      PropSPropRel src_swap_before_invariant tgt_swap_before_invariant.
    Proof.
      swp_t12.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Ht H1)|].
      exact (swp_state_eq_correspondence _ _ _ _ (Hsched tR tL Ht) (SW _ _ H1 _ _ H2 tR tL Ht)).
    Qed.

    Definition src_swap_after_invariant : Prop :=
      ltac:(body_of (fun s : S.statement_swap_after_invariant => s Job PStateR schedR)).
    Definition tgt_swap_after_invariant : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_swap_after_invariant
        Job dJ PStateL schedL)).
    Theorem swap_after_invariant_correspondence :
      PropSPropRel src_swap_after_invariant tgt_swap_after_invariant.
    Proof.
      swp_t12.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ H2 Ht)|].
      exact (swp_state_eq_correspondence _ _ _ _ (Hsched tR tL Ht) (SW _ _ H1 _ _ H2 tR tL Ht)).
    Qed.

    Definition src_service_before_swap_invariant : Prop :=
      ltac:(body_of (fun s : S.statement_service_before_swap_invariant => s Job PStateR schedR)).
    Definition tgt_service_before_swap_invariant : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_service_before_swap_invariant
        Job dJ PStateL schedL)).
    Theorem service_before_swap_invariant_correspondence :
      PropSPropRel src_service_before_swap_invariant tgt_service_before_swap_invariant.
    Proof.
      swp_t12.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht H1)|].
      apply ar_forall_identity_correspondence. intro j.
      exact (sub_nat_eq_correspondence _ _ _ _ (swp_service_related _ _ Hsched j _ _ Ht)
        (swp_service_related _ _ (SW _ _ H1 _ _ H2) j _ _ Ht)).
    Qed.

    Definition src_service_after_swap_invariant : Prop :=
      ltac:(body_of (fun s : S.statement_service_after_swap_invariant => s Job PStateR schedR)).
    Definition tgt_service_after_swap_invariant : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_service_after_swap_invariant
        Job dJ PStateL schedL)).
    Theorem service_after_swap_invariant_correspondence :
      PropSPropRel src_service_after_swap_invariant tgt_service_after_swap_invariant.
    Proof.
      swp_t12.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ H2 Ht)|].
      apply ar_forall_identity_correspondence. intro j.
      exact (sub_nat_eq_correspondence _ _ _ _ (swp_service_related _ _ Hsched j _ _ Ht)
        (swp_service_related _ _ (SW _ _ H1 _ _ H2) j _ _ Ht)).
    Qed.

    Definition src_service_of_others_invariant : Prop :=
      ltac:(body_of (fun s : S.statement_service_of_others_invariant => s Job PStateR schedR)).
    Definition tgt_service_of_others_invariant : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_service_of_others_invariant
        Job dJ PStateL schedL)).
    Theorem service_of_others_invariant_correspondence :
      PropSPropRel src_service_of_others_invariant tgt_service_of_others_invariant.
    Proof.
      swp_t12.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _
          (svc_scheduled_in_related Job PStateR PStateL R j _ _ (swp_state_rel _ _ (Hsched _ _ H1)))))|].
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _
          (svc_scheduled_in_related Job PStateR PStateL R j _ _ (swp_state_rel _ _ (Hsched _ _ H2)))))|].
      exact (sub_nat_eq_correspondence _ _ _ _ (swp_service_related _ _ Hsched j _ _ Ht)
        (swp_service_related _ _ (SW _ _ H1 _ _ H2) j _ _ Ht)).
    Qed.

    Definition src_swapped_jobs_come_from_arrival_sequence : Prop :=
      ltac:(body_of (fun s : S.statement_swapped_jobs_come_from_arrival_sequence => s Job PStateR schedR)).
    Definition tgt_swapped_jobs_come_from_arrival_sequence : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_swapped_jobs_come_from_arrival_sequence
        Job dJ PStateL schedL)).
    Theorem swapped_jobs_come_from_arrival_sequence_correspondence :
      PropSPropRel src_swapped_jobs_come_from_arrival_sequence
        tgt_swapped_jobs_come_from_arrival_sequence.
    Proof.
      swp_t12.
      apply cover_arr. intros arrR arrL Harr.
      have FROM := fun sR sL (Hs : SwpScheduleFunRel sR sL) =>
        (ltac:(unfold prosa.behavior.ready.jobs_come_from_arrival_sequence;
          cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence];
          apply ar_forall_identity_correspondence; intro j;
          apply ar_forall_nat_correspondence; intros tR tL Ht;
          apply ar_imp_correspondence;
            [exact (svc_bool_truth_correspondence _ _ (swp_scheduled_at_related _ _ Hs j tR tL Ht))|];
          exact (arrives_in_correspondence_certificate Job arrR arrL j Harr))
        : PropSPropRel (@prosa.behavior.ready.jobs_come_from_arrival_sequence Job PStateR sR arrR)
            (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job dJ PStateL sL arrL)).
      apply ar_imp_correspondence; [exact (FROM _ _ Hsched)|].
      exact (FROM _ _ (SW _ _ H1 _ _ H2)).
    Qed.

    Section CostStatements.
      Variable costR : prosa.behavior.job.JobCost Job.
      Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
      Hypothesis Hcost : SvcJobCostRel Job costR costL.

      Definition src_swapped_service_bound : Prop :=
        ltac:(body_of (fun s : S.statement_swapped_service_bound => s Job costR PStateR schedR)).
      Definition tgt_swapped_service_bound : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_swapped_service_bound
          Job dJ PStateL costL schedL)).
      Theorem swapped_service_bound_correspondence :
        PropSPropRel src_swapped_service_bound tgt_swapped_service_bound.
      Proof.
        swp_t12.
        apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
        apply ar_imp_correspondence; [exact (swp_service_bound_related _ _ Hsched _ _ Hcost)|].
        exact (swp_service_bound_related _ _ (SW _ _ H1 _ _ H2) _ _ Hcost).
      Qed.

      Definition src_swapped_completed_jobs_dont_execute : Prop :=
        ltac:(body_of (fun s : S.statement_swapped_completed_jobs_dont_execute => s Job costR PStateR schedR)).
      Definition tgt_swapped_completed_jobs_dont_execute : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_swapped_completed_jobs_dont_execute
          Job dJ PStateL costL schedL)).
      Theorem swapped_completed_jobs_dont_execute_correspondence :
        PropSPropRel src_swapped_completed_jobs_dont_execute tgt_swapped_completed_jobs_dont_execute.
      Proof.
        swp_t12.
        apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
        apply ar_imp_correspondence; [exact swp_unit_service_related|].
        apply ar_imp_correspondence; [exact swp_ideal_progress_related|].
        apply ar_imp_correspondence; [exact (swp_completed_jobs_dont_execute_related _ _ Hsched _ _ Hcost)|].
        exact (swp_completed_jobs_dont_execute_related _ _ (SW _ _ H1 _ _ H2) _ _ Hcost).
      Qed.

      Variable dlR : prosa.behavior.job.JobDeadline Job.
      Variable dlL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
      Hypothesis Hdl : forall j : Job,
        SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
          (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).

      Let MEETS := swp_job_meets_deadline_related _ _ Hsched _ _ Hcost _ _ Hdl.
      Let MEETS' t1R t1L H1 t2R t2L H2 :=
        swp_job_meets_deadline_related _ _ (SW t1R t1L H1 t2R t2L H2) _ _ Hcost _ _ Hdl.

      Definition src_uninvolved_implies_deadline_met : Prop :=
        ltac:(body_of (fun s : S.statement_uninvolved_implies_deadline_met => s Job costR dlR PStateR schedR)).
      Definition tgt_uninvolved_implies_deadline_met : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_uninvolved_implies_deadline_met
          Job dJ costL dlL PStateL schedL)).
      Theorem uninvolved_implies_deadline_met_correspondence :
        PropSPropRel src_uninvolved_implies_deadline_met tgt_uninvolved_implies_deadline_met.
      Proof.
        swp_t12.
        apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (MEETS j))|].
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _
            (swp_scheduled_at_related _ _ Hsched j _ _ H1)))|].
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _
            (swp_scheduled_at_related _ _ Hsched j _ _ H2)))|].
        exact (svc_bool_truth_correspondence _ _ (MEETS' _ _ H1 _ _ H2 j)).
      Qed.

      Let NOT_EDF t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
        PropSPropRel
          (forall j1 j2 : Job, @prosa.behavior.service.scheduled_at Job PStateR schedR j1 t1R ->
            @prosa.behavior.service.scheduled_at Job PStateR schedR j2 t2R ->
            is_true (leq (@prosa.behavior.job.job_deadline Job dlR j2) (@prosa.behavior.job.job_deadline Job dlR j1)))
          (forall j1 j2 : Job,
            Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j1 t1L) I.Bool_true ->
            Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j2 t2L) I.Bool_true ->
            svc_target_le (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j2)
              (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j1)).
      Proof.
        apply ar_forall_identity_correspondence. intro j1.
        apply ar_forall_identity_correspondence. intro j2.
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (swp_scheduled_at_related _ _ Hsched j1 _ _ H1))|].
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (swp_scheduled_at_related _ _ Hsched j2 _ _ H2))|].
        exact (sub_nat_le_correspondence _ _ _ _ (Hdl j2) (Hdl j1)).
      Qed.

      Let NO_IDLE t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
        PropSPropRel
          (forall j1 : Job, @prosa.behavior.service.scheduled_at Job PStateR schedR j1 t1R ->
            exists j2 : Job, @prosa.behavior.service.scheduled_at Job PStateR schedR j2 t2R /\
              is_true (ltn t2R (@prosa.behavior.job.job_deadline Job dlR j2)))
          (forall j1 : Job,
            Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j1 t1L) I.Bool_true ->
            I.Exists Job (fun j2 =>
              Lean.And (Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j2 t2L) I.Bool_true)
                (svc_target_lt t2L (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j2)))).
      Proof.
        apply ar_forall_identity_correspondence. intro j1.
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (swp_scheduled_at_related _ _ Hsched j1 _ _ H1))|].
        apply swp_exists_identity. intro j2.
        apply ar_and_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (swp_scheduled_at_related _ _ Hsched j2 _ _ H2))|].
        exact (sub_nat_lt_correspondence _ _ _ _ H2 (Hdl j2)).
      Qed.

      Definition src_moved_earlier_implies_deadline_met : Prop :=
        ltac:(body_of (fun s : S.statement_moved_earlier_implies_deadline_met => s Job costR dlR PStateR schedR)).
      Definition tgt_moved_earlier_implies_deadline_met : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_moved_earlier_implies_deadline_met
          Job dJ costL dlL PStateL schedL)).
      Theorem moved_earlier_implies_deadline_met_correspondence :
        PropSPropRel src_moved_earlier_implies_deadline_met tgt_moved_earlier_implies_deadline_met.
      Proof.
        apply ar_imp_correspondence; [exact (swp_completed_jobs_dont_execute_related _ _ Hsched _ _ Hcost)|].
        swp_t12.
        apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (MEETS j))|].
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (swp_scheduled_at_related _ _ Hsched j _ _ H2))|].
        exact (svc_bool_truth_correspondence _ _ (MEETS' _ _ H1 _ _ H2 j)).
      Qed.

      Definition src_moved_later_implies_deadline_met : Prop :=
        ltac:(body_of (fun s : S.statement_moved_later_implies_deadline_met => s Job costR dlR PStateR schedR)).
      Definition tgt_moved_later_implies_deadline_met : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_moved_later_implies_deadline_met
          Job dJ costL dlL PStateL schedL)).
      Theorem moved_later_implies_deadline_met_correspondence :
        PropSPropRel src_moved_later_implies_deadline_met tgt_moved_later_implies_deadline_met.
      Proof.
        swp_t12.
        apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
        apply ar_imp_correspondence; [exact (NOT_EDF _ _ H1 _ _ H2)|].
        apply ar_imp_correspondence; [exact (NO_IDLE _ _ H1 _ _ H2)|].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (MEETS j))|].
        apply ar_imp_correspondence;
          [exact (svc_bool_truth_correspondence _ _ (swp_scheduled_at_related _ _ Hsched j _ _ H1))|].
        exact (svc_bool_truth_correspondence _ _ (MEETS' _ _ H1 _ _ H2 j)).
      Qed.

      Definition src_edf_swap_no_deadline_misses_introduced : Prop :=
        ltac:(body_of (fun s : S.statement_edf_swap_no_deadline_misses_introduced =>
          s Job costR dlR PStateR schedR)).
      Definition tgt_edf_swap_no_deadline_misses_introduced : SProp :=
        ltac:(type_of_term (@I.Prosa_Analysis_Facts_Transform_Swaps_edf_swap_no_deadline_misses_introduced
          Job dJ costL dlL PStateL schedL)).
      Theorem edf_swap_no_deadline_misses_introduced_correspondence :
        PropSPropRel src_edf_swap_no_deadline_misses_introduced
          tgt_edf_swap_no_deadline_misses_introduced.
      Proof.
        apply ar_imp_correspondence; [exact (swp_completed_jobs_dont_execute_related _ _ Hsched _ _ Hcost)|].
        swp_t12.
        apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
        apply ar_imp_correspondence; [exact (NOT_EDF _ _ H1 _ _ H2)|].
        apply ar_imp_correspondence; [exact (NO_IDLE _ _ H1 _ _ H2)|].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (MEETS j))|].
        exact (svc_bool_truth_correspondence _ _ (MEETS' _ _ H1 _ _ H2 j)).
      Qed.
    End CostStatements.
  End Sched.
End Swaps.
