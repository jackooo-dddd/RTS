(* Re-bound copy of accepted certificates/analysis_facts_behavior_supply/FactsSupplyStatementCorrespondence.v for the analysis/facts/SBF artifact;
   only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import analysis.facts.behavior.supply.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSbfFacts
  ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence FsScheduleBaseAdapter
  FsScheduleFiniteOperations FsScheduleCorrespondence
  FsProcessorStateCorrespondence SupplyBaseAdapter
  SupplyNatBoolOperations SupplyIntervalOperations
  FactsSupplyPlatformPropertiesCorrespondence
  FactsSupplyOperationCorrespondence.

(** Statement correspondence only: the 16 exact target theorem *types* are
    imported from a proof-clean Lean module.  No source or target facts theorem
    proof is used below.  All computational observations are bridged by
    independently checked, artifact-local operation certificates. *)

Definition fs_target_le (a b : Lean.Nat) : SProp :=
  ImportedSbfFacts.LE_le_inst1 Lean.Nat
    ImportedSbfFacts.instLENat a b.

Definition fs_target_lt (a b : Lean.Nat) : SProp :=
  ImportedSbfFacts.LT_lt_inst1 Lean.Nat
    ImportedSbfFacts.instLTNat a b.

Lemma fs_forall_job_correspondence (Job : eqType)
    (PR : Job -> Prop) (PL : Job -> SProp) :
  (forall j, PropSPropRel (PR j) (PL j)) ->
  PropSPropRel (forall j, PR j) (forall j, PL j).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros Hsource j. exact (prop_to_sprop _ _ (HP j) (Hsource j)).
  - intro Htarget. apply strictly_inhabits. intro j.
    exact (sprop_to_prop _ _ (HP j) (Htarget j)).
Qed.

Lemma fs_forall_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall tR tL, SubNatRel tR tL ->
    PropSPropRel (PR tR) (PL tL)) ->
  PropSPropRel (forall tR, PR tR) (forall tL, PL tL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros Hsource tL.
    pose (tR := sub_nat_to_rocq tL).
    exact (prop_to_sprop _ _
      (HP tR tL (sub_nat_rel_surjective tL)) (Hsource tR)).
  - intro Htarget. apply strictly_inhabits. intro tR.
    pose (tL := sub_nat_to_imported tR).
    exact (sprop_to_prop _ _
      (HP tR tL (sub_nat_rel_canonical tR)) (Htarget tL)).
Qed.

Lemma fs_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros Hsource HPL.
    exact (prop_to_sprop _ _ HQ
      (Hsource (sprop_to_prop _ _ HP HPL))).
  - intro Htarget. apply strictly_inhabits. intro HPsource.
    exact (sprop_to_prop _ _ HQ
      (Htarget (prop_to_sprop _ _ HP HPsource))).
Qed.

Lemma fs_or_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p|q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intro H. destruct H as [p|q].
    + exact (strictly_inhabits (or_introl _ (sprop_to_prop _ _ HP p))).
    + exact (strictly_inhabits (or_intror _ (sprop_to_prop _ _ HQ q))).
Qed.

Lemma fs_bool_and_left (a b : bool) :
  is_true (a && b) -> is_true a.
Proof. by move/andP=> [Ha _]. Qed.

Lemma fs_bool_and_right (a b : bool) :
  is_true (a && b) -> is_true b.
Proof. by move/andP=> [_ Hb]. Qed.

Lemma fs_bool_and_intro (a b : bool) :
  is_true a -> is_true b -> is_true (a && b).
Proof. by move=> Ha Hb; apply/andP; split. Qed.

Lemma fs_le_chain_correspondence
    (aR bR cR : nat) (aL bL cL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel cR cL ->
  PropSPropRel (is_true ((leq aR bR) && (leq bR cR)))
    (Lean.And (fs_target_le aL bL) (fs_target_le bL cL)).
Proof.
  intros Ha Hb Hc.
  pose proof (sub_nat_le_correspondence aR aL bR bL Ha Hb) as Hab.
  pose proof (sub_nat_le_correspondence bR bL cR cL Hb Hc) as Hbc.
  apply prop_sprop_rel_intro.
  - intro Hsource. exact (Lean.And_intro _ _
      (prop_to_sprop _ _ Hab (fs_bool_and_left _ _ Hsource))
      (prop_to_sprop _ _ Hbc (fs_bool_and_right _ _ Hsource))).
  - exact (fun Htarget =>
      match Htarget with
      | Lean.And_intro HabL HbcL =>
          strictly_inhabits
            (fs_bool_and_intro _ _
              (sprop_to_prop _ _ Hab HabL)
              (sprop_to_prop _ _ Hbc HbcL))
      end).
Qed.

Section FactsSupplyStatements.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedSbfFacts.Prosa_Behavior_Schedule_ProcessorState
      Job (sch_decidable_eq Job).
  Variable R : SchProcessorStateRel Job PStateR PStateL.

  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL :
    ImportedSbfFacts.Prosa_Behavior_Schedule_schedule
      Job (sch_decidable_eq Job) PStateL.
  Hypothesis Hsched :
    SchScheduleRel Job PStateR PStateL
      (sch_ps_state_rel Job PStateR PStateL R) schedR schedL.

  Lemma fs_service_at_le_supply_at_correspondence :
    PropSPropRel
      (forall (j : Job) (t : nat),
        is_true (leq
          (@prosa.behavior.service.service_at Job PStateR schedR j t)
          (@prosa.model.processor.supply.supply_at Job PStateR schedR t)))
      (forall (j : Job) (t : Lean.Nat),
        fs_target_le
          (ImportedSbfFacts.Prosa_Behavior_Service_service_at
            Job (sch_decidable_eq Job) PStateL schedL j t)
          (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_at
            Job (sch_decidable_eq Job) PStateL schedL t)).
  Proof.
    apply fs_forall_job_correspondence. intro j.
    apply fs_forall_nat_correspondence. intros tR tL Ht.
    exact (sub_nat_le_correspondence _ _ _ _
      (fs_service_at_related Job PStateR PStateL R schedR schedL Hsched
        j tR tL Ht)
      (fs_supply_at_related Job PStateR PStateL R schedR schedL Hsched
        tR tL Ht)).
  Qed.

  Lemma fs_pos_service_impl_pos_supply_correspondence :
    PropSPropRel
      (forall (j : Job) (t : nat),
        is_true (ltn O
          (@prosa.behavior.service.service_at Job PStateR schedR j t)) ->
        is_true (ltn O
          (@prosa.model.processor.supply.supply_at Job PStateR schedR t)))
      (forall (j : Job) (t : Lean.Nat),
        fs_target_lt Lean.Nat_zero
          (ImportedSbfFacts.Prosa_Behavior_Service_service_at
            Job (sch_decidable_eq Job) PStateL schedL j t) ->
        fs_target_lt Lean.Nat_zero
          (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_at
            Job (sch_decidable_eq Job) PStateL schedL t)).
  Proof.
    apply fs_forall_job_correspondence. intro j.
    apply fs_forall_nat_correspondence. intros tR tL Ht.
    apply fs_imp_correspondence.
    - exact (sub_nat_lt_correspondence O Lean.Nat_zero _ _
        (sub_nat_rel_canonical O)
        (fs_service_at_related Job PStateR PStateL R schedR schedL Hsched
          j tR tL Ht)).
    - exact (sub_nat_lt_correspondence O Lean.Nat_zero _ _
        (sub_nat_rel_canonical O)
        (fs_supply_at_related Job PStateR PStateL R schedR schedL Hsched
          tR tL Ht)).
  Qed.

  Lemma fs_blackout_or_supply_correspondence :
    PropSPropRel
      (forall t : nat,
        is_true (@prosa.model.processor.supply.is_blackout
          Job PStateR schedR t) \/
        is_true (@prosa.model.processor.supply.has_supply
          Job PStateR schedR t))
      (forall t : Lean.Nat,
        Lean.Or
          (Lean.eq
            (ImportedSbfFacts.Prosa_Model_Processor_Supply_is_blackout
              Job (sch_decidable_eq Job) PStateL schedL t)
            ImportedSbfFacts.Bool_true)
          (Lean.eq
            (ImportedSbfFacts.Prosa_Model_Processor_Supply_has_supply
              Job (sch_decidable_eq Job) PStateL schedL t)
            ImportedSbfFacts.Bool_true)).
  Proof.
    apply fs_forall_nat_correspondence. intros tR tL Ht.
    apply fs_or_correspondence.
    - exact (svc_bool_truth_correspondence _ _
        (fs_is_blackout_related Job PStateR PStateL R schedR schedL Hsched
          tR tL Ht)).
    - exact (svc_bool_truth_correspondence _ _
        (fs_has_supply_related Job PStateR PStateL R schedR schedL Hsched
          tR tL Ht)).
  Qed.

  Lemma fs_supply_at_complement_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.unit_supply_proc_model
        Job PStateR ->
       forall t : nat,
         Logic.eq
           (@prosa.model.processor.supply.supply_at Job PStateR schedR t)
           ((S O) - nat_of_bool
             (@prosa.model.processor.supply.is_blackout
               Job PStateR schedR t)))
      (ImportedSbfFacts.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model
         Job (sch_decidable_eq Job) PStateL ->
       forall t : Lean.Nat,
         Lean.eq
           (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_at
             Job (sch_decidable_eq Job) PStateL schedL t)
           (svc_target_sub svc_target_one
             (ImportedSbfFacts.Bool_toNat
               (ImportedSbfFacts.Prosa_Model_Processor_Supply_is_blackout
                 Job (sch_decidable_eq Job) PStateL schedL t)))).
  Proof.
    apply fs_imp_correspondence.
    - exact (fs_unit_supply_proc_model_correspondence
        Job PStateR PStateL R).
    - apply fs_forall_nat_correspondence. intros tR tL Ht.
      apply sub_nat_eq_correspondence.
      + exact (fs_supply_at_related Job PStateR PStateL R schedR schedL
          Hsched tR tL Ht).
      + apply svc_target_sub_related.
        * exact (sub_nat_rel_canonical (S O)).
        * exact (fs_bool_to_nat_related _ _
            (fs_is_blackout_related Job PStateR PStateL R
              schedR schedL Hsched tR tL Ht)).
  Qed.

  Lemma fs_is_blackout_complement_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.unit_supply_proc_model
        Job PStateR ->
       forall t : nat,
         Logic.eq
           (nat_of_bool
             (@prosa.model.processor.supply.is_blackout
               Job PStateR schedR t))
           ((S O) - @prosa.model.processor.supply.supply_at
             Job PStateR schedR t))
      (ImportedSbfFacts.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model
         Job (sch_decidable_eq Job) PStateL ->
       forall t : Lean.Nat,
         Lean.eq
           (ImportedSbfFacts.Bool_toNat
             (ImportedSbfFacts.Prosa_Model_Processor_Supply_is_blackout
               Job (sch_decidable_eq Job) PStateL schedL t))
           (svc_target_sub svc_target_one
             (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_at
               Job (sch_decidable_eq Job) PStateL schedL t))).
  Proof.
    apply fs_imp_correspondence.
    - exact (fs_unit_supply_proc_model_correspondence
        Job PStateR PStateL R).
    - apply fs_forall_nat_correspondence. intros tR tL Ht.
      apply sub_nat_eq_correspondence.
      + exact (fs_bool_to_nat_related _ _
          (fs_is_blackout_related Job PStateR PStateL R
            schedR schedL Hsched tR tL Ht)).
      + apply svc_target_sub_related.
        * exact (sub_nat_rel_canonical (S O)).
        * exact (fs_supply_at_related Job PStateR PStateL R
            schedR schedL Hsched tR tL Ht).
  Qed.

  Lemma fs_supply_at_le_1_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.unit_supply_proc_model
        Job PStateR ->
       forall t : nat,
         is_true (leq
           (@prosa.model.processor.supply.supply_at Job PStateR schedR t)
           (S O)))
      (ImportedSbfFacts.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model
         Job (sch_decidable_eq Job) PStateL ->
       forall t : Lean.Nat,
         fs_target_le
           (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_at
             Job (sch_decidable_eq Job) PStateL schedL t)
           svc_target_one).
  Proof.
    apply fs_imp_correspondence.
    - exact (fs_unit_supply_proc_model_correspondence
        Job PStateR PStateL R).
    - apply fs_forall_nat_correspondence. intros tR tL Ht.
      exact (sub_nat_le_correspondence _ _ (S O) svc_target_one
        (fs_supply_at_related Job PStateR PStateL R
          schedR schedL Hsched tR tL Ht)
        (sub_nat_rel_canonical (S O))).
  Qed.

  Lemma fs_unit_supply_proc_service_case_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.unit_supply_proc_model
        Job PStateR ->
       forall (j : Job) (t : nat),
         Logic.eq
           (@prosa.behavior.service.service_at Job PStateR schedR j t) O
         \/ Logic.eq
           (@prosa.behavior.service.service_at Job PStateR schedR j t) (S O))
      (ImportedSbfFacts.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model
         Job (sch_decidable_eq Job) PStateL ->
       forall (j : Job) (t : Lean.Nat),
         Lean.Or
           (Lean.eq
             (ImportedSbfFacts.Prosa_Behavior_Service_service_at
               Job (sch_decidable_eq Job) PStateL schedL j t)
             svc_target_zero)
           (Lean.eq
             (ImportedSbfFacts.Prosa_Behavior_Service_service_at
               Job (sch_decidable_eq Job) PStateL schedL j t)
             svc_target_one)).
  Proof.
    apply fs_imp_correspondence.
    - exact (fs_unit_supply_proc_model_correspondence
        Job PStateR PStateL R).
    - apply fs_forall_job_correspondence. intro j.
      apply fs_forall_nat_correspondence. intros tR tL Ht.
      apply fs_or_correspondence.
      + apply sub_nat_eq_correspondence.
        * exact (fs_service_at_related Job PStateR PStateL R
            schedR schedL Hsched j tR tL Ht).
        * exact (sub_nat_rel_canonical O).
      + apply sub_nat_eq_correspondence.
        * exact (fs_service_at_related Job PStateR PStateL R
            schedR schedL Hsched j tR tL Ht).
        * exact (sub_nat_rel_canonical (S O)).
  Qed.

  Lemma fs_supply_during_bound_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.unit_supply_proc_model
        Job PStateR ->
       forall t d : nat,
         is_true (leq
           (@prosa.model.processor.supply.supply_during
             Job PStateR schedR t (t + d)) d))
      (ImportedSbfFacts.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model
         Job (sch_decidable_eq Job) PStateL ->
       forall t d : Lean.Nat,
         fs_target_le
           (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_during
             Job (sch_decidable_eq Job) PStateL schedL t
             (svc_target_add t d)) d).
  Proof.
    apply fs_imp_correspondence.
    - exact (fs_unit_supply_proc_model_correspondence
        Job PStateR PStateL R).
    - apply fs_forall_nat_correspondence. intros tR tL Ht.
      apply fs_forall_nat_correspondence. intros dR dL Hd.
      apply sub_nat_le_correspondence.
      + exact (fs_supply_during_related Job PStateR PStateL R
          schedR schedL Hsched tR (tR + dR) tL (svc_target_add tL dL)
          Ht (svc_target_add_related tR tL dR dL Ht Hd)).
      + exact Hd.
  Qed.

  Lemma fs_blackout_during_bound_correspondence :
    PropSPropRel
      (forall t d : nat,
        is_true (leq
          (@prosa.model.processor.supply.blackout_during
            Job PStateR schedR t (t + d)) d))
      (forall t d : Lean.Nat,
        fs_target_le
          (ImportedSbfFacts.Prosa_Model_Processor_Supply_blackout_during
            Job (sch_decidable_eq Job) PStateL schedL t
            (svc_target_add t d)) d).
  Proof.
    apply fs_forall_nat_correspondence. intros tR tL Ht.
    apply fs_forall_nat_correspondence. intros dR dL Hd.
    apply sub_nat_le_correspondence.
    - exact (fs_blackout_during_related Job PStateR PStateL R
        schedR schedL Hsched tR (tR + dR) tL (svc_target_add tL dL)
        Ht (svc_target_add_related tR tL dR dL Ht Hd)).
    - exact Hd.
  Qed.

  Lemma fs_supply_during_last_plus_before_correspondence :
    PropSPropRel
      (forall t1 t2 : nat,
        is_true (leq t1 t2) ->
        Logic.eq
          (@prosa.model.processor.supply.supply_during
            Job PStateR schedR t1 t2.+1)
          (@prosa.model.processor.supply.supply_during
            Job PStateR schedR t1 t2 +
           @prosa.model.processor.supply.supply_at
            Job PStateR schedR t2))
      (forall t1 t2 : Lean.Nat,
        fs_target_le t1 t2 ->
        Lean.eq
          (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_during
            Job (sch_decidable_eq Job) PStateL schedL t1
            (svc_target_add t2 svc_target_one))
          (svc_target_add
            (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_during
              Job (sch_decidable_eq Job) PStateL schedL t1 t2)
            (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_at
              Job (sch_decidable_eq Job) PStateL schedL t2))).
  Proof.
    apply fs_forall_nat_correspondence. intros t1R t1L Ht1.
    apply fs_forall_nat_correspondence. intros t2R t2L Ht2.
    apply fs_imp_correspondence.
    - exact (sub_nat_le_correspondence _ _ _ _ Ht1 Ht2).
    - apply sub_nat_eq_correspondence.
      + apply (fs_supply_during_related Job PStateR PStateL R
          schedR schedL Hsched t1R t2R.+1 t1L
          (svc_target_add t2L svc_target_one) Ht1).
        rewrite -addn1.
        exact (svc_target_add_related t2R t2L (S O) svc_target_one
          Ht2 (sub_nat_rel_canonical (S O))).
      + apply svc_target_add_related.
        * exact (fs_supply_during_related Job PStateR PStateL R
            schedR schedL Hsched t1R t2R t1L t2L Ht1 Ht2).
        * exact (fs_supply_at_related Job PStateR PStateL R
            schedR schedL Hsched t2R t2L Ht2).
  Qed.

  Lemma fs_blackout_during_last_plus_before_correspondence :
    PropSPropRel
      (forall t1 t2 : nat,
        is_true (leq t1 t2) ->
        Logic.eq
          (@prosa.model.processor.supply.blackout_during
            Job PStateR schedR t1 t2.+1)
          (@prosa.model.processor.supply.blackout_during
            Job PStateR schedR t1 t2 +
           nat_of_bool (@prosa.model.processor.supply.is_blackout
             Job PStateR schedR t2)))
      (forall t1 t2 : Lean.Nat,
        fs_target_le t1 t2 ->
        Lean.eq
          (ImportedSbfFacts.Prosa_Model_Processor_Supply_blackout_during
            Job (sch_decidable_eq Job) PStateL schedL t1
            (svc_target_add t2 svc_target_one))
          (svc_target_add
            (ImportedSbfFacts.Prosa_Model_Processor_Supply_blackout_during
              Job (sch_decidable_eq Job) PStateL schedL t1 t2)
            (ImportedSbfFacts.Bool_toNat
              (ImportedSbfFacts.Prosa_Model_Processor_Supply_is_blackout
                Job (sch_decidable_eq Job) PStateL schedL t2)))).
  Proof.
    apply fs_forall_nat_correspondence. intros t1R t1L Ht1.
    apply fs_forall_nat_correspondence. intros t2R t2L Ht2.
    apply fs_imp_correspondence.
    - exact (sub_nat_le_correspondence _ _ _ _ Ht1 Ht2).
    - apply sub_nat_eq_correspondence.
      + apply (fs_blackout_during_related Job PStateR PStateL R
          schedR schedL Hsched t1R t2R.+1 t1L
          (svc_target_add t2L svc_target_one) Ht1).
        rewrite -addn1.
        exact (svc_target_add_related t2R t2L (S O) svc_target_one
          Ht2 (sub_nat_rel_canonical (S O))).
      + apply svc_target_add_related.
        * exact (fs_blackout_during_related Job PStateR PStateL R
            schedR schedL Hsched t1R t2R t1L t2L Ht1 Ht2).
        * exact (fs_bool_to_nat_related _ _
            (fs_is_blackout_related Job PStateR PStateL R
              schedR schedL Hsched t2R t2L Ht2)).
  Qed.

  Lemma fs_supply_during_complement_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.unit_supply_proc_model
        Job PStateR ->
       forall t d : nat,
         Logic.eq
           (@prosa.model.processor.supply.supply_during
             Job PStateR schedR t (t + d))
           (d - @prosa.model.processor.supply.blackout_during
             Job PStateR schedR t (t + d)))
      (ImportedSbfFacts.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model
         Job (sch_decidable_eq Job) PStateL ->
       forall t d : Lean.Nat,
         Lean.eq
           (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_during
             Job (sch_decidable_eq Job) PStateL schedL t
             (svc_target_add t d))
           (svc_target_sub d
             (ImportedSbfFacts.Prosa_Model_Processor_Supply_blackout_during
               Job (sch_decidable_eq Job) PStateL schedL t
               (svc_target_add t d)))).
  Proof.
    apply fs_imp_correspondence.
    - exact (fs_unit_supply_proc_model_correspondence
        Job PStateR PStateL R).
    - apply fs_forall_nat_correspondence. intros tR tL Ht.
      apply fs_forall_nat_correspondence. intros dR dL Hd.
      apply sub_nat_eq_correspondence.
      + exact (fs_supply_during_related Job PStateR PStateL R
          schedR schedL Hsched tR (tR + dR) tL (svc_target_add tL dL)
          Ht (svc_target_add_related tR tL dR dL Ht Hd)).
      + apply svc_target_sub_related; first exact Hd.
        exact (fs_blackout_during_related Job PStateR PStateL R
          schedR schedL Hsched tR (tR + dR) tL (svc_target_add tL dL)
          Ht (svc_target_add_related tR tL dR dL Ht Hd)).
  Qed.

  Lemma fs_blackout_during_complement_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.unit_supply_proc_model
        Job PStateR ->
       forall t d : nat,
         Logic.eq
           (@prosa.model.processor.supply.blackout_during
             Job PStateR schedR t (t + d))
           (d - @prosa.model.processor.supply.supply_during
             Job PStateR schedR t (t + d)))
      (ImportedSbfFacts.Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model
         Job (sch_decidable_eq Job) PStateL ->
       forall t d : Lean.Nat,
         Lean.eq
           (ImportedSbfFacts.Prosa_Model_Processor_Supply_blackout_during
             Job (sch_decidable_eq Job) PStateL schedL t
             (svc_target_add t d))
           (svc_target_sub d
             (ImportedSbfFacts.Prosa_Model_Processor_Supply_supply_during
               Job (sch_decidable_eq Job) PStateL schedL t
               (svc_target_add t d)))).
  Proof.
    apply fs_imp_correspondence.
    - exact (fs_unit_supply_proc_model_correspondence
        Job PStateR PStateL R).
    - apply fs_forall_nat_correspondence. intros tR tL Ht.
      apply fs_forall_nat_correspondence. intros dR dL Hd.
      apply sub_nat_eq_correspondence.
      + exact (fs_blackout_during_related Job PStateR PStateL R
          schedR schedL Hsched tR (tR + dR) tL (svc_target_add tL dL)
          Ht (svc_target_add_related tR tL dR dL Ht Hd)).
      + apply svc_target_sub_related; first exact Hd.
        exact (fs_supply_during_related Job PStateR PStateL R
          schedR schedL Hsched tR (tR + dR) tL (svc_target_add tL dL)
          Ht (svc_target_add_related tR tL dR dL Ht Hd)).
  Qed.

  Lemma fs_blackout_during_cat_correspondence :
    PropSPropRel
      (forall t1 t2 t : nat,
        is_true ((leq t1 t) && (leq t t2)) ->
        Logic.eq
          (@prosa.model.processor.supply.blackout_during
            Job PStateR schedR t1 t +
           @prosa.model.processor.supply.blackout_during
            Job PStateR schedR t t2)
          (@prosa.model.processor.supply.blackout_during
            Job PStateR schedR t1 t2))
      (forall t1 t2 t : Lean.Nat,
        Lean.And (fs_target_le t1 t) (fs_target_le t t2) ->
        Lean.eq
          (svc_target_add
            (ImportedSbfFacts.Prosa_Model_Processor_Supply_blackout_during
              Job (sch_decidable_eq Job) PStateL schedL t1 t)
            (ImportedSbfFacts.Prosa_Model_Processor_Supply_blackout_during
              Job (sch_decidable_eq Job) PStateL schedL t t2))
          (ImportedSbfFacts.Prosa_Model_Processor_Supply_blackout_during
            Job (sch_decidable_eq Job) PStateL schedL t1 t2)).
  Proof.
    apply fs_forall_nat_correspondence. intros t1R t1L Ht1.
    apply fs_forall_nat_correspondence. intros t2R t2L Ht2.
    apply fs_forall_nat_correspondence. intros tR tL Ht.
    apply fs_imp_correspondence.
    - exact (fs_le_chain_correspondence t1R tR t2R t1L tL t2L
        Ht1 Ht Ht2).
    - apply sub_nat_eq_correspondence.
      + apply svc_target_add_related.
        * exact (fs_blackout_during_related Job PStateR PStateL R
            schedR schedL Hsched t1R tR t1L tL Ht1 Ht).
        * exact (fs_blackout_during_related Job PStateR PStateL R
            schedR schedL Hsched tR t2R tL t2L Ht Ht2).
      + exact (fs_blackout_during_related Job PStateR PStateL R
          schedR schedL Hsched t1R t2R t1L t2L Ht1 Ht2).
  Qed.

  Lemma fs_blackout_during_unit_growth_correspondence :
    PropSPropRel
      (forall t : nat,
        prosa.util.unit_growth.unit_growth_function
          (@prosa.model.processor.supply.blackout_during
            Job PStateR schedR t))
      (forall t : Lean.Nat,
        ImportedSbfFacts.Prosa_Util_UnitGrowth_unit_growth_function
          (ImportedSbfFacts.Prosa_Model_Processor_Supply_blackout_during
            Job (sch_decidable_eq Job) PStateL schedL t)).
  Proof.
    apply fs_forall_nat_correspondence. intros tR tL Ht.
    unfold prosa.util.unit_growth.unit_growth_function.
    cbn [ImportedSbfFacts.Prosa_Util_UnitGrowth_unit_growth_function].
    apply fs_forall_nat_correspondence. intros uR uL Hu.
    apply sub_nat_le_correspondence.
    - exact (fs_blackout_during_related Job PStateR PStateL R
        schedR schedL Hsched tR (uR + (S O)) tL
        (svc_target_add uL svc_target_one) Ht
        (svc_target_add_related uR uL (S O) svc_target_one
          Hu (sub_nat_rel_canonical (S O)))).
    - apply svc_target_add_related.
      + exact (fs_blackout_during_related Job PStateR PStateL R
          schedR schedL Hsched tR uR tL uL Ht Hu).
      + exact (sub_nat_rel_canonical (S O)).
  Qed.

  Lemma fs_progress_inside_supplies_correspondence :
    PropSPropRel
      (@prosa.model.processor.platform_properties.fully_consuming_proc_model
        Job PStateR ->
       forall (j : Job) (t : nat),
         is_true (@prosa.model.processor.supply.has_supply
           Job PStateR schedR t) ->
         is_true (@prosa.behavior.service.scheduled_at
           Job PStateR schedR j t) ->
         is_true (ltn O
           (@prosa.behavior.service.service_at Job PStateR schedR j t)))
      (ImportedSbfFacts.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model
         Job (sch_decidable_eq Job) PStateL ->
       forall (j : Job) (t : Lean.Nat),
         Lean.eq
           (ImportedSbfFacts.Prosa_Model_Processor_Supply_has_supply
             Job (sch_decidable_eq Job) PStateL schedL t)
           ImportedSbfFacts.Bool_true ->
         Lean.eq
           (ImportedSbfFacts.Prosa_Behavior_Service_scheduled_at
             Job (sch_decidable_eq Job) PStateL schedL j t)
           ImportedSbfFacts.Bool_true ->
         fs_target_lt Lean.Nat_zero
           (ImportedSbfFacts.Prosa_Behavior_Service_service_at
             Job (sch_decidable_eq Job) PStateL schedL j t)).
  Proof.
    apply fs_imp_correspondence.
    - exact (fs_fully_consuming_proc_model_correspondence
        Job PStateR PStateL R).
    - apply fs_forall_job_correspondence. intro j.
      apply fs_forall_nat_correspondence. intros tR tL Ht.
      apply fs_imp_correspondence.
      + exact (svc_bool_truth_correspondence _ _
          (fs_has_supply_related Job PStateR PStateL R
            schedR schedL Hsched tR tL Ht)).
      + apply fs_imp_correspondence.
        * exact (svc_bool_truth_correspondence _ _
            (fs_scheduled_at_related Job PStateR PStateL R
              schedR schedL Hsched j tR tL Ht)).
        * exact (sub_nat_lt_correspondence O Lean.Nat_zero _ _
            (sub_nat_rel_canonical O)
            (fs_service_at_related Job PStateR PStateL R
              schedR schedL Hsched j tR tL Ht)).
  Qed.
End FactsSupplyStatements.

Print Assumptions fs_service_at_le_supply_at_correspondence.
Print Assumptions fs_pos_service_impl_pos_supply_correspondence.
Print Assumptions fs_blackout_or_supply_correspondence.
Print Assumptions fs_supply_at_complement_correspondence.
Print Assumptions fs_is_blackout_complement_correspondence.
Print Assumptions fs_supply_at_le_1_correspondence.
Print Assumptions fs_unit_supply_proc_service_case_correspondence.
Print Assumptions fs_supply_during_bound_correspondence.
Print Assumptions fs_blackout_during_bound_correspondence.
Print Assumptions fs_supply_during_last_plus_before_correspondence.
Print Assumptions fs_blackout_during_last_plus_before_correspondence.
Print Assumptions fs_supply_during_complement_correspondence.
Print Assumptions fs_blackout_during_complement_correspondence.
Print Assumptions fs_blackout_during_cat_correspondence.
Print Assumptions fs_blackout_during_unit_growth_correspondence.
Print Assumptions fs_progress_inside_supplies_correspondence.
