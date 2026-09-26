From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From prosa Require Import FactsSbfPeriodicSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsSbfPeriodic ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalSequenceBaseAdapter ArrivalSequenceOperations ArrivalSequenceCorrespondence
  SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations
  SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence
  PredCorrespondence PlainCorrespondence NatSubCorrespondence DivModCorrespondence
  PeriodicCorrespondence
  FsScheduleBaseAdapter FsScheduleFiniteOperations FsScheduleCorrespondence
  FsProcessorStateCorrespondence FactsSupplyPlatformPropertiesCorrespondence.

Module I := ImportedFactsSbfPeriodic.
Module S := FactsSbfPeriodicSemanticSource.FactsSbfPeriodicSemanticSource.

(** Statement correspondences for [analysis/facts/model/sbf/periodic.v].

    Source side: the extracted statement [S.statement_X] specialised at its
    leading job type and processor state; target side: the type of the
    imported Lean theorem at the related processor state.  Inputs: the
    processor states by the accepted full observational
    [SchProcessorStateRel].  Every later binder (arrival sequence, schedule,
    Nat parameters) is covered in both directions: schedules through the
    accepted schedule import/export certificates, arrival sequences through
    the accepted canonical conversion and its inverse below, Nats through
    [ar_forall_nat_correspondence].  [prm_sbf] and [periodic_resource_model]
    are closed by the accepted Periodic definition correspondences, the Nat
    operations by the replayed DivMod correspondence, [unit_supply_proc_model]
    by the replayed platform-properties correspondence. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** Closed Nat expressions built from [+ * -], variables and literals. *)
Ltac fsp_nat :=
  solve [ assumption
        | exact (sub_nat_rel_canonical _)
        | apply dm_add_correspondence; fsp_nat
        | apply dm_mul_correspondence; fsp_nat
        | apply dm_sub_correspondence; fsp_nat ].

(** ** Coverage combinator and conversions (proved, not assumed) *)

Lemma fsp_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
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

Definition fsp_arrival_sequence_to_source (T : eqType)
    (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence T (ar_decidable_eq T)) :
    prosa.behavior.arrival_sequence.arrival_sequence T :=
  fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

Lemma fsp_arrival_sequence_to_source_rel (T : eqType) arrL :
  ArArrivalSequenceRel T (fsp_arrival_sequence_to_source T arrL) arrL.
Proof.
  intros tR tL Ht. unfold ArListRel, fsp_arrival_sequence_to_source.
  refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
  exact (sub_imported_eq_congr arrL _ _ Ht).
Qed.

Definition fsp_supply_of_sch (Job : eqType)
    (PStateR : prosa.behavior.schedule.ProcessorState Job)
    (PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job (sch_decidable_eq Job))
    (R : SchProcessorStateRel Job PStateR PStateL) :
    SupplyProcessorStateRel Job PStateR PStateL :=
  {| supply_ps_state_rel := sch_ps_state_rel Job PStateR PStateL R;
     supply_ps_core_to_target := sch_ps_core_to_target Job PStateR PStateL R;
     supply_ps_core_enumeration_rel := sch_ps_core_enumeration_rel Job PStateR PStateL R;
     supply_ps_supply_on_rel := sch_ps_supply_on_rel Job PStateR PStateL R |}.

Lemma fsp_prm_sbf_related (periodR allocR : nat) (periodL allocL : Lean.Nat) :
  SubNatRel periodR periodL -> SubNatRel allocR allocL ->
  PredFunctionRel
    (prosa.analysis.definitions.sbf.periodic.prm_sbf periodR allocR)
    (I.Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf periodL allocL).
Proof.
  intros Hp Ha nR nL Hn.
  exact (prm_sbf_correspondence _ _ _ _ _ _ Hp Ha Hn).
Qed.

Section PeriodicFacts.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    I.Prosa_Behavior_Schedule_ProcessorState Job (sch_decidable_eq Job).
  Variable R : SchProcessorStateRel Job PStateR PStateL.

  Let SR := fsp_supply_of_sch Job PStateR PStateL R.

  (** Schedules are covered by the accepted import/export certificates. *)
  Let fsp_cover_schedule :=
    fsp_forall_cover_sprop _ _
      (SchScheduleRel Job PStateR PStateL (sch_ps_state_rel Job PStateR PStateL R))
      (import_schedule Job PStateR PStateL (sch_ps_state_to_target Job PStateR PStateL R))
      (export_schedule Job PStateR PStateL (sch_ps_state_to_source Job PStateR PStateL R))
      (schedule_import_certificate Job PStateR PStateL R)
      (schedule_export_certificate Job PStateR PStateL R).

  Let fsp_cover_arrivals :=
    fsp_forall_cover_sprop _ _ (ArArrivalSequenceRel Job)
      (ar_arrival_sequence_to_imported Job) (fsp_arrival_sequence_to_source Job)
      (ar_arrival_sequence_canonical Job) (fsp_arrival_sequence_to_source_rel Job).

  Let UNIT := fs_unit_supply_proc_model_correspondence Job PStateR PStateL R.

  Ltac fsp_model schedR schedL Hsched pR pL Hp aR aL Ha :=
    exact (periodic_resource_model_correspondence Job PStateR PStateL SR
      schedR schedL Hsched pR aR pL aL Hp Ha).

  Ltac fsp_supply schedR schedL Hsched :=
    apply (supply_during_correspondence Job PStateR PStateL SR schedR schedL Hsched);
    fsp_nat.

  (** *** prm_sbf_monotone *)
  Definition src_prm_sbf_monotone : Prop :=
    ltac:(body_of (fun s : S.statement_prm_sbf_monotone => s Job PStateR)).
  Definition tgt_prm_sbf_monotone : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_monotone
      Job (sch_decidable_eq Job) PStateL)).

  Theorem prm_sbf_monotone_correspondence :
    PropSPropRel src_prm_sbf_monotone tgt_prm_sbf_monotone.
  Proof.
    apply fsp_cover_schedule. intros schedR schedL Hsched.
    apply ar_forall_nat_correspondence. intros pR pL Hp.
    apply ar_forall_nat_correspondence. intros aR aL Ha.
    apply ar_imp_correspondence; [fsp_model schedR schedL Hsched pR pL Hp aR aL Ha|].
    exact (pred_sbf_is_monotone_correspondence _ _ (fsp_prm_sbf_related _ _ _ _ Hp Ha)).
  Qed.

  (** *** prm_sbf_unit *)
  Definition src_prm_sbf_unit : Prop :=
    ltac:(body_of (fun s : S.statement_prm_sbf_unit => s Job PStateR)).
  Definition tgt_prm_sbf_unit : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_unit
      Job (sch_decidable_eq Job) PStateL)).

  Theorem prm_sbf_unit_correspondence :
    PropSPropRel src_prm_sbf_unit tgt_prm_sbf_unit.
  Proof.
    apply fsp_cover_schedule. intros schedR schedL Hsched.
    apply ar_forall_nat_correspondence. intros pR pL Hp.
    apply ar_forall_nat_correspondence. intros aR aL Ha.
    apply ar_imp_correspondence; [fsp_model schedR schedL Hsched pR pL Hp aR aL Ha|].
    exact (pred_unit_supply_bound_function_correspondence _ _
      (fsp_prm_sbf_related _ _ _ _ Hp Ha)).
  Qed.

  (** *** prm_sbf_valid *)
  Definition src_prm_sbf_valid : Prop :=
    ltac:(body_of (fun s : S.statement_prm_sbf_valid => s Job PStateR)).
  Definition tgt_prm_sbf_valid : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_valid
      Job (sch_decidable_eq Job) PStateL)).

  Theorem prm_sbf_valid_correspondence :
    PropSPropRel src_prm_sbf_valid tgt_prm_sbf_valid.
  Proof.
    apply ar_imp_correspondence; [exact UNIT|].
    apply fsp_cover_arrivals. intros arrR arrL Harr.
    apply fsp_cover_schedule. intros schedR schedL Hsched.
    apply ar_forall_nat_correspondence. intros pR pL Hp.
    apply ar_forall_nat_correspondence. intros aR aL Ha.
    apply ar_imp_correspondence; [fsp_model schedR schedL Hsched pR pL Hp aR aL Ha|].
    exact (plain_valid_supply_bound_function_correspondence Job PStateR PStateL SR
      schedR schedL Hsched arrR arrL Harr _ _ (fsp_prm_sbf_related _ _ _ _ Hp Ha)).
  Qed.

  (** *** prm_sbf_valid_aux_1 *)
  Definition src_prm_sbf_valid_aux_1 : Prop :=
    ltac:(body_of (fun s : S.statement_prm_sbf_valid_aux_1 => s Job PStateR)).
  Definition tgt_prm_sbf_valid_aux_1 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_valid_aux_1
      Job (sch_decidable_eq Job) PStateL)).

  Theorem prm_sbf_valid_aux_1_correspondence :
    PropSPropRel src_prm_sbf_valid_aux_1 tgt_prm_sbf_valid_aux_1.
  Proof.
    apply ar_imp_correspondence; [exact UNIT|].
    apply fsp_cover_schedule. intros schedR schedL Hsched.
    apply ar_forall_nat_correspondence. intros pR pL Hp.
    apply ar_forall_nat_correspondence. intros aR aL Ha.
    apply ar_imp_correspondence; [fsp_model schedR schedL Hsched pR pL Hp aR aL Ha|].
    apply ar_forall_nat_correspondence. intros kR kL Hk.
    apply ar_forall_nat_correspondence. intros q1R q1L Hq1.
    apply ar_forall_nat_correspondence. intros q2R q2L Hq2.
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply dm_le_correspondence.
    - apply (fsp_prm_sbf_related _ _ _ _ Hp Ha). fsp_nat.
    - fsp_supply schedR schedL Hsched.
  Qed.

  (** *** prm_sbf_valid_aux_2 *)
  Definition src_prm_sbf_valid_aux_2 : Prop :=
    ltac:(body_of (fun s : S.statement_prm_sbf_valid_aux_2 => s Job PStateR)).
  Definition tgt_prm_sbf_valid_aux_2 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_valid_aux_2
      Job (sch_decidable_eq Job) PStateL)).

  Theorem prm_sbf_valid_aux_2_correspondence :
    PropSPropRel src_prm_sbf_valid_aux_2 tgt_prm_sbf_valid_aux_2.
  Proof.
    apply ar_imp_correspondence; [exact UNIT|].
    apply fsp_cover_schedule. intros schedR schedL Hsched.
    apply ar_forall_nat_correspondence. intros pR pL Hp.
    apply ar_forall_nat_correspondence. intros aR aL Ha.
    apply ar_imp_correspondence; [fsp_model schedR schedL Hsched pR pL Hp aR aL Ha|].
    apply ar_forall_nat_correspondence. intros k1R k1L Hk1.
    apply ar_forall_nat_correspondence. intros k2R k2L Hk2.
    apply ar_forall_nat_correspondence. intros q1R q1L Hq1.
    apply ar_forall_nat_correspondence. intros q2R q2L Hq2.
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply dm_le_correspondence.
    - apply (fsp_prm_sbf_related _ _ _ _ Hp Ha). fsp_nat.
    - fsp_supply schedR schedL Hsched.
  Qed.

  (** *** prm_sbf_valid_aux_21 *)
  Definition src_prm_sbf_valid_aux_21 : Prop :=
    ltac:(body_of (fun s : S.statement_prm_sbf_valid_aux_21 => s Job PStateR)).
  Definition tgt_prm_sbf_valid_aux_21 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_valid_aux_21
      Job (sch_decidable_eq Job) PStateL)).

  Theorem prm_sbf_valid_aux_21_correspondence :
    PropSPropRel src_prm_sbf_valid_aux_21 tgt_prm_sbf_valid_aux_21.
  Proof.
    apply fsp_cover_schedule. intros schedR schedL Hsched.
    apply ar_forall_nat_correspondence. intros pR pL Hp.
    apply ar_forall_nat_correspondence. intros k1R k1L Hk1.
    apply ar_forall_nat_correspondence. intros k2R k2L Hk2.
    apply ar_forall_nat_correspondence. intros q1R q1L Hq1.
    apply ar_forall_nat_correspondence. intros q2R q2L Hq2.
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply dm_eq_correspondence.
    - fsp_supply schedR schedL Hsched.
    - apply dm_add_correspondence; [apply dm_add_correspondence|];
        fsp_supply schedR schedL Hsched.
  Qed.

  (** *** prm_sbf_valid_aux_22 *)
  Definition src_prm_sbf_valid_aux_22 : Prop :=
    ltac:(body_of (fun s : S.statement_prm_sbf_valid_aux_22 => s Job PStateR)).
  Definition tgt_prm_sbf_valid_aux_22 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_valid_aux_22
      Job (sch_decidable_eq Job) PStateL)).

  Theorem prm_sbf_valid_aux_22_correspondence :
    PropSPropRel src_prm_sbf_valid_aux_22 tgt_prm_sbf_valid_aux_22.
  Proof.
    apply ar_imp_correspondence; [exact UNIT|].
    apply fsp_cover_schedule. intros schedR schedL Hsched.
    apply ar_forall_nat_correspondence. intros pR pL Hp.
    apply ar_forall_nat_correspondence. intros aR aL Ha.
    apply ar_imp_correspondence; [fsp_model schedR schedL Hsched pR pL Hp aR aL Ha|].
    apply ar_forall_nat_correspondence. intros k1R k1L Hk1.
    apply ar_forall_nat_correspondence. intros k2R k2L Hk2.
    apply ar_forall_nat_correspondence. intros q1R q1L Hq1.
    apply ar_forall_nat_correspondence. intros q2R q2L Hq2.
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply dm_le_correspondence; [fsp_nat|fsp_supply schedR schedL Hsched].
  Qed.

  (** *** prm_sbf_valid_aux_23 *)
  Definition src_prm_sbf_valid_aux_23 : Prop :=
    ltac:(body_of (fun s : S.statement_prm_sbf_valid_aux_23 => s Job PStateR)).
  Definition tgt_prm_sbf_valid_aux_23 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_valid_aux_23
      Job (sch_decidable_eq Job) PStateL)).

  Theorem prm_sbf_valid_aux_23_correspondence :
    PropSPropRel src_prm_sbf_valid_aux_23 tgt_prm_sbf_valid_aux_23.
  Proof.
    apply fsp_cover_schedule. intros schedR schedL Hsched.
    apply ar_forall_nat_correspondence. intros pR pL Hp.
    apply ar_forall_nat_correspondence. intros aR aL Ha.
    apply ar_imp_correspondence; [fsp_model schedR schedL Hsched pR pL Hp aR aL Ha|].
    apply ar_forall_nat_correspondence. intros k1R k1L Hk1.
    apply ar_forall_nat_correspondence. intros k2R k2L Hk2.
    apply ar_forall_nat_correspondence. intros q1R q1L Hq1.
    apply ar_forall_nat_correspondence. intros q2R q2L Hq2.
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply dm_le_correspondence; [fsp_nat|fsp_supply schedR schedL Hsched].
  Qed.

  (** *** prm_sbf_valid_aux_24 *)
  Definition src_prm_sbf_valid_aux_24 : Prop :=
    ltac:(body_of (fun s : S.statement_prm_sbf_valid_aux_24 => s Job PStateR)).
  Definition tgt_prm_sbf_valid_aux_24 : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_valid_aux_24
      Job (sch_decidable_eq Job) PStateL)).

  Theorem prm_sbf_valid_aux_24_correspondence :
    PropSPropRel src_prm_sbf_valid_aux_24 tgt_prm_sbf_valid_aux_24.
  Proof.
    apply ar_imp_correspondence; [exact UNIT|].
    apply fsp_cover_schedule. intros schedR schedL Hsched.
    apply ar_forall_nat_correspondence. intros pR pL Hp.
    apply ar_forall_nat_correspondence. intros aR aL Ha.
    apply ar_imp_correspondence; [fsp_model schedR schedL Hsched pR pL Hp aR aL Ha|].
    apply ar_forall_nat_correspondence. intros k1R k1L Hk1.
    apply ar_forall_nat_correspondence. intros k2R k2L Hk2.
    apply ar_forall_nat_correspondence. intros q1R q1L Hq1.
    apply ar_forall_nat_correspondence. intros q2R q2L Hq2.
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply ar_imp_correspondence; [apply dm_lt_correspondence; fsp_nat|].
    apply dm_le_correspondence; [fsp_nat|fsp_supply schedR schedL Hsched].
  Qed.
End PeriodicFacts.
