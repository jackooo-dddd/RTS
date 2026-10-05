(* Artifact-local replay of the accepted certificates/analysis_definitions_delay_propagation/
   DelayPropagationCorrespondence.v (definition sections only), re-bound to
   ImportedFactsDelayPropagation. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import analysis.definitions.delay_propagation.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsDelayPropagation ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence.

Module I := ImportedFactsDelayPropagation.

(** Correspondence certificates for [analysis/definitions/delay_propagation.v].

    Definitions: for related inputs, source and compiled Lean definitions are
    related.  The mapping functions [job1_of], [task1_of] and [job2_of] and
    the delays are inputs; functions between the same (identity) carriers are
    shared, functions into [nat] / [seq] are related pointwise.  Remarks: the
    source side is the exact elaborated type of the pinned declaration (via
    [type of], proof not referenced), the target side the imported theorem's
    type; the task set and arrival sequence binders are covered in both
    directions. *)

Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic connectives *)

Lemma dp_eq_correspondence (T : Type) (xR xL yR yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL -> PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hx) Hy).
  - intro Heq. apply strictly_inhabits.
    exact (imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hx
        (sub_imported_eq_trans _ _ _ Heq (sub_imported_eq_sym _ _ Hy)))).
Qed.

Lemma dp_iff_correspondence (P Q : Prop) (PL QL : SProp) :
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

Lemma dp_and4_correspondence (P Q R S : Prop) (PL QL RL SL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel R RL -> PropSPropRel S SL ->
  PropSPropRel [/\ P, Q, R & S] (And PL (And QL (And RL SL))).
Proof.
  intros HP HQ HR HS. apply prop_sprop_rel_intro.
  - intros [p q r s].
    exact (And_intro _ _ (prop_to_sprop _ _ HP p)
      (And_intro _ _ (prop_to_sprop _ _ HQ q)
        (And_intro _ _ (prop_to_sprop _ _ HR r) (prop_to_sprop _ _ HS s)))).
  - intro H. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ HP (I.And_left _ _ H)).
    + exact (sprop_to_prop _ _ HQ (I.And_left _ _ (I.And_right _ _ H))).
    + exact (sprop_to_prop _ _ HR (I.And_left _ _ (I.And_right _ _ (I.And_right _ _ H)))).
    + exact (sprop_to_prop _ _ HS (I.And_right _ _ (I.And_right _ _ (I.And_right _ _ H)))).
Qed.

Lemma dp_mem_truth (T : eqType) (x : T) xsR xsL :
  ArListRel xsR xsL ->
  PropSPropRel (is_true (x \in xsR)) (Lean.eq (ar_target_decide_mem T x xsL) I.Bool_true).
Proof. intro H. exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related T x xsR xsL H)). Qed.

(** Nat [==] versus [decide (_ = _)] (same proof as the accepted service
    certificates' [svc_decide_eq_related]). *)
Lemma dp_decide_eq_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  ArBoolRel (aR == bR) (I.Decidable_decide (Lean.eq aL bL) (I.instDecidableEqNat aL bL)).
Proof.
  intros Ha Hb. apply ar_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - intro Heq. apply (prop_to_sprop _ _ (sub_nat_eq_correspondence aR aL bR bL Ha Hb)).
    by move/eqP: Heq.
  - intro Heq. apply strictly_inhabits. apply/eqP.
    exact (sprop_to_prop _ _ (sub_nat_eq_correspondence aR aL bR bL Ha Hb) Heq).
Qed.

(** [flatten (map f s)] versus [List.flatten (List.map f s)]. *)
Lemma dp_flatten_map_canonical (A B : Type) (fR : A -> seq B) (fL : A -> I.List B) :
  (forall x, ArListRel (fR x) (fL x)) ->
  forall xs : seq A,
    ArListRel (flatten [seq fR x | x <- xs])
      (I.List_flatten B (I.List_map A (I.List B) fL (ar_list_to_imported xs))).
Proof.
  intros Hf xs. induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - exact (ar_append_related _ _ _ _ _ (Hf x) IH).
Qed.

Lemma dp_flatten_map_related (A B : Type) (fR : A -> seq B) (fL : A -> I.List B) xsR xsL :
  (forall x, ArListRel (fR x) (fL x)) -> ArListRel xsR xsL ->
  ArListRel (flatten [seq fR x | x <- xsR])
    (I.List_flatten B (I.List_map A (I.List B) fL xsL)).
Proof.
  intros Hf Hxs.
  refine (ari_lean_transport (fun l => ArListRel _ (I.List_flatten B (I.List_map A (I.List B) fL l))) _ _ Hxs _).
  exact (dp_flatten_map_canonical A B fR fL Hf xsR).
Qed.

(** Two-way coverage of task sets and arrival sequences. *)
Lemma dp_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xR xL, ArListRel xR xL -> PropSPropRel (PR xR) (PL xL)) ->
  PropSPropRel (forall xR, PR xR) (forall xL, PL xL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR xL. exact (prop_to_sprop _ _ (H _ _ (ar_list_target_roundtrip xL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro xR.
    exact (sprop_to_prop _ _ (H xR (ar_list_to_imported xR) (@Lean.eq_refl _ _)) (HL _)).
Qed.

Definition dp_arrival_sequence_to_source (Job : eqType)
    (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job)) :
    prosa.behavior.arrival_sequence.arrival_sequence Job :=
  fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

Lemma dp_arrival_sequence_to_source_rel (Job : eqType) arrL :
  ArArrivalSequenceRel Job (dp_arrival_sequence_to_source Job arrL) arrL.
Proof.
  intros tR tL Ht. unfold ArListRel, dp_arrival_sequence_to_source.
  refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
  exact (sub_imported_eq_congr arrL _ _ Ht).
Qed.

Lemma dp_forall_arrival_sequence (Job : eqType)
    (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
    (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job) -> SProp) :
  (forall arrR arrL, ArArrivalSequenceRel Job arrR arrL -> PropSPropRel (PR arrR) (PL arrL)) ->
  PropSPropRel (forall arrR, PR arrR) (forall arrL, PL arrL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR arrL.
    exact (prop_to_sprop _ _ (H _ _ (dp_arrival_sequence_to_source_rel Job arrL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro arrR.
    exact (sprop_to_prop _ _ (H _ _ (ar_arrival_sequence_canonical Job arrR)) (HL _)).
Qed.

(** ** Delay propagation *)

Section Propagation.
  Context (Task1 Task2 Job1 Job2 : eqType).
  Let dT1 := ar_decidable_eq Task1.
  Let dT2 := ar_decidable_eq Task2.
  Let dJ1 := ar_decidable_eq Job1.
  Let dJ2 := ar_decidable_eq Job2.
  Variable jt1R : prosa.model.task.concept.JobTask Job1 Task1.
  Variable jt1L : I.Prosa_Model_Task_Concept_JobTask Job1 dJ1 Task1 dT1.
  Hypothesis Hjt1 : forall j : Job1,
    Lean.eq (@prosa.model.task.concept.job_task Job1 Task1 jt1R j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job1 dJ1 Task1 dT1 jt1L j).
  Variable jt2R : prosa.model.task.concept.JobTask Job2 Task2.
  Variable jt2L : I.Prosa_Model_Task_Concept_JobTask Job2 dJ2 Task2 dT2.
  Hypothesis Hjt2 : forall j : Job2,
    Lean.eq (@prosa.model.task.concept.job_task Job2 Task2 jt2R j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job2 dJ2 Task2 dT2 jt2L j).
  Variable ja1R : prosa.behavior.job.JobArrival Job1.
  Variable ja1L : I.Prosa_Behavior_Job_JobArrival Job1 dJ1.
  Hypothesis Hja1 : ArJobArrivalRel Job1 ja1R ja1L.
  Variable ja2R : prosa.behavior.job.JobArrival Job2.
  Variable ja2L : I.Prosa_Behavior_Job_JobArrival Job2 dJ2.
  Hypothesis Hja2 : ArJobArrivalRel Job2 ja2R ja2L.
  Variable job1_of : Job2 -> Job1.
  Variable task1_of : Task2 -> Task1.
  Variable dbR : Task2 -> nat.
  Variable dbL : Task2 -> Lean.Nat.
  Hypothesis Hdb : forall tsk, SubNatRel (dbR tsk) (dbL tsk).

  Let JT2 j := @prosa.model.task.concept.job_task Job2 Task2 jt2R j.
  Let JT2L j := I.Prosa_Model_Task_Concept_JobTask_job_task Job2 dJ2 Task2 dT2 jt2L j.

  Lemma dp_db_job_task (j : Job2) : SubNatRel (dbR (JT2 j)) (dbL (JT2L j)).
  Proof. exact (ari_lean_transport (fun v => SubNatRel (dbR (JT2 j)) (dbL v)) _ _ (Hjt2 j) (Hdb _)). Qed.

  Lemma dp_task_mem (j : Job2) tsR tsL :
    ArListRel tsR tsL ->
    PropSPropRel (is_true (JT2 j \in tsR))
      (Lean.eq (ar_target_decide_mem Task2 (JT2L j) tsL) I.Bool_true).
  Proof.
    intro Hts.
    refine (let H := dp_mem_truth Task2 (JT2 j) _ _ Hts in _).
    have E := imported_eq_to_coq_eq _ _ (Hjt2 j).
    unfold JT2L. rewrite -E. exact H.
  Qed.

  Theorem valid_delay_propagation_mapping_correspondence tsR tsL :
    ArListRel tsR tsL ->
    PropSPropRel
      (@prosa.analysis.definitions.delay_propagation.valid_delay_propagation_mapping
        Task1 Task2 Job1 Job2 jt1R jt2R ja1R ja2R job1_of task1_of dbR tsR)
      (I.Prosa_Analysis_Definitions_DelayPropagation_valid_delay_propagation_mapping
        Task1 Task2 dT1 dT2 Job1 Job2 dJ1 dJ2 jt1L jt2L ja1L ja2L job1_of task1_of dbL tsL).
  Proof.
    intro Hts.
    unfold prosa.analysis.definitions.delay_propagation.valid_delay_propagation_mapping.
    cbn [I.Prosa_Analysis_Definitions_DelayPropagation_valid_delay_propagation_mapping].
    apply ar_and_correspondence.
    - apply ar_forall_identity_correspondence => j2.
      exact (dp_eq_correspondence Task1 _ _ _ _ (Hjt1 (job1_of j2))
        (sub_imported_eq_congr task1_of _ _ (Hjt2 j2))).
    - apply ar_forall_identity_correspondence => j2.
      apply ar_imp_correspondence; [exact (dp_task_mem j2 _ _ Hts)|].
      exact (sub_nat_le_correspondence _ _ _ _ (Hja2 j2)
        (sub_add_correspondence _ _ _ _ (Hja1 (job1_of j2)) (dp_db_job_task j2))).
  Qed.

  Variable arr1R : prosa.behavior.arrival_sequence.arrival_sequence Job1.
  Variable arr1L : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job1 dJ1.
  Hypothesis Harr1 : ArArrivalSequenceRel Job1 arr1R arr1L.
  Variable job2_ofR : Job1 -> seq Job2.
  Variable job2_ofL : Job1 -> I.List Job2.
  Hypothesis Hj2 : forall j, ArListRel (job2_ofR j) (job2_ofL j).
  Variable adR : Job2 -> nat.
  Variable adL : Job2 -> Lean.Nat.
  Hypothesis Had : forall j, SubNatRel (adR j) (adL j).

  Theorem propagated_arrival_sequence_correspondence tR tL :
    SubNatRel tR tL ->
    ArListRel
      (@prosa.analysis.definitions.delay_propagation.propagated_arrival_sequence
        Job1 Job2 ja1R job1_of arr1R job2_ofR adR tR)
      (I.Prosa_Analysis_Definitions_DelayPropagation_propagated_arrival_sequence
        Job1 Job2 dJ1 dJ2 ja1L job1_of arr1L job2_ofL adL tL).
  Proof.
    intro Ht.
    unfold prosa.analysis.definitions.delay_propagation.propagated_arrival_sequence.
    cbn [I.Prosa_Analysis_Definitions_DelayPropagation_propagated_arrival_sequence].
    apply ar_filter_related.
    - intro j2. exact (dp_decide_eq_related _ _ _ _
        (sub_add_correspondence _ _ _ _ (Hja1 (job1_of j2)) (Had j2)) Ht).
    - exact (dp_flatten_map_related Job1 Job2 _ _ _ _ Hj2
        (arrivals_up_to_correspondence_certificate Job1 arr1R arr1L Harr1 _ _ Ht)).
  Qed.

  Theorem job_mapping_uniq_correspondence :
    PropSPropRel
      (@prosa.analysis.definitions.delay_propagation.job_mapping_uniq Job1 Job2 arr1R job2_ofR)
      (I.Prosa_Analysis_Definitions_DelayPropagation_job_mapping_uniq Job1 Job2 dJ1 dJ2 arr1L job2_ofL).
  Proof.
    unfold prosa.analysis.definitions.delay_propagation.job_mapping_uniq.
    cbn [I.Prosa_Analysis_Definitions_DelayPropagation_job_mapping_uniq].
    apply ar_forall_identity_correspondence => j1.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job1 arr1R arr1L j1 Harr1)|].
    exact (ar_uniq_correspondence Job2 _ _ (Hj2 j1)).
  Qed.

  Theorem valid_arr_seq_propagation_mapping_correspondence tsR tsL :
    ArListRel tsR tsL ->
    PropSPropRel
      (@prosa.analysis.definitions.delay_propagation.valid_arr_seq_propagation_mapping
        Task2 Job1 Job2 jt2R ja1R ja2R job1_of dbR arr1R job2_ofR adR tsR)
      (I.Prosa_Analysis_Definitions_DelayPropagation_valid_arr_seq_propagation_mapping
        Task2 dT2 Job1 Job2 dJ1 dJ2 jt2L ja1L ja2L job1_of dbL arr1L job2_ofL adL tsL).
  Proof.
    intro Hts.
    unfold prosa.analysis.definitions.delay_propagation.valid_arr_seq_propagation_mapping.
    cbn [I.Prosa_Analysis_Definitions_DelayPropagation_valid_arr_seq_propagation_mapping].
    apply dp_and4_correspondence.
    - apply ar_forall_identity_correspondence => j1.
      apply ar_forall_identity_correspondence => j2.
      apply dp_iff_correspondence.
      + exact (dp_mem_truth Job2 j2 _ _ (Hj2 j1)).
      + exact (dp_eq_correspondence Job1 _ _ _ _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _)).
    - exact job_mapping_uniq_correspondence.
    - apply ar_forall_identity_correspondence => j2.
      apply ar_imp_correspondence; [exact (dp_task_mem j2 _ _ Hts)|].
      apply ar_imp_correspondence;
        [exact (arrives_in_correspondence_certificate Job1 arr1R arr1L (job1_of j2) Harr1)|].
      exact (sub_nat_le_correspondence _ _ _ _ (Had j2) (dp_db_job_task j2)).
    - apply ar_forall_identity_correspondence => j2.
      exact (sub_nat_eq_correspondence _ _ _ _ (Hja2 j2)
        (sub_add_correspondence _ _ _ _ (Hja1 (job1_of j2)) (Had j2))).
  Qed.
End Propagation.

(* The release-jitter section of the accepted certificate is not replayed here:
   its two remarks are not part of this artifact's export. *)
