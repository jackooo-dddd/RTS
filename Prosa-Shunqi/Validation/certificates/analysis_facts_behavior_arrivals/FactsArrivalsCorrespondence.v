From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path
  fintype bigop.
From prosa Require Import FactsArrivalsSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsArrivals ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedFactsArrivals.
Module S := FactsArrivalsSemanticSource.FactsArrivalsSemanticSource.

(** Statement correspondences for [analysis/facts/behavior/arrivals.v].

    Source side: the extracted statement [S.statement_X] (bound to the
    authoritative elaborated type) specialised at the input binders.
    Target side: the type of the imported Lean theorem [I.X] instantiated at
    the related inputs; computing it with [type of] makes the target
    proposition exactly the imported theorem's type (exact-type guard by
    construction).  The proofs use only operation correspondences and never
    the source or imported theorems. *)

(** [body_of (fun s : S.statement_X => s inputs)] is the source statement
    specialised at the inputs; [type_of_term t] is the type of [t]. *)
Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Generic combinators *)

Lemma fa_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [Hpq Hqp]. apply I.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ (Hpq (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP (Hqp (sprop_to_prop _ _ HQ q))).
  - intros [Hpq Hqp]. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ (Hpq (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP (Hqp (prop_to_sprop _ _ HQ q))).
Qed.

Lemma fa_le_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (I.LE_le_inst1 Lean.Nat I.instLENat aL bL).
Proof. exact (sub_nat_le_correspondence aR aL bR bL). Qed.

Lemma fa_lt_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (I.LT_lt_inst1 Lean.Nat I.instLTNat aL bL).
Proof. exact (sub_nat_lt_correspondence aR aL bR bL). Qed.

Lemma fa_range_related aR aL bR bL cR cL :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel cR cL ->
  PropSPropRel (is_true (leq aR bR && ltn bR cR))
    (Lean.eq (I.Bool_and (ar_target_decide_le aL bL) (ar_target_decide_lt bL cL))
      I.Bool_true).
Proof.
  intros Ha Hb Hc. apply ar_bool_truth_correspondence.
  exact (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ha Hb)
    (ar_decide_lt_related _ _ _ _ Hb Hc)).
Qed.

Lemma fa_mem_truth (T : eqType) (x : T) (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL ->
  PropSPropRel (is_true (x \in xsR)) (Lean.eq (ar_target_decide_mem T x xsL) I.Bool_true).
Proof. intro H. exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related T x xsR xsL H)). Qed.

(** ** Arrival predicates (inputs: Job, JobArrival) *)

Section ArrivalPredicates.
  Context (Job : eqType).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job (ar_decidable_eq Job).
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

  Definition src_arrived_between_before : Prop :=
    ltac:(body_of (fun s : S.statement_arrived_between_before => s Job jaR)).
  Definition tgt_arrived_between_before : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrived_between_before
      Job (ar_decidable_eq Job) jaL)).
  Theorem arrived_between_before_correspondence :
    PropSPropRel src_arrived_between_before tgt_arrived_between_before.
  Proof.
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence.
    - exact (ar_bool_truth_correspondence _ _
        (arrived_between_correspondence_certificate Job jaR jaL j Hja _ _ _ _ H1 H2)).
    - exact (ar_bool_truth_correspondence _ _
        (arrived_before_correspondence_certificate Job jaR jaL j Hja _ _ H2)).
  Qed.

  Definition src_arrived_before_has_arrived : Prop :=
    ltac:(body_of (fun s : S.statement_arrived_before_has_arrived => s Job jaR)).
  Definition tgt_arrived_before_has_arrived : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrived_before_has_arrived
      Job (ar_decidable_eq Job) jaL)).
  Theorem arrived_before_has_arrived_correspondence :
    PropSPropRel src_arrived_before_has_arrived tgt_arrived_before_has_arrived.
  Proof.
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence.
    - exact (ar_bool_truth_correspondence _ _
        (arrived_before_correspondence_certificate Job jaR jaL j Hja _ _ Ht)).
    - exact (ar_bool_truth_correspondence _ _
        (has_arrived_correspondence_certificate Job jaR jaL j Hja _ _ Ht)).
  Qed.

  (** [arr_seq] is bound after the class parameters but before any
      hypothesis; it is quantified inside the statement and covered in both
      directions. *)
  Definition fa_arrival_sequence_to_source
      (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job)) :
      prosa.behavior.arrival_sequence.arrival_sequence Job :=
    fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

  Lemma fa_arrival_sequence_to_source_rel arrL :
    ArArrivalSequenceRel Job (fa_arrival_sequence_to_source arrL) arrL.
  Proof.
    intros tR tL Ht. unfold ArListRel, fa_arrival_sequence_to_source.
    refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
    exact (sub_imported_eq_congr arrL _ _ Ht).
  Qed.

  Lemma fa_forall_arrival_sequence
      (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
      (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job) -> SProp) :
    (forall arrR arrL, ArArrivalSequenceRel Job arrR arrL -> PropSPropRel (PR arrR) (PL arrL)) ->
    PropSPropRel (forall arrR, PR arrR) (forall arrL, PL arrL).
  Proof.
    intro H. apply prop_sprop_rel_intro.
    - intros HR arrL. exact (prop_to_sprop _ _ (H _ _ (fa_arrival_sequence_to_source_rel arrL))
        (HR (fa_arrival_sequence_to_source arrL))).
    - intro HL. apply strictly_inhabits. intro arrR.
      exact (sprop_to_prop _ _ (H _ _ (ar_arrival_sequence_canonical Job arrR))
        (HL (ar_arrival_sequence_to_imported Job arrR))).
  Qed.

  Definition src_consistent_times_valid_arrival : Prop :=
    ltac:(body_of (fun s : S.statement_consistent_times_valid_arrival => s Job jaR)).
  Definition tgt_consistent_times_valid_arrival : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_consistent_times_valid_arrival
      Job (ar_decidable_eq Job) jaL)).
  Theorem consistent_times_valid_arrival_correspondence :
    PropSPropRel src_consistent_times_valid_arrival tgt_consistent_times_valid_arrival.
  Proof.
    apply fa_forall_arrival_sequence => arrR arrL Harr.
    apply ar_imp_correspondence.
    - exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    - exact (consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
  Qed.

  Definition src_uniq_valid_arrival : Prop :=
    ltac:(body_of (fun s : S.statement_uniq_valid_arrival => s Job jaR)).
  Definition tgt_uniq_valid_arrival : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_uniq_valid_arrival
      Job (ar_decidable_eq Job) jaL)).
  Theorem uniq_valid_arrival_correspondence :
    PropSPropRel src_uniq_valid_arrival tgt_uniq_valid_arrival.
  Proof.
    apply fa_forall_arrival_sequence => arrR arrL Harr.
    apply ar_imp_correspondence.
    - exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    - exact (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr).
  Qed.
End ArrivalPredicates.

(** ** Arrival-sequence prefixes (inputs: Job) *)

Section Prefix.
  Context (Job : eqType).
  Let AS := fa_forall_arrival_sequence Job.

  Lemma fa_forall_pred (PR : (Job -> bool) -> Prop) (PL : (Job -> I.Bool) -> SProp) :
    (forall pR pL, ArPredRel pR pL -> PropSPropRel (PR pR) (PL pL)) ->
    PropSPropRel (forall pR, PR pR) (forall pL, PL pL).
  Proof.
    intro H. apply prop_sprop_rel_intro.
    - intros HR pL.
      have Hp : ArPredRel (fun x => ar_bool_to_rocq (pL x)) pL :=
        fun x => ar_bool_target_roundtrip (pL x).
      exact (prop_to_sprop _ _ (H _ _ Hp) (HR _)).
    - intro HL. apply strictly_inhabits. intro pR.
      exact (sprop_to_prop _ _ (H _ _ (ar_pred_canonical pR)) (HL _)).
  Qed.

  Lemma fa_nil_related : ArListRel (@nil Job) (I.List_nil Job).
  Proof. exact (@Lean.eq_refl _ _). Qed.

  Definition src_arrivals_between_cat : Prop :=
    ltac:(body_of (fun s : S.statement_arrivals_between_cat => s Job)).
  Definition tgt_arrivals_between_cat : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_cat
      Job (ar_decidable_eq Job))).
  Theorem arrivals_between_cat_correspondence :
    PropSPropRel src_arrivals_between_cat tgt_arrivals_between_cat.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (fa_le_related _ _ _ _ H1 Ht)|].
    apply ar_imp_correspondence; [exact (fa_le_related _ _ _ _ Ht H2)|].
    exact (ar_list_eq_correspondence _ _ _ _ _
      (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2)
      (ar_append_related _ _ _ _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 Ht)
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht H2))).
  Qed.

  Definition src_arrivals_P_cat : Prop :=
    ltac:(body_of (fun s : S.statement_arrivals_P_cat => s Job)).
  Definition tgt_arrivals_P_cat : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_P_cat
      Job (ar_decidable_eq Job))).
  Theorem arrivals_P_cat_correspondence :
    PropSPropRel src_arrivals_P_cat tgt_arrivals_P_cat.
  Proof.
    apply AS => arrR arrL Harr.
    apply fa_forall_pred => PR PL HP.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (fa_range_related _ _ _ _ _ _ H1 Ht H2)|].
    exact (ar_list_eq_correspondence _ _ _ _ _
      (arrivals_between_P_correspondence_certificate Job arrR arrL PR PL Harr HP _ _ _ _ H1 H2)
      (ar_append_related _ _ _ _ _
        (arrivals_between_P_correspondence_certificate Job arrR arrL PR PL Harr HP _ _ _ _ H1 Ht)
        (arrivals_between_P_correspondence_certificate Job arrR arrL PR PL Harr HP _ _ _ _ Ht H2))).
  Qed.

  Definition src_arrivals_between_mem_cat : Prop :=
    ltac:(body_of (fun s : S.statement_arrivals_between_mem_cat => s Job)).
  Definition tgt_arrivals_between_mem_cat : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_mem_cat
      Job (ar_decidable_eq Job))).
  Theorem arrivals_between_mem_cat_correspondence :
    PropSPropRel src_arrivals_between_mem_cat tgt_arrivals_between_mem_cat.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (fa_le_related _ _ _ _ H1 Ht)|].
    apply ar_imp_correspondence; [exact (fa_le_related _ _ _ _ Ht H2)|].
    exact (ar_bool_eq_correspondence _ _ _ _
      (ar_decide_mem_related Job j _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2))
      (ar_decide_mem_related Job j _ _
        (ar_append_related _ _ _ _ _
          (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 Ht)
          (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht H2)))).
  Qed.

  Definition src_arrivals_between_sub : Prop :=
    ltac:(body_of (fun s : S.statement_arrivals_between_sub => s Job)).
  Definition tgt_arrivals_between_sub : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_sub
      Job (ar_decidable_eq Job))).
  Theorem arrivals_between_sub_correspondence :
    PropSPropRel src_arrivals_between_sub tgt_arrivals_between_sub.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t1'R t1'L H1'.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_nat_correspondence => t2'R t2'L H2'.
    apply ar_imp_correspondence; [exact (fa_le_related _ _ _ _ H1' H1)|].
    apply ar_imp_correspondence; [exact (fa_le_related _ _ _ _ H2 H2')|].
    apply ar_imp_correspondence.
    - exact (fa_mem_truth Job j _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2)).
    - exact (fa_mem_truth Job j _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1' H2')).
  Qed.

  Definition src_in_arrivals_implies_arrived : Prop :=
    ltac:(body_of (fun s : S.statement_in_arrivals_implies_arrived => s Job)).
  Definition tgt_in_arrivals_implies_arrived : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_in_arrivals_implies_arrived
      Job (ar_decidable_eq Job))).
  Theorem in_arrivals_implies_arrived_correspondence :
    PropSPropRel src_in_arrivals_implies_arrived tgt_in_arrivals_implies_arrived.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence.
    - exact (fa_mem_truth Job j _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2)).
    - exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
  Qed.

  Definition src_in_arrseq_implies_arrives : Prop :=
    ltac:(body_of (fun s : S.statement_in_arrseq_implies_arrives => s Job)).
  Definition tgt_in_arrseq_implies_arrives : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_in_arrseq_implies_arrives
      Job (ar_decidable_eq Job))).
  Theorem in_arrseq_implies_arrives_correspondence :
    PropSPropRel src_in_arrseq_implies_arrives tgt_in_arrseq_implies_arrives.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence.
    - exact (fa_mem_truth Job j _ _ (Harr tR tL Ht)).
    - exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
  Qed.

  Definition src_arrivals_between_geq : Prop :=
    ltac:(body_of (fun s : S.statement_arrivals_between_geq => s Job)).
  Definition tgt_arrivals_between_geq : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_geq
      Job (ar_decidable_eq Job))).
  Theorem arrivals_between_geq_correspondence :
    PropSPropRel src_arrivals_between_geq tgt_arrivals_between_geq.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (fa_le_related _ _ _ _ H2 H1)|].
    exact (ar_list_eq_correspondence _ _ _ _ _
      (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2)
      fa_nil_related).
  Qed.

  Definition src_arrivals_between_nonempty : Prop :=
    ltac:(body_of (fun s : S.statement_arrivals_between_nonempty => s Job)).
  Definition tgt_arrivals_between_nonempty : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_nonempty
      Job (ar_decidable_eq Job))).
  Theorem arrivals_between_nonempty_correspondence :
    PropSPropRel src_arrivals_between_nonempty tgt_arrivals_between_nonempty.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence.
    - exact (fa_mem_truth Job j _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2)).
    - exact (fa_lt_related _ _ _ _ H1 H2).
  Qed.
End Prefix.

(** ** New bridge: mathcomp [sorted] (adjacent pairs) ↔ Lean [List.IsChain] *)

Inductive FaSUnit : SProp := fa_sunit.

Definition fa_ischain_head {A : Type} (R : A -> A -> SProp) (l : I.List A) : SProp :=
  match l with
  | I.List_cons x (I.List_cons y _) => R x y
  | _ => FaSUnit
  end.

Definition fa_ischain_tail {A : Type} (R : A -> A -> SProp) (l : I.List A) : SProp :=
  match l with
  | I.List_cons _ ((I.List_cons _ _) as rest) => I.List_IsChain A R rest
  | _ => FaSUnit
  end.

Lemma fa_ischain_inv_head {A : Type} (R : A -> A -> SProp) (l : I.List A) :
  I.List_IsChain A R l -> fa_ischain_head R l.
Proof. intro H. destruct H as [|a|a b l hr h]; [exact fa_sunit|exact fa_sunit|exact hr]. Qed.

Lemma fa_ischain_inv_tail {A : Type} (R : A -> A -> SProp) (l : I.List A) :
  I.List_IsChain A R l -> fa_ischain_tail R l.
Proof. intro H. destruct H as [|a|a b l hr h]; [exact fa_sunit|exact fa_sunit|exact h]. Qed.

Lemma fa_path_ischain (A : Type) (rR : A -> A -> bool) (rL : A -> A -> I.Bool)
    (Hr : forall x y, ArBoolRel (rR x y) (rL x y)) :
  forall (xs : seq A) (x : A),
    PropSPropRel (is_true (path rR x xs))
      (I.List_IsChain A (fun a b => Lean.eq (rL a b) I.Bool_true) (ar_list_to_imported (x :: xs))).
Proof.
  induction xs as [|y ys IH]; intro x.
  - apply prop_sprop_rel_intro.
    + intros _. exact (I.List_IsChain_singleton A _ x).
    + intros _. apply strictly_inhabits. reflexivity.
  - have Hxy := ar_bool_truth_correspondence _ _ (Hr x y).
    have Hrest := IH y.
    apply prop_sprop_rel_intro.
    + intro H.
      have Hand : rR x y /\ path rR y ys := elimT andP H.
      exact (I.List_IsChain_cons_cons A _ x y (ar_list_to_imported ys)
        (prop_to_sprop _ _ Hxy (proj1 Hand)) (prop_to_sprop _ _ Hrest (proj2 Hand))).
    + intro H. apply strictly_inhabits. cbn [path]. apply/andP. split.
      * exact (sprop_to_prop _ _ Hxy (fa_ischain_inv_head _ _ H)).
      * exact (sprop_to_prop _ _ Hrest (fa_ischain_inv_tail _ _ H)).
Qed.

Lemma fa_sorted_ischain (A : Type) (rR : A -> A -> bool) (rL : A -> A -> I.Bool)
    (Hr : forall x y, ArBoolRel (rR x y) (rL x y)) (xsR : seq A) (xsL : I.List A) :
  ArListRel xsR xsL ->
  PropSPropRel (is_true (sorted rR xsR))
    (I.List_IsChain A (fun a b => Lean.eq (rL a b) I.Bool_true) xsL).
Proof.
  intro Hxs. unfold ArListRel in Hxs. destruct Hxs.
  destruct xsR as [|x xs].
  - apply prop_sprop_rel_intro.
    + intros _. exact (I.List_IsChain_nil A _).
    + intros _. apply strictly_inhabits. reflexivity.
  - exact (fa_path_ischain A rR rL Hr xs x).
Qed.

(** ** Arrival times (inputs: Job, JobArrival; [arr_seq] covered) *)

Section ArrivalTimes.
  Context (Job : eqType).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job (ar_decidable_eq Job).
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Let AS := fa_forall_arrival_sequence Job.
  Let ABC := arrivals_between_correspondence_certificate Job.
  Let CAT := consistent_arrival_times_correspondence_certificate Job jaR jaL.

  Lemma fa_arrival_lt_pred (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArPredRel (fun j => ltn (@prosa.behavior.job.job_arrival Job jaR j) tR)
      (fun j => ar_target_decide_lt
        (I.Prosa_Behavior_Job_JobArrival_job_arrival Job (ar_decidable_eq Job) jaL j) tL).
  Proof. intros Ht j. exact (ar_decide_lt_related _ _ _ _ (Hja j) Ht). Qed.

  Definition by_arrival_times_correspondence (j1 j2 : Job) :
    ArBoolRel (@S.by_arrival_times Job jaR j1 j2)
      (I.Prosa_Analysis_Facts_Behavior_Arrivals_by_arrival_times Job (ar_decidable_eq Job) jaL j1 j2) :=
    ar_decide_le_related _ _ _ _ (Hja j1) (Hja j2).

  Definition src_job_arrival_arrives_at : Prop :=
    ltac:(body_of (fun s : S.statement_job_arrival_arrives_at => s Job jaR)).
  Definition tgt_job_arrival_arrives_at : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_job_arrival_arrives_at
      Job (ar_decidable_eq Job) jaL)).
  Theorem job_arrival_arrives_at_correspondence :
    PropSPropRel src_job_arrival_arrives_at tgt_job_arrival_arrives_at.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence.
    - exact (ar_bool_truth_correspondence _ _
        (arrives_at_correspondence_certificate Job arrR arrL j Harr _ _ Ht)).
    - exact (sub_nat_eq_correspondence _ _ _ _ (Hja j) Ht).
  Qed.

  Definition src_job_arrival_at : Prop :=
    ltac:(body_of (fun s : S.statement_job_arrival_at => s Job jaR)).
  Definition tgt_job_arrival_at : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_job_arrival_at
      Job (ar_decidable_eq Job) jaL)).
  Theorem job_arrival_at_correspondence :
    PropSPropRel src_job_arrival_at tgt_job_arrival_at.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence.
    - exact (fa_mem_truth Job j _ _
        (arrivals_at_correspondence_certificate Job arrR arrL Harr _ _ Ht)).
    - exact (sub_nat_eq_correspondence _ _ _ _ (Hja j) Ht).
  Qed.

  Definition src_job_in_arrivals_at : Prop :=
    ltac:(body_of (fun s : S.statement_job_in_arrivals_at => s Job jaR)).
  Definition tgt_job_in_arrivals_at : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_job_in_arrivals_at
      Job (ar_decidable_eq Job) jaL)).
  Theorem job_in_arrivals_at_correspondence :
    PropSPropRel src_job_in_arrivals_at tgt_job_in_arrivals_at.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence; [exact (sub_nat_eq_correspondence _ _ _ _ (Hja j) Ht)|].
    exact (fa_mem_truth Job j _ _ (arrivals_at_correspondence_certificate Job arrR arrL Harr _ _ Ht)).
  Qed.

  Definition src_job_arrival_between : Prop :=
    ltac:(body_of (fun s : S.statement_job_arrival_between => s Job jaR)).
  Definition tgt_job_arrival_between : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_job_arrival_between
      Job (ar_decidable_eq Job) jaL)).
  Theorem job_arrival_between_correspondence :
    PropSPropRel src_job_arrival_between tgt_job_arrival_between.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence.
    - exact (fa_mem_truth Job j _ _ (ABC arrR arrL Harr _ _ _ _ H1 H2)).
    - exact (fa_range_related _ _ _ _ _ _ H1 (Hja j) H2).
  Qed.

  Definition src_job_arrival_between_ge : Prop :=
    ltac:(body_of (fun s : S.statement_job_arrival_between_ge => s Job jaR)).
  Definition tgt_job_arrival_between_ge : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_job_arrival_between_ge
      Job (ar_decidable_eq Job) jaL)).
  Theorem job_arrival_between_ge_correspondence :
    PropSPropRel src_job_arrival_between_ge tgt_job_arrival_between_ge.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence.
    - exact (fa_mem_truth Job j _ _ (ABC arrR arrL Harr _ _ _ _ H1 H2)).
    - exact (fa_le_related _ _ _ _ H1 (Hja j)).
  Qed.

  Definition src_job_arrival_between_lt : Prop :=
    ltac:(body_of (fun s : S.statement_job_arrival_between_lt => s Job jaR)).
  Definition tgt_job_arrival_between_lt : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_job_arrival_between_lt
      Job (ar_decidable_eq Job) jaL)).
  Theorem job_arrival_between_lt_correspondence :
    PropSPropRel src_job_arrival_between_lt tgt_job_arrival_between_lt.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence.
    - exact (fa_mem_truth Job j _ _ (ABC arrR arrL Harr _ _ _ _ H1 H2)).
    - exact (fa_lt_related _ _ _ _ (Hja j) H2).
  Qed.

  Definition src_arrivals_between_filter_nil : Prop :=
    ltac:(body_of (fun s : S.statement_arrivals_between_filter_nil => s Job jaR)).
  Definition tgt_arrivals_between_filter_nil : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_filter_nil
      Job (ar_decidable_eq Job) jaL)).
  Theorem arrivals_between_filter_nil_correspondence :
    PropSPropRel src_arrivals_between_filter_nil tgt_arrivals_between_filter_nil.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence; [exact (fa_lt_related _ _ _ _ Ht H1)|].
    exact (ar_list_eq_correspondence _ _ _ _ _
      (ar_filter_related Job _ _ _ _ (fa_arrival_lt_pred _ _ Ht)
        (ABC arrR arrL Harr _ _ _ _ H1 H2))
      (fa_nil_related Job)).
  Qed.

  Definition src_arrivals_between_filter : Prop :=
    ltac:(body_of (fun s : S.statement_arrivals_between_filter => s Job jaR)).
  Definition tgt_arrivals_between_filter : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_filter
      Job (ar_decidable_eq Job) jaL)).
  Theorem arrivals_between_filter_correspondence :
    PropSPropRel src_arrivals_between_filter tgt_arrivals_between_filter.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence; [exact (fa_le_related _ _ _ _ Ht H2)|].
    exact (ar_list_eq_correspondence _ _ _ _ _
      (ABC arrR arrL Harr _ _ _ _ H1 Ht)
      (ar_filter_related Job _ _ _ _ (fa_arrival_lt_pred _ _ Ht)
        (ABC arrR arrL Harr _ _ _ _ H1 H2))).
  Qed.

  Definition src_in_arrivals_implies_arrived_between : Prop :=
    ltac:(body_of (fun s : S.statement_in_arrivals_implies_arrived_between => s Job jaR)).
  Definition tgt_in_arrivals_implies_arrived_between : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_in_arrivals_implies_arrived_between
      Job (ar_decidable_eq Job) jaL)).
  Theorem in_arrivals_implies_arrived_between_correspondence :
    PropSPropRel src_in_arrivals_implies_arrived_between tgt_in_arrivals_implies_arrived_between.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence.
    - exact (fa_mem_truth Job j _ _ (ABC arrR arrL Harr _ _ _ _ H1 H2)).
    - exact (ar_bool_truth_correspondence _ _
        (arrived_between_correspondence_certificate Job jaR jaL j Hja _ _ _ _ H1 H2)).
  Qed.

  Definition src_in_arrivals_implies_arrived_before : Prop :=
    ltac:(body_of (fun s : S.statement_in_arrivals_implies_arrived_before => s Job jaR)).
  Definition tgt_in_arrivals_implies_arrived_before : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_in_arrivals_implies_arrived_before
      Job (ar_decidable_eq Job) jaL)).
  Theorem in_arrivals_implies_arrived_before_correspondence :
    PropSPropRel src_in_arrivals_implies_arrived_before tgt_in_arrivals_implies_arrived_before.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence.
    - exact (fa_mem_truth Job j _ _
        (arrivals_before_correspondence_certificate Job arrR arrL Harr _ _ Ht)).
    - exact (ar_bool_truth_correspondence _ _
        (arrived_before_correspondence_certificate Job jaR jaL j Hja _ _ Ht)).
  Qed.

  Definition src_arrived_between_implies_in_arrivals : Prop :=
    ltac:(body_of (fun s : S.statement_arrived_between_implies_in_arrivals => s Job jaR)).
  Definition tgt_arrived_between_implies_in_arrivals : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrived_between_implies_in_arrivals
      Job (ar_decidable_eq Job) jaL)).
  Theorem arrived_between_implies_in_arrivals_correspondence :
    PropSPropRel src_arrived_between_implies_in_arrivals tgt_arrived_between_implies_in_arrivals.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence.
    - exact (ar_bool_truth_correspondence _ _
        (arrived_between_correspondence_certificate Job jaR jaL j Hja _ _ _ _ H1 H2)).
    - exact (fa_mem_truth Job j _ _ (ABC arrR arrL Harr _ _ _ _ H1 H2)).
  Qed.

  Definition src_job_arrival_between_P : Prop :=
    ltac:(body_of (fun s : S.statement_job_arrival_between_P => s Job jaR)).
  Definition tgt_job_arrival_between_P : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_job_arrival_between_P
      Job (ar_decidable_eq Job) jaL)).
  Theorem job_arrival_between_P_correspondence :
    PropSPropRel src_job_arrival_between_P tgt_job_arrival_between_P.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence => j.
    apply fa_forall_pred => PR PL HP.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence.
    - exact (fa_mem_truth Job j _ _
        (arrivals_between_P_correspondence_certificate Job arrR arrL PR PL Harr HP _ _ _ _ H1 H2)).
    - exact (fa_range_related _ _ _ _ _ _ H1 (Hja j) H2).
  Qed.

  Definition src_job_in_arrivals_between : Prop :=
    ltac:(body_of (fun s : S.statement_job_in_arrivals_between => s Job jaR)).
  Definition tgt_job_in_arrivals_between : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_job_in_arrivals_between
      Job (ar_decidable_eq Job) jaL)).
  Theorem job_in_arrivals_between_correspondence :
    PropSPropRel src_job_in_arrivals_between tgt_job_in_arrivals_between.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence; [exact (fa_le_related _ _ _ _ H1 (Hja j))|].
    apply ar_imp_correspondence; [exact (fa_lt_related _ _ _ _ (Hja j) H2)|].
    exact (fa_mem_truth Job j _ _ (ABC arrR arrL Harr _ _ _ _ H1 H2)).
  Qed.

  Definition src_arrivals_uniq : Prop :=
    ltac:(body_of (fun s : S.statement_arrivals_uniq => s Job jaR)).
  Definition tgt_arrivals_uniq : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_uniq
      Job (ar_decidable_eq Job) jaL)).
  Theorem arrivals_uniq_correspondence :
    PropSPropRel src_arrivals_uniq tgt_arrivals_uniq.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_imp_correspondence;
      [exact (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr)|].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    exact (ar_uniq_correspondence Job _ _ (ABC arrR arrL Harr _ _ _ _ H1 H2)).
  Qed.

  Definition src_arrival_lt_implies_job_in_arrivals_between_P : Prop :=
    ltac:(body_of (fun s : S.statement_arrival_lt_implies_job_in_arrivals_between_P => s Job jaR)).
  Definition tgt_arrival_lt_implies_job_in_arrivals_between_P : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrival_lt_implies_job_in_arrivals_between_P
      Job (ar_decidable_eq Job) jaL)).
  Theorem arrival_lt_implies_job_in_arrivals_between_P_correspondence :
    PropSPropRel src_arrival_lt_implies_job_in_arrivals_between_P tgt_arrival_lt_implies_job_in_arrivals_between_P.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply fa_forall_pred => PR PL HP.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    have BP := arrivals_between_P_correspondence_certificate Job arrR arrL PR PL Harr HP.
    apply ar_imp_correspondence; [exact (fa_mem_truth Job j1 _ _ (BP _ _ _ _ H1 H2))|].
    apply ar_imp_correspondence; [exact (fa_mem_truth Job j2 _ _ (BP _ _ _ _ H1 H2))|].
    apply ar_imp_correspondence; [exact (fa_lt_related _ _ _ _ (Hja j2) (Hja j1))|].
    exact (fa_mem_truth Job j2 _ _ (BP _ _ _ _ H1 (Hja j1))).
  Qed.

  Definition src_job_arrival_in_bounds : Prop :=
    ltac:(body_of (fun s : S.statement_job_arrival_in_bounds => s Job jaR)).
  Definition tgt_job_arrival_in_bounds : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_job_arrival_in_bounds
      Job (ar_decidable_eq Job) jaL)).
  Theorem job_arrival_in_bounds_correspondence :
    PropSPropRel src_job_arrival_in_bounds tgt_job_arrival_in_bounds.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply fa_iff_correspondence.
    - exact (fa_mem_truth Job j _ _ (ABC arrR arrL Harr _ _ _ _ H1 H2)).
    - apply ar_and_correspondence.
      + exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      + exact (fa_range_related _ _ _ _ _ _ H1 (Hja j) H2).
  Qed.

  Definition src_arrivals_at_sorted : Prop :=
    ltac:(body_of (fun s : S.statement_arrivals_at_sorted => s Job jaR)).
  Definition tgt_arrivals_at_sorted : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_at_sorted
      Job (ar_decidable_eq Job) jaL)).
  Theorem arrivals_at_sorted_correspondence :
    PropSPropRel src_arrivals_at_sorted tgt_arrivals_at_sorted.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_nat_correspondence => tR tL Ht.
    exact (fa_sorted_ischain Job _ _ by_arrival_times_correspondence _ _
      (arrivals_at_correspondence_certificate Job arrR arrL Harr _ _ Ht)).
  Qed.

  Definition src_arrivals_between_sorted : Prop :=
    ltac:(body_of (fun s : S.statement_arrivals_between_sorted => s Job jaR)).
  Definition tgt_arrivals_between_sorted : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_sorted
      Job (ar_decidable_eq Job) jaL)).
  Theorem arrivals_between_sorted_correspondence :
    PropSPropRel src_arrivals_between_sorted tgt_arrivals_between_sorted.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (CAT arrR arrL Hja Harr)|].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    exact (fa_sorted_ischain Job _ _ by_arrival_times_correspondence _ _
      (ABC arrR arrL Harr _ _ _ _ H1 H2)).
  Qed.
End ArrivalTimes.

(** ** Schedules (inputs: Job, a related pair of processor states) *)

Section Schedules.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job (svc_decidable_eq Job).
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job (svc_decidable_eq Job) PStateL.
  Let SR := SvcScheduleRel Job PStateR PStateL R.

  (** Two-way schedule coverage: every source schedule has a related target
      schedule and conversely.  Both are built from the processor-state
      relation's roundtrip data; no schedule property is assumed. *)
  Definition fa_sched_to_target (schedR : SchedR) : SchedL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R
      (schedR (sub_nat_to_rocq tL)).
  Definition fa_sched_to_source (schedL : SchedL) : SchedR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R
      (schedL (sub_nat_to_imported tR)).

  Lemma fa_sched_to_target_rel schedR : SR schedR (fa_sched_to_target schedR).
  Proof.
    intros tR tL Ht. unfold fa_sched_to_target.
    refine (ari_lean_transport (fun x => svc_ps_state_rel Job PStateR PStateL R (schedR tR)
      (svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq x)))) _ _ Ht _).
    refine (ari_lean_transport (fun n => svc_ps_state_rel Job PStateR PStateL R (schedR tR)
      (svc_ps_state_to_target Job PStateR PStateL R (schedR n))) _ _
      (sub_imported_eq_sym _ _ (ari_logic_eq_to_lean_eq _ _ (sub_nat_rocq_roundtrip tR))) _).
    exact (svc_ps_state_rel_canonical Job PStateR PStateL R (schedR tR)).
  Qed.

  Lemma fa_sched_to_source_rel schedL : SR (fa_sched_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. unfold fa_sched_to_source.
    refine (ari_lean_transport (fun x => svc_ps_state_rel Job PStateR PStateL R
      (svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)))
      (schedL x)) _ _ Ht _).
    exact (svc_ps_state_rel_surjective Job PStateR PStateL R (schedL (sub_nat_to_imported tR))).
  Qed.

  Lemma fa_forall_schedule (PR : SchedR -> Prop) (PL : SchedL -> SProp) :
    (forall sR sL, SR sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall sR, PR sR) (forall sL, PL sL).
  Proof.
    intro H. apply prop_sprop_rel_intro.
    - intros HR sL. exact (prop_to_sprop _ _ (H _ _ (fa_sched_to_source_rel sL)) (HR _)).
    - intro HL. apply strictly_inhabits. intro sR.
      exact (sprop_to_prop _ _ (H _ _ (fa_sched_to_target_rel sR)) (HL _)).
  Qed.

  Section Related.
    Variable schedR : SchedR.
    Variable schedL : SchedL.
    Hypothesis Hsched : SR schedR schedL.

    Lemma fa_scheduled_at_related (j : Job) tR tL :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_scheduled_at Job (svc_decidable_eq Job) PStateL schedL j tL).
    Proof.
      intro Ht. exact (svc_scheduled_in_related Job PStateR PStateL R j _ _ (Hsched tR tL Ht)).
    Qed.

    Lemma fa_scheduled_at_truth (j : Job) tR tL :
      SubNatRel tR tL ->
      PropSPropRel (is_true (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR))
        (Lean.eq (I.Prosa_Behavior_Service_scheduled_at Job (svc_decidable_eq Job)
          PStateL schedL j tL) I.Bool_true).
    Proof. intro Ht. exact (ar_bool_truth_correspondence _ _ (fa_scheduled_at_related j tR tL Ht)). Qed.

    Lemma fa_jobs_come_from_related arrR arrL :
      ArArrivalSequenceRel Job arrR arrL ->
      PropSPropRel (@prosa.behavior.ready.jobs_come_from_arrival_sequence Job PStateR schedR arrR)
        (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job (svc_decidable_eq Job)
          PStateL schedL arrL).
    Proof.
      intro Harr.
      unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
      cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence].
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (fa_scheduled_at_truth j tR tL Ht)|].
      exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    Qed.

    Lemma fa_jobs_must_arrive_related jaR jaL :
      ArJobArrivalRel Job jaR jaL ->
      PropSPropRel (@prosa.behavior.ready.jobs_must_arrive_to_execute Job jaR PStateR schedR)
        (I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job (svc_decidable_eq Job)
          jaL PStateL schedL).
    Proof.
      intro Hja.
      unfold prosa.behavior.ready.jobs_must_arrive_to_execute.
      cbn [I.Prosa_Behavior_Ready_jobs_must_arrive_to_execute].
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (fa_scheduled_at_truth j tR tL Ht)|].
      exact (ar_bool_truth_correspondence _ _
        (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
    Qed.
  End Related.

  Let AS := fa_forall_arrival_sequence Job.
  Let FS := fa_forall_schedule.

  Definition src_arrives_in_jobs_come_from_arrival_sequence : Prop :=
    ltac:(body_of (fun s : S.statement_arrives_in_jobs_come_from_arrival_sequence => s Job PStateR)).
  Definition tgt_arrives_in_jobs_come_from_arrival_sequence : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrives_in_jobs_come_from_arrival_sequence
      Job (svc_decidable_eq Job) PStateL)).
  Theorem arrives_in_jobs_come_from_arrival_sequence_correspondence :
    PropSPropRel src_arrives_in_jobs_come_from_arrival_sequence
      tgt_arrives_in_jobs_come_from_arrival_sequence.
  Proof.
    apply AS => arrR arrL Harr.
    apply FS => schedR schedL Hsched.
    apply ar_imp_correspondence; [exact (fa_jobs_come_from_related _ _ Hsched _ _ Harr)|].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence; [exact (fa_scheduled_at_truth _ _ Hsched j tR tL Ht)|].
    exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
  Qed.

  Section WithArrival.
    Variable jaR : prosa.behavior.job.JobArrival Job.
    Variable jaL : I.Prosa_Behavior_Job_JobArrival Job (ar_decidable_eq Job).
    Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

    Definition src_arrived_between_jobs_must_arrive_to_execute : Prop :=
      ltac:(body_of (fun s : S.statement_arrived_between_jobs_must_arrive_to_execute =>
        s Job jaR PStateR)).
    Definition tgt_arrived_between_jobs_must_arrive_to_execute : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrived_between_jobs_must_arrive_to_execute
        Job (svc_decidable_eq Job) jaL PStateL)).
    Theorem arrived_between_jobs_must_arrive_to_execute_correspondence :
      PropSPropRel src_arrived_between_jobs_must_arrive_to_execute
        tgt_arrived_between_jobs_must_arrive_to_execute.
    Proof.
      apply FS => schedR schedL Hsched.
      apply ar_imp_correspondence; [exact (fa_jobs_must_arrive_related _ _ Hsched _ _ Hja)|].
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (fa_scheduled_at_truth _ _ Hsched j tR tL Ht)|].
      exact (ar_bool_truth_correspondence _ _
        (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
    Qed.

    Definition src_arrivals_before_scheduled_at : Prop :=
      ltac:(body_of (fun s : S.statement_arrivals_before_scheduled_at => s Job jaR PStateR)).
    Definition tgt_arrivals_before_scheduled_at : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_before_scheduled_at
        Job (svc_decidable_eq Job) jaL PStateL)).
    Theorem arrivals_before_scheduled_at_correspondence :
      PropSPropRel src_arrivals_before_scheduled_at tgt_arrivals_before_scheduled_at.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_imp_correspondence;
        [exact (consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
      apply FS => schedR schedL Hsched.
      apply ar_imp_correspondence; [exact (fa_jobs_come_from_related _ _ Hsched _ _ Harr)|].
      apply ar_imp_correspondence; [exact (fa_jobs_must_arrive_related _ _ Hsched _ _ Hja)|].
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (fa_scheduled_at_truth _ _ Hsched j tR tL Ht)|].
      apply ar_forall_nat_correspondence => t'R t'L Ht'.
      apply ar_imp_correspondence; [exact (fa_lt_related _ _ _ _ Ht Ht')|].
      exact (fa_mem_truth Job j _ _
        (arrivals_before_correspondence_certificate Job arrR arrL Harr _ _ Ht')).
    Qed.

    Definition src_arrivals_up_to_scheduled_at : Prop :=
      ltac:(body_of (fun s : S.statement_arrivals_up_to_scheduled_at => s Job jaR PStateR)).
    Definition tgt_arrivals_up_to_scheduled_at : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_up_to_scheduled_at
        Job (svc_decidable_eq Job) jaL PStateL)).
    Theorem arrivals_up_to_scheduled_at_correspondence :
      PropSPropRel src_arrivals_up_to_scheduled_at tgt_arrivals_up_to_scheduled_at.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_imp_correspondence;
        [exact (consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
      apply FS => schedR schedL Hsched.
      apply ar_imp_correspondence; [exact (fa_jobs_come_from_related _ _ Hsched _ _ Harr)|].
      apply ar_imp_correspondence; [exact (fa_jobs_must_arrive_related _ _ Hsched _ _ Hja)|].
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (fa_scheduled_at_truth _ _ Hsched j tR tL Ht)|].
      apply ar_forall_nat_correspondence => t'R t'L Ht'.
      apply ar_imp_correspondence; [exact (fa_le_related _ _ _ _ Ht Ht')|].
      exact (fa_mem_truth Job j _ _
        (arrivals_up_to_correspondence_certificate Job arrR arrL Harr _ _ Ht')).
    Qed.
  End WithArrival.
End Schedules.

(** ** Arrived jobs (inputs: Job, related processor states, schedule, cost,
    arrival and readiness instances).  The readiness relation relates only the
    [job_ready] data field, over every related pair of schedules; the
    [ready_implies_pending] law field of either side is never used. *)

Section Arrived.
  Context (Job : eqType).
  Let d := svc_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job d.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job d PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job d.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job d.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

  Definition FaJobReadyRel
      (jrR : @prosa.behavior.ready.JobReady Job PStateR costR jaR)
      (jrL : I.Prosa_Behavior_Ready_JobReady Job d PStateL costL jaL) : SProp :=
    forall sR sL, SvcScheduleRel Job PStateR PStateL R sR sL ->
    forall (j : Job) tR tL, SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.ready.job_ready Job PStateR costR jaR jrR sR j tR)
        (I.Prosa_Behavior_Ready_JobReady_job_ready Job d PStateL costL jaL jrL sL j tL).

  Variable jrR : @prosa.behavior.ready.JobReady Job PStateR costR jaR.
  Variable jrL : I.Prosa_Behavior_Ready_JobReady Job d PStateL costL jaL.
  Hypothesis Hjr : FaJobReadyRel jrR jrL.

  Let AS := fa_forall_arrival_sequence Job.

  Lemma fa_ready_truth (j : Job) tR tL :
    SubNatRel tR tL ->
    PropSPropRel (is_true (@prosa.behavior.ready.job_ready Job PStateR costR jaR jrR schedR j tR))
      (Lean.eq (I.Prosa_Behavior_Ready_JobReady_job_ready Job d PStateL costL jaL jrL schedL j tL)
        I.Bool_true).
  Proof. intro Ht. exact (ar_bool_truth_correspondence _ _ (Hjr _ _ Hsched j tR tL Ht)). Qed.
  Let READY := fa_ready_truth.

  (** Service operations re-instantiated at this artifact's identity
      (same proofs as the accepted readiness/basic certificate). *)
  Lemma fa_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service_at Job d PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [I.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j
      (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma fa_service_during_related (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (I.Prosa_Behavior_Service_service_during Job d PStateL schedL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
      (fun t => I.Prosa_Behavior_Service_service_at Job d PStateL schedL j t)
      Ht1 Ht2 (fun tR tL Ht => fa_service_at_related j tR tL Ht).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job d PStateL schedL j t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Lemma fa_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service Job d PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service.
    cbn [I.Prosa_Behavior_Service_service].
    exact (fa_service_during_related j O tR Lean.Nat_zero tL (sub_nat_rel_canonical O) Ht).
  Qed.

  Lemma fa_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR schedR costR j tR)
      (I.Prosa_Behavior_Service_completed_by Job d PStateL schedL costL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.completed_by.
    cbn [I.Prosa_Behavior_Service_completed_by].
    exact (svc_decide_le_related _ _ _ _ (Hcost j) (fa_service_related j tR tL Ht)).
  Qed.

  Lemma fa_pending_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.pending Job PStateR schedR costR jaR j tR)
      (I.Prosa_Behavior_Service_pending Job d PStateL schedL costL jaL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.pending.
    cbn [I.Prosa_Behavior_Service_pending].
    apply svc_bool_and_related.
    - exact (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht).
    - exact (svc_bool_not_related _ _ (fa_completed_by_related j tR tL Ht)).
  Qed.

  Lemma fa_backlogged_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.ready.backlogged Job PStateR costR jaR jrR schedR j tR)
      (I.Prosa_Behavior_Ready_backlogged Job d PStateL costL jaL jrL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.ready.backlogged.
    cbn [I.Prosa_Behavior_Ready_backlogged].
    apply svc_bool_and_related.
    - exact (Hjr _ _ Hsched j tR tL Ht).
    - exact (svc_bool_not_related _ _
        (fa_scheduled_at_related Job PStateR PStateL R schedR schedL Hsched j tR tL Ht)).
  Qed.

  Lemma fa_jobs_must_be_ready_related :
    PropSPropRel
      (@prosa.behavior.ready.jobs_must_be_ready_to_execute Job jaR PStateR schedR costR jrR)
      (I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute Job d jaL PStateL schedL costL jrL).
  Proof.
    unfold prosa.behavior.ready.jobs_must_be_ready_to_execute.
    cbn [I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence;
      [exact (fa_scheduled_at_truth Job PStateR PStateL R schedR schedL Hsched j tR tL Ht)|].
    exact (READY j tR tL Ht).
  Qed.

  Lemma fa_valid_schedule_related arrR arrL :
    ArArrivalSequenceRel Job arrR arrL ->
    PropSPropRel
      (@prosa.behavior.ready.valid_schedule Job jaR PStateR schedR costR jrR arrR)
      (I.Prosa_Behavior_Ready_valid_schedule Job d jaL PStateL schedL costL jrL arrL).
  Proof.
    intro Harr. unfold prosa.behavior.ready.valid_schedule.
    cbn [I.Prosa_Behavior_Ready_valid_schedule].
    apply ar_and_correspondence.
    - exact (fa_jobs_come_from_related Job PStateR PStateL R schedR schedL Hsched _ _ Harr).
    - exact fa_jobs_must_be_ready_related.
  Qed.

  Definition src_any_ready_job_is_pending : Prop :=
    ltac:(body_of (fun s : S.statement_any_ready_job_is_pending => s Job PStateR schedR costR jaR jrR)).
  Definition tgt_any_ready_job_is_pending : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_any_ready_job_is_pending
      Job d PStateL schedL costL jaL jrL)).
  Theorem any_ready_job_is_pending_correspondence :
    PropSPropRel src_any_ready_job_is_pending tgt_any_ready_job_is_pending.
  Proof.
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence; [exact (READY j tR tL Ht)|].
    exact (ar_bool_truth_correspondence _ _ (fa_pending_related j tR tL Ht)).
  Qed.

  Definition src_ready_implies_arrived : Prop :=
    ltac:(body_of (fun s : S.statement_ready_implies_arrived => s Job PStateR schedR costR jaR jrR)).
  Definition tgt_ready_implies_arrived : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_ready_implies_arrived
      Job d PStateL schedL costL jaL jrL)).
  Theorem ready_implies_arrived_correspondence :
    PropSPropRel src_ready_implies_arrived tgt_ready_implies_arrived.
  Proof.
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence; [exact (READY j tR tL Ht)|].
    exact (ar_bool_truth_correspondence _ _
      (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
  Qed.

  Definition src_jobs_must_arrive_to_be_ready : Prop :=
    ltac:(body_of (fun s : S.statement_jobs_must_arrive_to_be_ready => s Job PStateR schedR costR jaR jrR)).
  Definition tgt_jobs_must_arrive_to_be_ready : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_jobs_must_arrive_to_be_ready
      Job d PStateL schedL costL jaL jrL)).
  Theorem jobs_must_arrive_to_be_ready_correspondence :
    PropSPropRel src_jobs_must_arrive_to_be_ready tgt_jobs_must_arrive_to_be_ready.
  Proof.
    apply ar_imp_correspondence; [exact fa_jobs_must_be_ready_related|].
    exact (fa_jobs_must_arrive_related Job PStateR PStateL R schedR schedL Hsched _ _ Hja).
  Qed.

  Definition src_valid_schedule_implies_jobs_must_arrive_to_execute : Prop :=
    ltac:(body_of (fun s : S.statement_valid_schedule_implies_jobs_must_arrive_to_execute => s Job PStateR schedR costR jaR jrR)).
  Definition tgt_valid_schedule_implies_jobs_must_arrive_to_execute : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_valid_schedule_implies_jobs_must_arrive_to_execute
      Job d PStateL schedL costL jaL jrL)).
  Theorem valid_schedule_implies_jobs_must_arrive_to_execute_correspondence :
    PropSPropRel src_valid_schedule_implies_jobs_must_arrive_to_execute tgt_valid_schedule_implies_jobs_must_arrive_to_execute.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (fa_valid_schedule_related _ _ Harr)|].
    exact (fa_jobs_must_arrive_related Job PStateR PStateL R schedR schedL Hsched _ _ Hja).
  Qed.

  Definition src_backlogged_implies_arrived : Prop :=
    ltac:(body_of (fun s : S.statement_backlogged_implies_arrived => s Job PStateR schedR costR jaR jrR)).
  Definition tgt_backlogged_implies_arrived : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_backlogged_implies_arrived
      Job d PStateL schedL costL jaL jrL)).
  Theorem backlogged_implies_arrived_correspondence :
    PropSPropRel src_backlogged_implies_arrived tgt_backlogged_implies_arrived.
  Proof.
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (fa_backlogged_related j tR tL Ht))|].
    exact (ar_bool_truth_correspondence _ _
      (has_arrived_correspondence_certificate Job jaR jaL j Hja tR tL Ht)).
  Qed.

  Definition src_backlogged_implies_incomplete : Prop :=
    ltac:(body_of (fun s : S.statement_backlogged_implies_incomplete => s Job PStateR schedR costR jaR jrR)).
  Definition tgt_backlogged_implies_incomplete : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_backlogged_implies_incomplete
      Job d PStateL schedL costL jaL jrL)).
  Theorem backlogged_implies_incomplete_correspondence :
    PropSPropRel src_backlogged_implies_incomplete tgt_backlogged_implies_incomplete.
  Proof.
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (fa_backlogged_related j tR tL Ht))|].
    exact (ar_bool_truth_correspondence _ _
      (svc_bool_not_related _ _ (fa_completed_by_related j tR tL Ht))).
  Qed.

  Definition src_job_scheduled_implies_ready : Prop :=
    ltac:(body_of (fun s : S.statement_job_scheduled_implies_ready => s Job PStateR schedR costR jaR jrR)).
  Definition tgt_job_scheduled_implies_ready : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_job_scheduled_implies_ready
      Job d PStateL schedL costL jaL jrL)).
  Theorem job_scheduled_implies_ready_correspondence :
    PropSPropRel src_job_scheduled_implies_ready tgt_job_scheduled_implies_ready.
  Proof.
    apply ar_imp_correspondence; [exact fa_jobs_must_be_ready_related|].
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence;
      [exact (fa_scheduled_at_truth Job PStateR PStateL R schedR schedL Hsched j tR tL Ht)|].
    exact (READY j tR tL Ht).
  Qed.

  Definition src_valid_schedule_jobs_come_from_arrival_sequence : Prop :=
    ltac:(body_of (fun s : S.statement_valid_schedule_jobs_come_from_arrival_sequence => s Job PStateR schedR costR jaR jrR)).
  Definition tgt_valid_schedule_jobs_come_from_arrival_sequence : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_valid_schedule_jobs_come_from_arrival_sequence
      Job d PStateL schedL costL jaL jrL)).
  Theorem valid_schedule_jobs_come_from_arrival_sequence_correspondence :
    PropSPropRel src_valid_schedule_jobs_come_from_arrival_sequence tgt_valid_schedule_jobs_come_from_arrival_sequence.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (fa_valid_schedule_related _ _ Harr)|].
    exact (fa_jobs_come_from_related Job PStateR PStateL R schedR schedL Hsched _ _ Harr).
  Qed.

  Definition src_valid_schedule_jobs_must_be_ready_to_execute : Prop :=
    ltac:(body_of (fun s : S.statement_valid_schedule_jobs_must_be_ready_to_execute => s Job PStateR schedR costR jaR jrR)).
  Definition tgt_valid_schedule_jobs_must_be_ready_to_execute : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_valid_schedule_jobs_must_be_ready_to_execute
      Job d PStateL schedL costL jaL jrL)).
  Theorem valid_schedule_jobs_must_be_ready_to_execute_correspondence :
    PropSPropRel src_valid_schedule_jobs_must_be_ready_to_execute tgt_valid_schedule_jobs_must_be_ready_to_execute.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_imp_correspondence; [exact (fa_valid_schedule_related _ _ Harr)|].
    exact fa_jobs_must_be_ready_related.
  Qed.
End Arrived.

(** ** Partition by task (inputs: Job, Task, related JobTask instances) *)

Lemma fa_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xR xL, ArListRel xR xL -> PropSPropRel (PR xR) (PL xL)) ->
  PropSPropRel (forall xR, PR xR) (forall xL, PL xL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR xL. exact (prop_to_sprop _ _ (H _ _ (ar_list_target_roundtrip xL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro xR.
    exact (sprop_to_prop _ _ (H xR (ar_list_to_imported xR) (@Lean.eq_refl _ _)) (HL _)).
Qed.

(** MathComp [\cat_(x <- xs) F x] versus Lean [bigCatSeqAll xs F]
    (= [List.flatMap], which reduces definitionally in the imported term). *)
Lemma fa_bigcat_as_foldr (T U : Type) (FR : T -> seq U) (xs : seq T) :
  Logic.eq (\big[cat/[::]]_(x <- xs) FR x) (foldr (fun x acc => FR x ++ acc) [::] xs).
Proof. elim: xs => [|x xs IH]; [by rewrite big_nil | by rewrite big_cons IH]. Qed.

Lemma fa_foldr_cat_canonical (T U : Type) (FR : T -> seq U) (FL : T -> I.List U) :
  (forall x, ArListRel (FR x) (FL x)) ->
  forall xs : seq T,
    ArListRel (foldr (fun x acc => FR x ++ acc) [::] xs)
      (I.Prosa_Util_Bigcat_bigCatSeqAll T U (ar_list_to_imported xs) FL).
Proof.
  intros HF xs. induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - exact (ar_append_related _ _ _ _ _ (HF x) IH).
Qed.

Lemma fa_bigcat_related (T U : Type) (FR : T -> seq U) (FL : T -> I.List U) :
  (forall x, ArListRel (FR x) (FL x)) ->
  forall xsR xsL, ArListRel xsR xsL ->
    ArListRel (\big[cat/[::]]_(x <- xsR) FR x)
      (I.Prosa_Util_Bigcat_bigCatSeqAll T U xsL FL).
Proof.
  intros HF xsR xsL Hxs.
  refine (ari_lean_transport (fun l => ArListRel (\big[cat/[::]]_(x <- xsR) FR x)
    (I.Prosa_Util_Bigcat_bigCatSeqAll T U l FL)) _ _ Hxs _).
  refine (ari_lean_transport (fun s => ArListRel s
    (I.Prosa_Util_Bigcat_bigCatSeqAll T U (ar_list_to_imported xsR) FL)) _ _
    (sub_imported_eq_sym _ _ (ari_logic_eq_to_lean_eq _ _ (fa_bigcat_as_foldr T U FR xsR))) _).
  exact (fa_foldr_cat_canonical T U FR FL HF xsR).
Qed.

Section Partition.
  Context (Job Task : eqType).
  Let dJ := ar_decidable_eq Job.
  Let dT := ar_decidable_eq Task.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).

  Lemma fa_all_jobs_from_taskset_related arrR arrL tsR tsL :
    ArArrivalSequenceRel Job arrR arrL -> ArListRel tsR tsL ->
    PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
      (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
  Proof.
    intros Harr Hts.
    unfold prosa.model.task.concept.all_jobs_from_taskset.
    cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    have E := imported_eq_to_coq_eq _ _ (Hjt j).
    rewrite -E.
    exact (fa_mem_truth Task _ _ _ Hts).
  Qed.

  Definition src_arrivals_between_partitioned_by_task : Prop :=
    ltac:(body_of (fun s : S.statement_arrivals_between_partitioned_by_task => s Job Task jtR)).
  Definition tgt_arrivals_between_partitioned_by_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Behavior_Arrivals_arrivals_between_partitioned_by_task
      Job dJ Task dT jtL)).
  Theorem arrivals_between_partitioned_by_task_correspondence :
    PropSPropRel src_arrivals_between_partitioned_by_task
      tgt_arrivals_between_partitioned_by_task.
  Proof.
    apply (fa_forall_arrival_sequence Job) => arrR arrL Harr.
    apply fa_forall_list => tsR tsL Hts.
    apply ar_imp_correspondence; [exact (fa_all_jobs_from_taskset_related _ _ _ _ Harr Hts)|].
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_identity_correspondence => j.
    exact (ar_bool_eq_correspondence _ _ _ _
      (ar_decide_mem_related Job j _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2))
      (ar_decide_mem_related Job j _ _
        (fa_bigcat_related Task Job _ _
          (fun tsk => task_arrivals_between_correspondence Job Task jtR jtL Hjt arrR arrL Harr
            tsk tsk t1R t1L t2R t2L (@Lean.eq_refl _ tsk) H1 H2)
          tsR tsL Hts))).
  Qed.
End Partition.
