From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From prosa Require Import FactsTaskArrivalsSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsTaskArrivals ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations.

Module S := FactsTaskArrivalsSemanticSource.FactsTaskArrivalsSemanticSource.

(** Statement correspondences for [analysis/facts/model/task_arrivals.v].

    Source side: the extracted statement [S.statement_X] specialised at the
    leading input binders ([Job], [Task], [JobTask], and [JobArrival] where
    present); target side: the type of the imported Lean theorem.  Arrival
    sequences are covered in both directions; [job_task] is related by
    [Lean.eq] (as in the accepted arrivals certificates). *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Arithmetic and propositional helpers *)

Lemma ta_le_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (I.LE_le_inst1 Lean.Nat I.instLENat aL bL).
Proof. exact (sub_nat_le_correspondence aR aL bR bL). Qed.

Lemma ta_lt_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (I.LT_lt_inst1 Lean.Nat I.instLTNat aL bL).
Proof. exact (sub_nat_lt_correspondence aR aL bR bL). Qed.

Lemma ta_range_le_lt aR aL bR bL cR cL :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel cR cL ->
  PropSPropRel (is_true (leq aR bR && ltn bR cR))
    (Lean.eq (I.Bool_and (ar_target_decide_le aL bL) (ar_target_decide_lt bL cL)) I.Bool_true).
Proof.
  intros Ha Hb Hc. apply ar_bool_truth_correspondence.
  exact (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ha Hb)
    (ar_decide_lt_related _ _ _ _ Hb Hc)).
Qed.

Lemma ta_range_le_le aR aL bR bL cR cL :
  SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel cR cL ->
  PropSPropRel (is_true (leq aR bR && leq bR cR))
    (Lean.eq (I.Bool_and (ar_target_decide_le aL bL) (ar_target_decide_le bL cL)) I.Bool_true).
Proof.
  intros Ha Hb Hc. apply ar_bool_truth_correspondence.
  exact (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ Ha Hb)
    (ar_decide_le_related _ _ _ _ Hb Hc)).
Qed.

Lemma ta_mem_truth (T : eqType) (x : T) (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL ->
  PropSPropRel (is_true (x \in xsR)) (Lean.eq (ar_target_decide_mem T x xsL) I.Bool_true).
Proof. intro H. exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related T x xsR xsL H)). Qed.

Lemma ta_eq_correspondence (T : Type) (xR xL yR yL : T) :
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

Lemma ta_exists_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xR xL, ArListRel xR xL -> PropSPropRel (PR xR) (PL xL)) ->
  PropSPropRel (exists x, PR x) (I.Exists (I.List T) PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro (I.List T) PL (ar_list_to_imported x)
      (prop_to_sprop _ _ (H x _ (@Lean.eq_refl _ _)) Hx)).
  - intros [xL Hx]. apply strictly_inhabits. exists (ar_list_to_rocq xL).
    exact (sprop_to_prop _ _ (H _ xL (ar_list_target_roundtrip xL)) Hx).
Qed.

Lemma ta_false_correspondence : PropSPropRel Logic.False I.False.
Proof. apply prop_sprop_rel_intro; intro H; destruct H. Qed.

Lemma ta_list_neq_nil (T : eqType) (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL -> PropSPropRel (xsR <> [::]) (I.Ne (I.List T) xsL (I.List_nil T)).
Proof.
  intro H. unfold I.Ne, I.Not. apply ar_imp_correspondence.
  - exact (ar_list_eq_correspondence T _ [::] _ (I.List_nil T) H (@Lean.eq_refl _ _)).
  - exact ta_false_correspondence.
Qed.

Lemma ta_prefix_of_related (T : eqType) xsR xsL ysR ysL :
  ArListRel xsR xsL -> ArListRel ysR ysL ->
  PropSPropRel (@prosa.util.list.ListSemanticSource.prefix_of T xsR ysR)
    (I.Prosa_Util_List_prefix_of T (ar_decidable_eq T) xsL ysL).
Proof.
  intros Hx Hy.
  unfold prosa.util.list.ListSemanticSource.prefix_of. cbn [I.Prosa_Util_List_prefix_of].
  apply ta_exists_list => tR tL Ht.
  exact (ar_list_eq_correspondence T _ _ _ _ (ar_append_related T _ _ _ _ Hx Ht) Hy).
Qed.

Lemma ta_strict_prefix_of_related (T : eqType) xsR xsL ysR ysL :
  ArListRel xsR xsL -> ArListRel ysR ysL ->
  PropSPropRel (@prosa.util.list.ListSemanticSource.strict_prefix_of T xsR ysR)
    (I.Prosa_Util_List_strict_prefix_of T (ar_decidable_eq T) xsL ysL).
Proof.
  intros Hx Hy.
  unfold prosa.util.list.ListSemanticSource.strict_prefix_of. cbn [I.Prosa_Util_List_strict_prefix_of].
  apply ta_exists_list => tR tL Ht.
  apply ar_and_correspondence.
  - exact (ta_list_neq_nil T _ _ Ht).
  - exact (ar_list_eq_correspondence T _ _ _ _ (ar_append_related T _ _ _ _ Hx Ht) Hy).
Qed.

(** ** Sums over [index_iota] versus [sumSeq (List.range' _ _)] *)

Lemma ta_list_sum_fold (xs : I.List_inst1 Lean.Nat) :
  Lean.eq (I.List_sum_inst1 Lean.Nat I.instAddNat (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass) xs)
    (svc_target_list_fold_sum xs).
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (fun v => Lean.Nat_add x v) _ _ IH).
Qed.

Lemma ta_interval_sum_related (mR nR : nat) (mL nL : Lean.Nat)
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  SubNatRel mR mL -> SubNatRel nR nL -> SvcNatFunRel fR fL ->
  SubNatRel (\sum_(mR <= i < nR) fR i)
    (I.Prosa_Util_Sum_sumSeq_inst1 Lean.Nat (I.List_range' mL (svc_target_sub nL mL) svc_target_one) fL).
Proof.
  intros Hm Hn Hf.
  refine (sub_imported_eq_trans _ _ _ (svc_interval_sum_related mR nR mL nL fR fL Hm Hn Hf) _).
  exact (sub_imported_eq_sym _ _ (ta_list_sum_fold _)).
Qed.

(** ** Arrival-sequence coverage *)

Section ArrCoverage.
  Context (Job : eqType).
  Definition ta_arrival_sequence_to_source
      (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job)) :
      prosa.behavior.arrival_sequence.arrival_sequence Job :=
    fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).
  Lemma ta_arrival_sequence_to_source_rel arrL :
    ArArrivalSequenceRel Job (ta_arrival_sequence_to_source arrL) arrL.
  Proof.
    intros tR tL Ht. unfold ArListRel, ta_arrival_sequence_to_source.
    refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
    exact (sub_imported_eq_congr arrL _ _ Ht).
  Qed.
  Lemma ta_forall_arrival_sequence
      (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
      (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job) -> SProp) :
    (forall arrR arrL, ArArrivalSequenceRel Job arrR arrL -> PropSPropRel (PR arrR) (PL arrL)) ->
    PropSPropRel (forall arrR, PR arrR) (forall arrL, PL arrL).
  Proof.
    intro H. apply prop_sprop_rel_intro.
    - intros HR arrL. exact (prop_to_sprop _ _ (H _ _ (ta_arrival_sequence_to_source_rel arrL)) (HR _)).
    - intro HL. apply strictly_inhabits. intro arrR.
      exact (sprop_to_prop _ _ (H _ _ (ar_arrival_sequence_canonical Job arrR)) (HL _)).
  Qed.
End ArrCoverage.

(** ** [sorted] / [List.IsChain] (same proofs as the accepted facts/arrivals certificate) *)

Inductive TaSUnit : SProp := ta_sunit.

Definition ta_ischain_head {A : Type} (R : A -> A -> SProp) (l : I.List A) : SProp :=
  match l with
  | I.List_cons x (I.List_cons y _) => R x y
  | _ => TaSUnit
  end.

Definition ta_ischain_tail {A : Type} (R : A -> A -> SProp) (l : I.List A) : SProp :=
  match l with
  | I.List_cons _ ((I.List_cons _ _) as rest) => I.List_IsChain A R rest
  | _ => TaSUnit
  end.

Lemma ta_ischain_inv_head {A : Type} (R : A -> A -> SProp) (l : I.List A) :
  I.List_IsChain A R l -> ta_ischain_head R l.
Proof. intro H. destruct H as [|a|a b l hr h]; [exact ta_sunit|exact ta_sunit|exact hr]. Qed.

Lemma ta_ischain_inv_tail {A : Type} (R : A -> A -> SProp) (l : I.List A) :
  I.List_IsChain A R l -> ta_ischain_tail R l.
Proof. intro H. destruct H as [|a|a b l hr h]; [exact ta_sunit|exact ta_sunit|exact h]. Qed.

Lemma ta_path_ischain (A : Type) (rR : A -> A -> bool) (rL : A -> A -> I.Bool)
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
      * exact (sprop_to_prop _ _ Hxy (ta_ischain_inv_head _ _ H)).
      * exact (sprop_to_prop _ _ Hrest (ta_ischain_inv_tail _ _ H)).
Qed.

Lemma ta_sorted_ischain (A : Type) (rR : A -> A -> bool) (rL : A -> A -> I.Bool)
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
  - exact (ta_path_ischain A rR rL Hr xs x).
Qed.


(** ** Statement correspondences *)

Section Statements.
  Context (Job Task : eqType).
  Let dJ := ar_decidable_eq Job.
  Let dT := ar_decidable_eq Task.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).

  Let AS := ta_forall_arrival_sequence Job.
  Let TAB arrR arrL Harr tsk t1R t1L t2R t2L H1 H2 :=
    task_arrivals_between_correspondence Job Task jtR jtL Hjt arrR arrL Harr tsk tsk
      t1R t1L t2R t2L (@Lean.eq_refl _ tsk) H1 H2.
  Let NTA arrR arrL Harr tsk t1R t1L t2R t2L H1 H2 :=
    number_of_task_arrivals_correspondence Job Task jtR jtL Hjt arrR arrL Harr tsk tsk
      t1R t1L t2R t2L (@Lean.eq_refl _ tsk) H1 H2.
  Let ABC arrR arrL Harr := arrivals_between_correspondence_certificate Job arrR arrL Harr.
  Let ARR arrR arrL Harr j := arrives_in_correspondence_certificate Job arrR arrL j Harr.
  Let TASKEQ j tsk := ta_eq_correspondence Task _ _ tsk tsk (Hjt j) (@Lean.eq_refl _ tsk).

  Lemma ta_job_task_eq_decide (j : Job) (tsk : Task) :
    ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
      (I.Decidable_decide
        (Lean.eq (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j) tsk)
        (dT (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j) tsk)).
  Proof.
    refine (ari_lean_transport (fun v => ArBoolRel _
      (I.Decidable_decide (Lean.eq v tsk) (dT v tsk))) _ _ (Hjt j) _).
    exact (ari_decide_eq_related Task _ tsk).
  Qed.

  Definition src_num_arrivals_of_task_cat : Prop :=
    ltac:(body_of (fun s : S.statement_num_arrivals_of_task_cat => s Job Task jtR)).
  Definition tgt_num_arrivals_of_task_cat : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_num_arrivals_of_task_cat Job dJ Task dT jtL)).
  Theorem num_arrivals_of_task_cat_correspondence :
    PropSPropRel src_num_arrivals_of_task_cat tgt_num_arrivals_of_task_cat.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => tsk.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (ta_range_le_le _ _ _ _ _ _ H1 Ht H2)|].
    exact (sub_nat_eq_correspondence _ _ _ _ (NTA _ _ Harr tsk _ _ _ _ H1 H2)
      (sub_add_correspondence _ _ _ _ (NTA _ _ Harr tsk _ _ _ _ H1 Ht) (NTA _ _ Harr tsk _ _ _ _ Ht H2))).
  Qed.

  Definition src_task_arrivals_between_cat : Prop :=
    ltac:(body_of (fun s : S.statement_task_arrivals_between_cat => s Job Task jtR)).
  Definition tgt_task_arrivals_between_cat : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_between_cat Job dJ Task dT jtL)).
  Theorem task_arrivals_between_cat_correspondence :
    PropSPropRel src_task_arrivals_between_cat tgt_task_arrivals_between_cat.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => tsk.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence; [exact (ta_le_related _ _ _ _ H1 Ht)|].
    apply ar_imp_correspondence; [exact (ta_le_related _ _ _ _ Ht H2)|].
    exact (ar_list_eq_correspondence Job _ _ _ _ (TAB _ _ Harr tsk _ _ _ _ H1 H2)
      (ar_append_related Job _ _ _ _ (TAB _ _ Harr tsk _ _ _ _ H1 Ht) (TAB _ _ Harr tsk _ _ _ _ Ht H2))).
  Qed.

  Definition src_task_arrivals_cat : Prop :=
    ltac:(body_of (fun s : S.statement_task_arrivals_cat => s Job Task jtR)).
  Definition tgt_task_arrivals_cat : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_cat Job dJ Task dT jtL)).
  Theorem task_arrivals_cat_correspondence :
    PropSPropRel src_task_arrivals_cat tgt_task_arrivals_cat.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => tsk.
    apply ar_forall_nat_correspondence => tmR tmL Hm.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence; [exact (ta_le_related _ _ _ _ Hm Ht)|].
    exact (ar_list_eq_correspondence Job _ _ _ _
      (task_arrivals_up_to_correspondence Job Task jtR jtL Hjt arrR arrL Harr tsk tsk _ _ (@Lean.eq_refl _ _) Ht)
      (ar_append_related Job _ _ _ _
        (task_arrivals_up_to_correspondence Job Task jtR jtL Hjt arrR arrL Harr tsk tsk _ _ (@Lean.eq_refl _ _) Hm)
        (TAB _ _ Harr tsk _ _ _ _ (ari_succ_related _ _ Hm) (ari_succ_related _ _ Ht)))).
  Qed.

  Definition src_task_arrivals_between_subset : Prop :=
    ltac:(body_of (fun s : S.statement_task_arrivals_between_subset => s Job Task jtR)).
  Definition tgt_task_arrivals_between_subset : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_between_subset Job dJ Task dT jtL)).
  Theorem task_arrivals_between_subset_correspondence :
    PropSPropRel src_task_arrivals_between_subset tgt_task_arrivals_between_subset.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => tsk.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (ta_mem_truth Job j _ _ (TAB _ _ Harr tsk _ _ _ _ H1 H2))|].
    exact (ta_mem_truth Job j _ _ (ABC _ _ Harr _ _ _ _ H1 H2)).
  Qed.

  Definition src_arrives_in_task_arrivals_implies_arrived : Prop :=
    ltac:(body_of (fun s : S.statement_arrives_in_task_arrivals_implies_arrived => s Job Task jtR)).
  Definition tgt_arrives_in_task_arrivals_implies_arrived : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_arrives_in_task_arrivals_implies_arrived Job dJ Task dT jtL)).
  Theorem arrives_in_task_arrivals_implies_arrived_correspondence :
    PropSPropRel src_arrives_in_task_arrivals_implies_arrived tgt_arrives_in_task_arrivals_implies_arrived.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => tsk.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (ta_mem_truth Job j _ _ (TAB _ _ Harr tsk _ _ _ _ H1 H2))|].
    exact (ARR _ _ Harr j).
  Qed.

  Definition src_arrives_in_task_arrivals_implies_job_task : Prop :=
    ltac:(body_of (fun s : S.statement_arrives_in_task_arrivals_implies_job_task => s Job Task jtR)).
  Definition tgt_arrives_in_task_arrivals_implies_job_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_arrives_in_task_arrivals_implies_job_task Job dJ Task dT jtL)).
  Theorem arrives_in_task_arrivals_implies_job_task_correspondence :
    PropSPropRel src_arrives_in_task_arrivals_implies_job_task tgt_arrives_in_task_arrivals_implies_job_task.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => tsk.
    apply ar_forall_identity_correspondence => j.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence;
      [exact (ta_mem_truth Job j _ _ (task_arrivals_before_correspondence Job Task jtR jtL Hjt
         arrR arrL Harr tsk tsk _ _ (@Lean.eq_refl _ _) Ht))|].
    exact (ar_bool_truth_correspondence _ _ (ta_job_task_eq_decide j tsk)).
  Qed.

  Definition src_in_task_arrivals_between_implies_job_of_task : Prop :=
    ltac:(body_of (fun s : S.statement_in_task_arrivals_between_implies_job_of_task => s Job Task jtR)).
  Definition tgt_in_task_arrivals_between_implies_job_of_task : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_in_task_arrivals_between_implies_job_of_task Job dJ Task dT jtL)).
  Theorem in_task_arrivals_between_implies_job_of_task_correspondence :
    PropSPropRel src_in_task_arrivals_between_implies_job_of_task tgt_in_task_arrivals_between_implies_job_of_task.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => tsk.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (ta_mem_truth Job j _ _ (TAB _ _ Harr tsk _ _ _ _ H1 H2))|].
    exact (TASKEQ j tsk).
  Qed.

  Definition src_task_arrivals_nonempty : Prop :=
    ltac:(body_of (fun s : S.statement_task_arrivals_nonempty => s Job Task jtR)).
  Definition tgt_task_arrivals_nonempty : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_nonempty Job dJ Task dT jtL)).
  Theorem task_arrivals_nonempty_correspondence :
    PropSPropRel src_task_arrivals_nonempty tgt_task_arrivals_nonempty.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => tsk.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (ta_mem_truth Job j _ _ (TAB _ _ Harr tsk _ _ _ _ H1 H2))|].
    exact (ta_lt_related _ _ _ _ H1 H2).
  Qed.

  Definition src_number_of_task_arrivals_nonzero : Prop :=
    ltac:(body_of (fun s : S.statement_number_of_task_arrivals_nonzero => s Job Task jtR)).
  Definition tgt_number_of_task_arrivals_nonzero : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_number_of_task_arrivals_nonzero Job dJ Task dT jtL)).
  Theorem number_of_task_arrivals_nonzero_correspondence :
    PropSPropRel src_number_of_task_arrivals_nonzero tgt_number_of_task_arrivals_nonzero.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => tsk.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    apply ar_imp_correspondence;
      [exact (ta_lt_related _ _ _ _ (sub_nat_rel_canonical O) (NTA _ _ Harr tsk _ _ _ _ H1 H2))|].
    exact (ta_lt_related _ _ _ _ H1 H2).
  Qed.

  Definition src_task_arrivals_between_is_cat_of_task_arrivals_at : Prop :=
    ltac:(body_of (fun s : S.statement_task_arrivals_between_is_cat_of_task_arrivals_at => s Job Task jtR)).
  Definition tgt_task_arrivals_between_is_cat_of_task_arrivals_at : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_between_is_cat_of_task_arrivals_at Job dJ Task dT jtL)).
  Theorem task_arrivals_between_is_cat_of_task_arrivals_at_correspondence :
    PropSPropRel src_task_arrivals_between_is_cat_of_task_arrivals_at
      tgt_task_arrivals_between_is_cat_of_task_arrivals_at.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => tsk.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    exact (ar_list_eq_correspondence Job _ _ _ _ (TAB _ _ Harr tsk _ _ _ _ H1 H2)
      (ar_bigCatNat_related_any Job _ _ _ _ _ _
        (fun tR tL Ht => task_arrivals_at_correspondence Job Task jtR jtL Hjt arrR arrL Harr
          tsk tsk tR tL (@Lean.eq_refl _ _) Ht) H1 H2)).
  Qed.

  Definition src_size_of_task_arrivals_between : Prop :=
    ltac:(body_of (fun s : S.statement_size_of_task_arrivals_between => s Job Task jtR)).
  Definition tgt_size_of_task_arrivals_between : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_size_of_task_arrivals_between Job dJ Task dT jtL)).
  Theorem size_of_task_arrivals_between_correspondence :
    PropSPropRel src_size_of_task_arrivals_between tgt_size_of_task_arrivals_between.
  Proof.
    apply AS => arrR arrL Harr.
    apply ar_forall_identity_correspondence => tsk.
    apply ar_forall_nat_correspondence => t1R t1L H1.
    apply ar_forall_nat_correspondence => t2R t2L H2.
    exact (sub_nat_eq_correspondence _ _ _ _ (ari_size_related Job _ _ (TAB _ _ Harr tsk _ _ _ _ H1 H2))
      (ta_interval_sum_related _ _ _ _ _ _ H1 H2
        (fun tR tL Ht => ari_size_related Job _ _
          (task_arrivals_at_correspondence Job Task jtR jtL Hjt arrR arrL Harr
            tsk tsk tR tL (@Lean.eq_refl _ _) Ht)))).
  Qed.

  Section WithArrival.
    Variable jaR : prosa.behavior.job.JobArrival Job.
    Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
    Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

    Let CAT arrR arrL Harr := consistent_arrival_times_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.
    Let UPJA arrR arrL Harr j := task_arrivals_up_to_job_arrival_correspondence Job Task jtR jtL Hjt
      arrR arrL Harr jaR jaL Hja j.
    Let TAUP arrR arrL Harr tsk tR tL Ht := task_arrivals_up_to_correspondence Job Task jtR jtL Hjt
      arrR arrL Harr tsk tsk tR tL (@Lean.eq_refl _ tsk) Ht.

    Definition src_task_arrivals_up_to_prefix_cat : Prop :=
      ltac:(body_of (fun s : S.statement_task_arrivals_up_to_prefix_cat => s Job Task jtR jaR)).
    Definition tgt_task_arrivals_up_to_prefix_cat : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_up_to_prefix_cat Job dJ Task dT jtL jaL)).
    Theorem task_arrivals_up_to_prefix_cat_correspondence :
      PropSPropRel src_task_arrivals_up_to_prefix_cat tgt_task_arrivals_up_to_prefix_cat.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_forall_identity_correspondence => j1.
      apply ar_forall_identity_correspondence => j2.
      apply ar_imp_correspondence; [exact (ARR _ _ Harr j1)|].
      apply ar_imp_correspondence; [exact (ARR _ _ Harr j2)|].
      apply ar_imp_correspondence; [exact (ta_eq_correspondence Task _ _ _ _ (Hjt j1) (Hjt j2))|].
      apply ar_imp_correspondence; [exact (ta_le_related _ _ _ _ (Hja j1) (Hja j2))|].
      exact (ta_prefix_of_related Job _ _ _ _ (UPJA _ _ Harr j1) (UPJA _ _ Harr j2)).
    Qed.

    Definition src_arrives_in_task_arrivals_up_to : Prop :=
      ltac:(body_of (fun s : S.statement_arrives_in_task_arrivals_up_to => s Job Task jtR jaR)).
    Definition tgt_arrives_in_task_arrivals_up_to : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_arrives_in_task_arrivals_up_to Job dJ Task dT jtL jaL)).
    Theorem arrives_in_task_arrivals_up_to_correspondence :
      PropSPropRel src_arrives_in_task_arrivals_up_to tgt_arrives_in_task_arrivals_up_to.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_imp_correspondence; [exact (CAT _ _ Harr)|].
      apply ar_forall_identity_correspondence => j.
      apply ar_imp_correspondence; [exact (ARR _ _ Harr j)|].
      exact (ta_mem_truth Job j _ _ (UPJA _ _ Harr j)).
    Qed.

    Definition src_arrives_in_task_arrivals_at : Prop :=
      ltac:(body_of (fun s : S.statement_arrives_in_task_arrivals_at => s Job Task jtR jaR)).
    Definition tgt_arrives_in_task_arrivals_at : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_arrives_in_task_arrivals_at Job dJ Task dT jtL jaL)).
    Theorem arrives_in_task_arrivals_at_correspondence :
      PropSPropRel src_arrives_in_task_arrivals_at tgt_arrives_in_task_arrivals_at.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_imp_correspondence; [exact (CAT _ _ Harr)|].
      apply ar_forall_identity_correspondence => j.
      apply ar_imp_correspondence; [exact (ARR _ _ Harr j)|].
      exact (ta_mem_truth Job j _ _ (task_arrivals_at_job_arrival_correspondence Job Task jtR jtL Hjt
        arrR arrL Harr jaR jaL Hja j)).
    Qed.

    Definition src_task_arrivals_up_to_cat : Prop :=
      ltac:(body_of (fun s : S.statement_task_arrivals_up_to_cat => s Job Task jtR jaR)).
    Definition tgt_task_arrivals_up_to_cat : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_up_to_cat Job dJ Task dT jtL jaL)).
    Theorem task_arrivals_up_to_cat_correspondence :
      PropSPropRel src_task_arrivals_up_to_cat tgt_task_arrivals_up_to_cat.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_forall_identity_correspondence => j.
      apply ar_imp_correspondence; [exact (ARR _ _ Harr j)|].
      exact (ar_list_eq_correspondence Job _ _ _ _ (UPJA _ _ Harr j)
        (ar_append_related Job _ _ _ _
          (task_arrivals_before_job_arrival_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j)
          (task_arrivals_at_job_arrival_correspondence Job Task jtR jtL Hjt arrR arrL Harr jaR jaL Hja j))).
    Qed.

    Definition src_job_in_task_arrivals_between : Prop :=
      ltac:(body_of (fun s : S.statement_job_in_task_arrivals_between => s Job Task jtR jaR)).
    Definition tgt_job_in_task_arrivals_between : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_job_in_task_arrivals_between Job dJ Task dT jtL jaL)).
    Theorem job_in_task_arrivals_between_correspondence :
      PropSPropRel src_job_in_task_arrivals_between tgt_job_in_task_arrivals_between.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_imp_correspondence; [exact (CAT _ _ Harr)|].
      apply ar_forall_identity_correspondence => tsk.
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence; [exact (ARR _ _ Harr j)|].
      apply ar_imp_correspondence; [exact (TASKEQ j tsk)|].
      apply ar_imp_correspondence; [exact (ta_range_le_lt _ _ _ _ _ _ H1 (Hja j) H2)|].
      exact (ta_mem_truth Job j _ _ (TAB _ _ Harr tsk _ _ _ _ H1 H2)).
    Qed.

    Definition src_arrives_in_task_arrivals_before_implies_arrives_before : Prop :=
      ltac:(body_of (fun s : S.statement_arrives_in_task_arrivals_before_implies_arrives_before => s Job Task jtR jaR)).
    Definition tgt_arrives_in_task_arrivals_before_implies_arrives_before : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_arrives_in_task_arrivals_before_implies_arrives_before Job dJ Task dT jtL jaL)).
    Theorem arrives_in_task_arrivals_before_implies_arrives_before_correspondence :
      PropSPropRel src_arrives_in_task_arrivals_before_implies_arrives_before
        tgt_arrives_in_task_arrivals_before_implies_arrives_before.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_imp_correspondence; [exact (CAT _ _ Harr)|].
      apply ar_forall_identity_correspondence => tsk.
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence;
        [exact (ta_mem_truth Job j _ _ (task_arrivals_before_correspondence Job Task jtR jtL Hjt
           arrR arrL Harr tsk tsk _ _ (@Lean.eq_refl _ _) Ht))|].
      exact (ta_lt_related _ _ _ _ (Hja j) Ht).
    Qed.

    Definition src_uniq_task_arrivals : Prop :=
      ltac:(body_of (fun s : S.statement_uniq_task_arrivals => s Job Task jtR jaR)).
    Definition tgt_uniq_task_arrivals : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_uniq_task_arrivals Job dJ Task dT jtL jaL)).
    Theorem uniq_task_arrivals_correspondence :
      PropSPropRel src_uniq_task_arrivals tgt_uniq_task_arrivals.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_imp_correspondence; [exact (CAT _ _ Harr)|].
      apply ar_forall_identity_correspondence => tsk.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence;
        [exact (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr)|].
      exact (ar_uniq_correspondence Job _ _ (TAUP _ _ Harr tsk _ _ Ht)).
    Qed.

    Definition src_task_arrivals_between_uniq : Prop :=
      ltac:(body_of (fun s : S.statement_task_arrivals_between_uniq => s Job Task jtR jaR)).
    Definition tgt_task_arrivals_between_uniq : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_between_uniq Job dJ Task dT jtL jaL)).
    Theorem task_arrivals_between_uniq_correspondence :
      PropSPropRel src_task_arrivals_between_uniq tgt_task_arrivals_between_uniq.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_imp_correspondence; [exact (CAT _ _ Harr)|].
      apply ar_forall_identity_correspondence => tsk.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      apply ar_imp_correspondence;
        [exact (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr)|].
      exact (ar_uniq_correspondence Job _ _ (TAB _ _ Harr tsk _ _ _ _ H1 H2)).
    Qed.

    Definition src_job_notin_task_arrivals_before : Prop :=
      ltac:(body_of (fun s : S.statement_job_notin_task_arrivals_before => s Job Task jtR jaR)).
    Definition tgt_job_notin_task_arrivals_before : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_job_notin_task_arrivals_before Job dJ Task dT jtL jaL)).
    Theorem job_notin_task_arrivals_before_correspondence :
      PropSPropRel src_job_notin_task_arrivals_before tgt_job_notin_task_arrivals_before.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_imp_correspondence; [exact (CAT _ _ Harr)|].
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (ARR _ _ Harr j)|].
      apply ar_imp_correspondence; [exact (ta_lt_related _ _ _ _ Ht (Hja j))|].
      exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
        (ar_decide_mem_related Job j _ _ (task_arrivals_up_to_correspondence Job Task jtR jtL Hjt
          arrR arrL Harr _ _ _ _ (Hjt j) Ht)))).
    Qed.

    Definition src_arrival_lt_implies_strict_prefix : Prop :=
      ltac:(body_of (fun s : S.statement_arrival_lt_implies_strict_prefix => s Job Task jtR jaR)).
    Definition tgt_arrival_lt_implies_strict_prefix : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_arrival_lt_implies_strict_prefix Job dJ Task dT jtL jaL)).
    Theorem arrival_lt_implies_strict_prefix_correspondence :
      PropSPropRel src_arrival_lt_implies_strict_prefix tgt_arrival_lt_implies_strict_prefix.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_imp_correspondence; [exact (CAT _ _ Harr)|].
      apply ar_forall_identity_correspondence => tsk.
      apply ar_forall_identity_correspondence => j1.
      apply ar_forall_identity_correspondence => j2.
      apply ar_imp_correspondence; [exact (TASKEQ j1 tsk)|].
      apply ar_imp_correspondence; [exact (TASKEQ j2 tsk)|].
      apply ar_imp_correspondence; [exact (ARR _ _ Harr j1)|].
      apply ar_imp_correspondence; [exact (ARR _ _ Harr j2)|].
      apply ar_imp_correspondence; [exact (ta_lt_related _ _ _ _ (Hja j1) (Hja j2))|].
      exact (ta_strict_prefix_of_related Job _ _ _ _ (UPJA _ _ Harr j1) (UPJA _ _ Harr j2)).
    Qed.

    Definition src_nth_job_of_task_arrivals : Prop :=
      ltac:(body_of (fun s : S.statement_nth_job_of_task_arrivals => s Job Task jtR jaR)).
    Definition tgt_nth_job_of_task_arrivals : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_nth_job_of_task_arrivals Job dJ Task dT jtL jaL)).
    Theorem nth_job_of_task_arrivals_correspondence :
      PropSPropRel src_nth_job_of_task_arrivals tgt_nth_job_of_task_arrivals.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_imp_correspondence; [exact (CAT _ _ Harr)|].
      apply ar_forall_identity_correspondence => tsk.
      apply ar_forall_nat_correspondence => nR nL Hn.
      apply ar_forall_identity_correspondence => j_def.
      apply ar_forall_identity_correspondence => j.
      apply ar_forall_nat_correspondence => tR tL Ht.
      apply ar_imp_correspondence; [exact (ARR _ _ Harr j)|].
      apply ar_imp_correspondence; [exact (TASKEQ j tsk)|].
      apply ar_imp_correspondence;
        [exact (sub_nat_eq_correspondence _ _ _ _ (job_index_correspondence Job Task jtR jtL Hjt
           arrR arrL Harr jaR jaL Hja j) Hn)|].
      apply ar_imp_correspondence; [exact (ta_le_related _ _ _ _ (Hja j) Ht)|].
      exact (ta_eq_correspondence Job _ _ j j
        (ari_nth_related Job j_def _ _ _ _ (TAUP _ _ Harr tsk _ _ Ht) Hn) (@Lean.eq_refl _ _)).
    Qed.

    Definition ta_by_arrival_times_related (j1 j2 : Job) :
      ArBoolRel (@prosa.FactsArrivalsSemanticSource.FactsArrivalsSemanticSource.by_arrival_times Job jaR j1 j2)
        (I.Prosa_Analysis_Facts_Behavior_Arrivals_by_arrival_times Job dJ jaL j1 j2) :=
      ar_decide_le_related _ _ _ _ (Hja j1) (Hja j2).

    Definition src_task_arrivals_between_sorted : Prop :=
      ltac:(body_of (fun s : S.statement_task_arrivals_between_sorted => s Job Task jtR jaR)).
    Definition tgt_task_arrivals_between_sorted : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskArrivals_task_arrivals_between_sorted Job dJ Task dT jtL jaL)).
    Theorem task_arrivals_between_sorted_correspondence :
      PropSPropRel src_task_arrivals_between_sorted tgt_task_arrivals_between_sorted.
    Proof.
      apply AS => arrR arrL Harr.
      apply ar_imp_correspondence; [exact (CAT _ _ Harr)|].
      apply ar_forall_identity_correspondence => tsk.
      apply ar_forall_nat_correspondence => t1R t1L H1.
      apply ar_forall_nat_correspondence => t2R t2L H2.
      exact (ta_sorted_ischain Job _ _ ta_by_arrival_times_related _ _ (TAB _ _ Harr tsk _ _ _ _ H1 H2)).
    Qed.
  End WithArrival.
End Statements.
