From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From HB Require Import structures.
From prosa Require Import implementation.definitions.job_constructor FactsJobConstructorSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsJobConstructor ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  EacFullCorrespondence AbCorrespondence ImplTaskCorrespondence JobConstructorCorrespondence
  JcJitterSvcBaseAdapter JcJitterSvcNatBoolOperations JcJitterSvcIntervalOperations
  JcMaximalArrivalSequenceCorrespondence JcListOps.

Module I := ImportedFactsJobConstructor.
Module T := prosa.implementation.definitions.task.
Module JC := prosa.implementation.definitions.job_constructor.
Module MAS := prosa.implementation.definitions.maximal_arrival_sequence.
Module S := FactsJobConstructorSemanticSource.FactsJobConstructorSemanticSource.

(** Statement correspondences for [implementation/facts/job_constructor.v].

    Concrete tasks and jobs are related by the accepted fieldwise canonical relations [ItTaskRel] / [ItJobRel] (two-way
    totals); task and job lists by the canonical list maps; Nat values by [SubNatRel].  The imported statements live at
    the concrete (universe-0) copies of the list operations and of the maximal-arrival-sequence definitions
    ([List_inst1], [concrete_arrival_sequence_inst3], [max_arrivals_at_inst1], …):
    - the maximal-arrival-sequence definitions are related over the two concrete task types by the task-relational
      form of the accepted definition certificates (replayed at this export as [JcMaximalArrivalSequenceCorrespondence]);
    - membership and uniqueness are the accepted list relations ([JcListOps], at the concrete list copies) over the
      compiled task and job types, which carry the equality type transported from the source types along the
      accepted import/export maps;
    - the half-open concatenation of [arrivals_between] uses the concrete-type [bigCat] equations of this file's
      export root. *)

Definition LT := I.Prosa_Implementation_Definitions_Task_concrete_task.
Definition LJ := I.Prosa_Implementation_Definitions_Task_concrete_job.
Definition jf_dT := I.Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task.
Definition jf_dJ := I.Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job.
Definition jf_cL := I.Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals.

(** ** Generic relational combinators *)

Lemma jf_forall_cover {A B : Type} (R : A -> B -> SProp) (toL : A -> B) (toR : B -> A)
    (PR : A -> Prop) (PL : B -> SProp) :
  (forall a, R a (toL a)) -> (forall b, R (toR b) b) ->
  (forall a b, R a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intros HL HR HP. apply prop_sprop_rel_intro.
  - intros H b. exact (prop_to_sprop _ _ (HP _ _ (HR b)) (H (toR b))).
  - intro H. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (HP _ _ (HL a)) (H (toL a))).
Qed.

Lemma jf_imp {P P' : Prop} {Q Q' : SProp} :
  PropSPropRel P Q -> PropSPropRel P' Q' -> PropSPropRel (P -> P') (Q -> Q').
Proof.
  intros H H'. apply prop_sprop_rel_intro.
  - intros f q. exact (prop_to_sprop _ _ H' (f (sprop_to_prop _ _ H q))).
  - intro f. apply strictly_inhabits. intro p. exact (sprop_to_prop _ _ H' (f (prop_to_sprop _ _ H p))).
Qed.

Lemma jf_and {P P' : Prop} {Q Q' : SProp} :
  PropSPropRel P Q -> PropSPropRel P' Q' -> PropSPropRel (P /\ P') (Lean.And Q Q').
Proof.
  intros H H'. apply prop_sprop_rel_intro.
  - intros [p p']. exact (Lean.And_intro _ _ (prop_to_sprop _ _ H p) (prop_to_sprop _ _ H' p')).
  - intros [q q']. apply strictly_inhabits. exact (conj (sprop_to_prop _ _ H q) (sprop_to_prop _ _ H' q')).
Qed.

Lemma jf_forall_nat (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall n, PR n) (forall n, PL n).
Proof.
  apply (jf_forall_cover SubNatRel sub_nat_to_imported sub_nat_to_rocq).
  - exact sub_nat_rel_canonical.
  - intro n. exact (sub_nat_imported_roundtrip n).
Qed.

Lemma jf_forall_task (PR : T.concrete_task -> Prop) (PL : LT -> SProp) :
  (forall tR tL, ItTaskRel tR tL -> PropSPropRel (PR tR) (PL tL)) ->
  PropSPropRel (forall t, PR t) (forall t, PL t).
Proof. apply (jf_forall_cover ItTaskRel it_task_export it_task_import PR PL concrete_task_source_total concrete_task_target_total). Qed.

Lemma jf_forall_job (PR : T.concrete_job -> Prop) (PL : LJ -> SProp) :
  (forall jR jL, ItJobRel jR jL -> PropSPropRel (PR jR) (PL jL)) ->
  PropSPropRel (forall j, PR j) (forall j, PL j).
Proof. apply (jf_forall_cover ItJobRel it_job_export it_job_import PR PL concrete_job_source_total concrete_job_target_total). Qed.

(** ** Equality types on the compiled concrete types (transported along the accepted import maps) *)

Lemma jf_task_cancel : cancel it_task_import it_task_export.
Proof. move=> b. exact (imported_eq_to_coq_eq _ _ (it_task_target_roundtrip b)). Qed.
Lemma jf_job_cancel : cancel it_job_import it_job_export.
Proof. move=> b. exact (imported_eq_to_coq_eq _ _ (it_job_target_roundtrip b)). Qed.

HB.instance Definition _ := Equality.copy I.Prosa_Implementation_Definitions_Task_concrete_task (can_type jf_task_cancel).
HB.instance Definition _ := Equality.copy I.Prosa_Implementation_Definitions_Task_concrete_job (can_type jf_job_cancel).

Lemma jf_task_export_inj : injective it_task_export.
Proof. exact (can_inj it_task_source_roundtrip). Qed.
Lemma jf_job_export_inj : injective it_job_export.
Proof. exact (can_inj it_job_source_roundtrip). Qed.

(** ** Task and job lists *)

Fixpoint jf_tasks_export (xs : seq T.concrete_task) : I.List_inst1 LT :=
  match xs with
  | [::] => I.List_nil_inst1 _
  | x :: tail => I.List_cons_inst1 _ (it_task_export x) (jf_tasks_export tail)
  end.

Definition JfTaskListRel (xsR : seq T.concrete_task) (xsL : I.List_inst1 LT) : SProp :=
  Lean.eq (jf_tasks_export xsR) xsL.

Fixpoint jf_tasks_import (xs : I.List_inst1 LT) : seq T.concrete_task :=
  match xs with
  | I.List_nil_inst1 => [::]
  | I.List_cons_inst1 x tail => it_task_import x :: jf_tasks_import tail
  end.

Fixpoint jf_tasks_target_roundtrip xs : JfTaskListRel (jf_tasks_import xs) xs :=
  match xs with
  | I.List_nil_inst1 => @Lean.eq_refl _ _
  | I.List_cons_inst1 x tail =>
      sub_imported_eq_congr2 (I.List_cons_inst1 _) _ _ _ _ (it_task_target_roundtrip x)
        (jf_tasks_target_roundtrip tail)
  end.

Lemma jf_forall_tasks (PR : seq T.concrete_task -> Prop) (PL : I.List_inst1 LT -> SProp) :
  (forall xsR xsL, JfTaskListRel xsR xsL -> PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (forall xs, PR xs) (forall xs, PL xs).
Proof.
  apply (jf_forall_cover JfTaskListRel jf_tasks_export jf_tasks_import).
  - intro xs. exact (@Lean.eq_refl _ _).
  - exact jf_tasks_target_roundtrip.
Qed.

Fixpoint jf_tasks_ar (xs : seq T.concrete_task) :
    Lean.eq (ar_list_to_imported (map it_task_export xs)) (jf_tasks_export xs) :=
  match xs with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => sub_imported_eq_congr (I.List_cons_inst1 LT (it_task_export x)) _ _ (jf_tasks_ar tail)
  end.

Fixpoint jf_jobs_ar (xs : seq T.concrete_job) :
    Lean.eq (ar_list_to_imported (map it_job_export xs)) (jc_jobs_export xs) :=
  match xs with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => sub_imported_eq_congr (I.List_cons_inst1 LJ (it_job_export x)) _ _ (jf_jobs_ar tail)
  end.

Lemma jf_tasks_arlist xsR xsL : JfTaskListRel xsR xsL -> ArListRel (map it_task_export xsR) xsL.
Proof. intro H. exact (sub_imported_eq_trans _ _ _ (jf_tasks_ar xsR) H). Qed.

Lemma jf_jobs_arlist xsR xsL : JcJobListRel xsR xsL -> ArListRel (map it_job_export xsR) xsL.
Proof. intro H. exact (sub_imported_eq_trans _ _ _ (jf_jobs_ar xsR) H). Qed.

(** Uniqueness and membership through the injective export maps. *)

Lemma jf_tasks_uniq xsR xsL : JfTaskListRel xsR xsL ->
  PropSPropRel (uniq xsR) (I.List_Nodup_inst1 LT xsL).
Proof.
  intro H. rewrite -(map_inj_uniq jf_task_export_inj).
  exact (ar_uniq_correspondence LT _ _ (jf_tasks_arlist _ _ H)).
Qed.

Lemma jf_jobs_uniq xsR xsL : JcJobListRel xsR xsL ->
  PropSPropRel (uniq xsR) (I.List_Nodup_inst1 LJ xsL).
Proof.
  intro H. rewrite -(map_inj_uniq jf_job_export_inj).
  exact (ar_uniq_correspondence LJ _ _ (jf_jobs_arlist _ _ H)).
Qed.

Lemma jf_task_mem_decide tR tL xsR xsL (d : I.Decidable (ar_target_mem tL xsL)) :
  ItTaskRel tR tL -> JfTaskListRel xsR xsL ->
  ArBoolRel (tR \in xsR) (I.Decidable_decide (ar_target_mem tL xsL) d).
Proof.
  intros Ht Hxs. apply ar_decide_bool_correspondence.
  rewrite -(mem_map jf_task_export_inj).
  have E : Logic.eq (it_task_export tR) tL := imported_eq_to_coq_eq _ _ Ht.
  rewrite E.
  exact (ar_membership_correspondence LT tL _ _ (jf_tasks_arlist _ _ Hxs)).
Qed.

Lemma jf_job_mem_decide jR jL xsR xsL (d : I.Decidable (ar_target_mem jL xsL)) :
  ItJobRel jR jL -> JcJobListRel xsR xsL ->
  ArBoolRel (jR \in xsR) (I.Decidable_decide (ar_target_mem jL xsL) d).
Proof.
  intros Hj Hxs. apply ar_decide_bool_correspondence.
  rewrite -(mem_map jf_job_export_inj).
  have E : Logic.eq (it_job_export jR) jL := imported_eq_to_coq_eq _ _ Hj.
  rewrite E.
  exact (ar_membership_correspondence LJ jL _ _ (jf_jobs_arlist _ _ Hxs)).
Qed.

(** Job-list length. *)

Fixpoint jf_jobs_length (xs : seq T.concrete_job) :
    SubNatRel (size xs) (I.List_length_inst1 LJ (jc_jobs_export xs)) :=
  match xs with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => sub_imported_eq_congr Lean.Nat_succ _ _ (jf_jobs_length tail)
  end.

Lemma jf_jobs_length_rel xsR xsL : JcJobListRel xsR xsL ->
  SubNatRel (size xsR) (I.List_length_inst1 LJ xsL).
Proof.
  intro H. exact (sub_imported_eq_trans _ _ _ (jf_jobs_length xsR)
    (sub_imported_eq_congr (I.List_length_inst1 LJ) _ _ H)).
Qed.

(** ** The maximal arrival sequence over the two concrete task types (task-relational form of the accepted
    definition certificates; the Nat-list layer is the replayed accepted one) *)

Lemma jf_max_arrivals_rel tR tL : ItTaskRel tR tL ->
  SvcNatFunRel (@prosa.model.task.arrival.curves.max_arrivals _ T.ConcreteMaxArrivals tR)
    (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals_inst1 LT jf_dT jf_cL tL).
Proof. intros Ht nR nL Hn. exact (ConcreteMaxArrivals_correspondence tR tL nR nL Ht Hn). Qed.

Theorem jf_jobs_remaining_rel tR tL (Htk : ItTaskRel tR tL) xsR xsL :
  SvcNatListRel xsR xsL ->
  MsOptRel (@MAS.jobs_remaining _ T.ConcreteMaxArrivals tR xsR)
    (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_jobs_remaining_inst1 LT jf_dT jf_cL tL xsL).
Proof.
  intro Hx.
  unfold MAS.jobs_remaining.
  cbn [I.Prosa_Implementation_Definitions_MaximalArrivalSequence_jobs_remaining_inst1].
  apply ms_supremum_related.
  apply svc_map_related.
  - intros dR dL Hd.
    exact (svc_target_sub_related _ _ _ _ (jf_max_arrivals_rel tR tL Htk _ _ (ms_succ_related _ _ Hd))
      (suffix_sum_correspondence xsR xsL dR dL Hx Hd)).
  - exact (svc_range_related _ _ _ _ (sub_nat_rel_canonical O) (ms_succ_related _ _ (ms_size_related xsR xsL Hx))).
Qed.

Theorem jf_next_max_arrival_rel tR tL (Htk : ItTaskRel tR tL) xsR xsL :
  SvcNatListRel xsR xsL ->
  SubNatRel (@MAS.next_max_arrival _ T.ConcreteMaxArrivals tR xsR)
    (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival_inst1 LT jf_dT jf_cL tL xsL).
Proof.
  intro Hx.
  unfold MAS.next_max_arrival.
  cbn [I.Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival_inst1].
  have Hj := jf_jobs_remaining_rel tR tL Htk xsR xsL Hx.
  refine (ms_lean_transport (fun o => SubNatRel _
    (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival_match_1
      (fun _ : I.Option_inst1 Lean.Nat => Lean.Nat) o
      (fun _ : I.Unit => I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals_inst1 LT jf_dT jf_cL tL
        (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Time_duration 1 (I.instOfNatNat 1)))
      (fun a : Lean.Nat => a))) _ _ Hj _).
  destruct (@MAS.jobs_remaining _ T.ConcreteMaxArrivals tR xsR) as [n|].
  - exact (sub_nat_rel_canonical n).
  - exact (jf_max_arrivals_rel tR tL Htk (S O) _ (sub_nat_rel_canonical (S O))).
Qed.

Theorem jf_extend_arrival_prefix_rel tR tL (Htk : ItTaskRel tR tL) xsR xsL :
  SvcNatListRel xsR xsL ->
  SvcNatListRel (@MAS.extend_arrival_prefix _ T.ConcreteMaxArrivals tR xsR)
    (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_extend_arrival_prefix_inst1 LT jf_dT jf_cL tL xsL).
Proof.
  intro Hx.
  unfold MAS.extend_arrival_prefix.
  cbn [I.Prosa_Implementation_Definitions_MaximalArrivalSequence_extend_arrival_prefix_inst1].
  have Hn := jf_next_max_arrival_rel tR tL Htk xsR xsL Hx.
  refine (ms_lean_transport (fun l => SvcNatListRel _
    (I.HAppend_hAppend_inst7 (I.List_inst1 Lean.Nat) (I.List_inst1 Lean.Nat) (I.List_inst1 Lean.Nat)
      (I.instHAppendOfAppend_inst1 (I.List_inst1 Lean.Nat) (I.List_instAppend_inst1 Lean.Nat)) l
      (I.List_cons_inst1 Lean.Nat
        (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival_inst1 LT jf_dT jf_cL tL xsL)
        (I.List_nil_inst1 Lean.Nat)))) _ _ Hx _).
  refine (ms_lean_transport (fun v => SvcNatListRel _
    (I.HAppend_hAppend_inst7 (I.List_inst1 Lean.Nat) (I.List_inst1 Lean.Nat) (I.List_inst1 Lean.Nat)
      (I.instHAppendOfAppend_inst1 (I.List_inst1 Lean.Nat) (I.List_instAppend_inst1 Lean.Nat))
      (svc_nat_list_to_imported xsR)
      (I.List_cons_inst1 Lean.Nat v (I.List_nil_inst1 Lean.Nat)))) _ _ Hn _).
  exact (ms_append_single_canonical xsR _).
Qed.

Theorem jf_maximal_arrival_prefix_rel tR tL (Htk : ItTaskRel tR tL) nR nL :
  SubNatRel nR nL ->
  SvcNatListRel (@MAS.maximal_arrival_prefix _ T.ConcreteMaxArrivals tR nR)
    (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix_inst1 LT jf_dT jf_cL tL nL).
Proof.
  intro Hn.
  unfold MAS.maximal_arrival_prefix.
  cbn [I.Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix_inst1].
  refine (ms_lean_transport (fun m => SvcNatListRel _
    (I.Nat_repeat_inst1 (I.List_inst1 Lean.Nat)
      (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_extend_arrival_prefix_inst1 LT jf_dT jf_cL tL)
      m (I.List_nil_inst1 Lean.Nat))) _ _ (ms_succ_related _ _ Hn) _).
  exact (ms_repeat_related _ _ (fun xsR xsL Hx => jf_extend_arrival_prefix_rel tR tL Htk xsR xsL Hx) nR.+1).
Qed.

Theorem jf_max_arrivals_at_rel tR tL (Htk : ItTaskRel tR tL) nR nL :
  SubNatRel nR nL ->
  SubNatRel (@MAS.max_arrivals_at _ T.ConcreteMaxArrivals tR nR)
    (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_max_arrivals_at_inst1 LT jf_dT jf_cL tL nL).
Proof.
  intro Hn.
  unfold MAS.max_arrivals_at.
  cbn [I.Prosa_Implementation_Definitions_MaximalArrivalSequence_max_arrivals_at_inst1].
  exact (ms_nth_related _ _ _ _ (jf_maximal_arrival_prefix_rel tR tL Htk nR nL Hn) Hn).
Qed.

(** The concrete arrival sequence of the job generator: job lists by the canonical map. *)

Definition jf_target_append (a b : I.List_inst1 LJ) : I.List_inst1 LJ :=
  I.HAppend_hAppend_inst7 (I.List_inst1 LJ) (I.List_inst1 LJ) (I.List_inst1 LJ)
    (I.instHAppendOfAppend_inst1 (I.List_inst1 LJ) (I.List_instAppend_inst1 LJ)) a b.

Fixpoint jf_jobs_append (a b : seq T.concrete_job) :
    Lean.eq (jc_jobs_export (a ++ b)) (jf_target_append (jc_jobs_export a) (jc_jobs_export b)) :=
  match a with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => sub_imported_eq_congr (I.List_cons_inst1 LJ (it_job_export x)) _ _ (jf_jobs_append tail b)
  end.

Lemma jf_bigcat_tasks (FR : T.concrete_task -> seq T.concrete_job) (FL : LT -> I.List_inst1 LJ) :
  (forall tR, JcJobListRel (FR tR) (FL (it_task_export tR))) ->
  forall xs : seq T.concrete_task,
  JcJobListRel (\cat_(x <- xs) FR x) (I.Prosa_Util_Bigcat_bigCatSeqAll_inst3 LT LJ (jf_tasks_export xs) FL).
Proof.
  intros HF xs. induction xs as [|x xs IH].
  - rewrite big_nil. exact (@Lean.eq_refl _ _).
  - rewrite big_cons. unfold JcJobListRel in IH |- *.
    refine (sub_imported_eq_trans _ _ _ (jf_jobs_append (FR x) _) _).
    exact (sub_imported_eq_congr2 jf_target_append _ _ _ _ (HF x) IH).
Qed.

Definition jf_target_arr_seq (tsL : I.List_inst1 LT) :=
  I.Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence_inst3 LT jf_dT
    I.Prosa_Implementation_Definitions_JobConstructor_Job jf_dJ jf_cL
    I.Prosa_Implementation_Definitions_JobConstructor_generate_jobs_at tsL.

Lemma jf_arrivals_at_rel tsR tsL tR tL : JfTaskListRel tsR tsL -> SubNatRel tR tL ->
  JcJobListRel (prosa.behavior.arrival_sequence.arrivals_at
      (MAS.concrete_arrival_sequence JC.generate_jobs_at tsR) tR)
    (I.Prosa_Behavior_Arrival_sequence_arrivals_at_inst1 I.Prosa_Implementation_Definitions_JobConstructor_Job jf_dJ
      (jf_target_arr_seq tsL) tL).
Proof.
  intros Hts Ht. destruct Hts. destruct Ht.
  unfold prosa.behavior.arrival_sequence.arrivals_at, MAS.concrete_arrival_sequence, jf_target_arr_seq.
  cbn [I.Prosa_Behavior_Arrival_sequence_arrivals_at_inst1
    I.Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence_inst3].
  apply jf_bigcat_tasks. intro x.
  exact (generate_jobs_at_correspondence x (it_task_export x) _ _ tR _ (concrete_task_source_total x)
    (jf_max_arrivals_at_rel x _ (concrete_task_source_total x) tR _ (sub_nat_rel_canonical tR))
    (sub_nat_rel_canonical tR)).
Qed.

(** The half-open concatenation of [arrivals_between] (the accepted [bigCat] relations of
    ArrivalsSeqOperations.v, at the concrete job lists and this export's concrete-job [bigCat] equations). *)

Definition JfJobFamilyRel (fR : nat -> seq T.concrete_job) (fL : Lean.Nat -> I.List_inst1 LJ) : SProp :=
  forall nR nL, SubNatRel nR nL -> JcJobListRel (fR nR) (fL nL).

Lemma jf_bigcat_delta (fR : nat -> seq T.concrete_job) (fL : Lean.Nat -> I.List_inst1 LJ) (m d : nat) :
  JfJobFamilyRel fR fL ->
  JcJobListRel (\cat_(m <= i < m + d) fR i)
    (I.Prosa_Util_Notation_bigCat_inst1 LJ (sub_nat_to_imported m)
      (Lean.Nat_add (sub_nat_to_imported m) (sub_nat_to_imported d)) fL).
Proof.
  intro Hf. induction d as [|d IH].
  - rewrite addn0 big_geq //.
    unfold JcJobListRel. cbn.
    exact (sub_imported_eq_sym _ _
      (I.Prosa_Validation_FactsJobConstructorInterface_production_bigCat_job_same (sub_nat_to_imported m) fL)).
  - rewrite addnS big_nat_recr; try exact (leq_addr d m).
    have Happ : JcJobListRel (\cat_(m <= i < m + d) fR i ++ fR (m + d))
        (jf_target_append
          (I.Prosa_Util_Notation_bigCat_inst1 LJ (sub_nat_to_imported m)
            (Lean.Nat_add (sub_nat_to_imported m) (sub_nat_to_imported d)) fL)
          (fL (Lean.Nat_add (sub_nat_to_imported m) (sub_nat_to_imported d)))) :=
      sub_imported_eq_trans _ _ _ (jf_jobs_append _ _)
        (sub_imported_eq_congr2 jf_target_append _ _ _ _ IH
          (Hf (m + d) _ (sub_add_correspondence m (sub_nat_to_imported m) d (sub_nat_to_imported d)
            (sub_nat_rel_canonical m) (sub_nat_rel_canonical d)))).
    unfold JcJobListRel in Happ |- *.
    exact (sub_imported_eq_trans _ _ _ Happ
      (sub_imported_eq_sym _ _
        (I.Prosa_Validation_FactsJobConstructorInterface_production_bigCat_job_add_succ
          (sub_nat_to_imported m) (sub_nat_to_imported d) fL))).
Qed.

Lemma jf_bigcat_canonical (fR : nat -> seq T.concrete_job) (fL : Lean.Nat -> I.List_inst1 LJ) (m n : nat) :
  JfJobFamilyRel fR fL ->
  JcJobListRel (\cat_(m <= i < n) fR i)
    (I.Prosa_Util_Notation_bigCat_inst1 LJ (sub_nat_to_imported m) (sub_nat_to_imported n) fL).
Proof.
  intro Hf. unfold JcJobListRel.
  apply coq_eq_to_imported_eq.
  case Hmn: (m <= n)%N.
  - have Hn : m + (n - m) = n by rewrite addnC subnK.
    rewrite -Hn.
    have HdeltaP := imported_eq_to_coq_eq _ _ (jf_bigcat_delta fR fL m (n - m) Hf).
    etransitivity; first exact HdeltaP.
    apply imported_eq_to_coq_eq.
    exact (sub_imported_eq_congr
      (fun upper => I.Prosa_Util_Notation_bigCat_inst1 LJ (sub_nat_to_imported m) upper fL) _ _
      (sub_imported_eq_sym _ _
        (sub_add_correspondence m (sub_nat_to_imported m) (n - m) (sub_nat_to_imported (n - m))
          (sub_nat_rel_canonical m) (sub_nat_rel_canonical (n - m))))).
  - have Hlt : (n < m)%N by rewrite ltnNge Hmn.
    have Hnm : (n <= m)%N := ltnW Hlt.
    rewrite big_geq //.
    have HleL := prop_to_sprop _ _
      (sub_nat_le_correspondence n (sub_nat_to_imported n) m (sub_nat_to_imported m)
        (sub_nat_rel_canonical n) (sub_nat_rel_canonical m)) Hnm.
    apply imported_eq_to_coq_eq.
    exact (sub_imported_eq_sym _ _
      (I.Prosa_Validation_FactsJobConstructorInterface_production_bigCat_job_of_le
        (sub_nat_to_imported m) (sub_nat_to_imported n) fL HleL)).
Qed.

Lemma jf_arrivals_between_rel tsR tsL t1R t1L t2R t2L :
  JfTaskListRel tsR tsL -> SubNatRel t1R t1L -> SubNatRel t2R t2L ->
  JcJobListRel (prosa.behavior.arrival_sequence.arrivals_between
      (MAS.concrete_arrival_sequence JC.generate_jobs_at tsR) t1R t2R)
    (I.Prosa_Behavior_Arrival_sequence_arrivals_between_inst1 I.Prosa_Implementation_Definitions_JobConstructor_Job
      jf_dJ (jf_target_arr_seq tsL) t1L t2L).
Proof.
  intros Hts H1 H2. destruct H1. destruct H2.
  unfold prosa.behavior.arrival_sequence.arrivals_between.
  cbn [I.Prosa_Behavior_Arrival_sequence_arrivals_between_inst1].
  exact (jf_bigcat_canonical _ _ t1R t2R (fun nR nL Hn => jf_arrivals_at_rel tsR tsL nR nL Hts Hn)).
Qed.

(** ** Statement correspondences *)

Ltac type_of_term t := let T := type of t in exact T.


Definition src_job_generation_valid_number : Prop := S.statement_job_generation_valid_number.
Definition tgt_job_generation_valid_number : SProp :=
  ltac:(type_of_term I.Prosa_Implementation_Facts_JobConstructor_job_generation_valid_number).

Theorem job_generation_valid_number_correspondence :
  PropSPropRel src_job_generation_valid_number tgt_job_generation_valid_number.
Proof.
  unfold src_job_generation_valid_number, tgt_job_generation_valid_number, S.statement_job_generation_valid_number.
  apply jf_forall_tasks => tsR tsL Hts.
  apply jf_forall_task => tR tL Ht.
  apply jf_forall_nat => nR nL Hn.
  apply jf_forall_nat => iR iL Hi.
  apply jf_imp.
  - exact (ar_bool_truth_correspondence _ _ (jf_task_mem_decide tR tL tsR tsL _ Ht Hts)).
  - exact (sub_nat_eq_correspondence _ _ _ _
      (jf_jobs_length_rel _ _ (generate_jobs_at_correspondence tR tL nR nL iR iL Ht Hn Hi)) Hn).
Qed.

Definition src_generate_jobs_at_unique : Prop := S.statement_generate_jobs_at_unique.
Definition tgt_generate_jobs_at_unique : SProp :=
  ltac:(type_of_term I.Prosa_Implementation_Facts_JobConstructor_generate_jobs_at_unique).

Theorem generate_jobs_at_unique_correspondence :
  PropSPropRel src_generate_jobs_at_unique tgt_generate_jobs_at_unique.
Proof.
  unfold src_generate_jobs_at_unique, tgt_generate_jobs_at_unique, S.statement_generate_jobs_at_unique.
  apply jf_forall_task => tR tL Ht.
  apply jf_forall_nat => nR nL Hn.
  apply jf_forall_nat => iR iL Hi.
  exact (jf_jobs_uniq _ _ (generate_jobs_at_correspondence tR tL nR nL iR iL Ht Hn Hi)).
Qed.

Definition src_job_arrival_consistent : Prop := S.statement_job_arrival_consistent.
Definition tgt_job_arrival_consistent : SProp :=
  ltac:(type_of_term I.Prosa_Implementation_Facts_JobConstructor_job_arrival_consistent).

Theorem job_arrival_consistent_correspondence :
  PropSPropRel src_job_arrival_consistent tgt_job_arrival_consistent.
Proof.
  unfold src_job_arrival_consistent, tgt_job_arrival_consistent, S.statement_job_arrival_consistent.
  apply jf_forall_tasks => tsR tsL Hts.
  apply jf_forall_job => jR jL Hj.
  apply jf_forall_nat => tR tL Ht.
  apply jf_imp.
  - exact (ar_bool_truth_correspondence _ _
      (jf_job_mem_decide jR jL _ _ _ Hj (jf_arrivals_at_rel tsR tsL tR tL Hts Ht))).
  - exact (sub_nat_eq_correspondence _ _ _ _ (it_job_arrival jR jL Hj) Ht).
Qed.

Definition src_arrivals_at_unique : Prop := S.statement_arrivals_at_unique.
Definition tgt_arrivals_at_unique : SProp :=
  ltac:(type_of_term I.Prosa_Implementation_Facts_JobConstructor_arrivals_at_unique).

Theorem arrivals_at_unique_correspondence :
  PropSPropRel src_arrivals_at_unique tgt_arrivals_at_unique.
Proof.
  unfold src_arrivals_at_unique, tgt_arrivals_at_unique, S.statement_arrivals_at_unique.
  apply jf_forall_tasks => tsR tsL Hts.
  apply jf_imp; first exact (jf_tasks_uniq _ _ Hts).
  apply jf_forall_nat => tR tL Ht.
  exact (jf_jobs_uniq _ _ (jf_arrivals_at_rel tsR tsL tR tL Hts Ht)).
Qed.

Definition src_job_generation_valid_jobs : Prop := S.statement_job_generation_valid_jobs.
Definition tgt_job_generation_valid_jobs : SProp :=
  ltac:(type_of_term I.Prosa_Implementation_Facts_JobConstructor_job_generation_valid_jobs).

Theorem job_generation_valid_jobs_correspondence :
  PropSPropRel src_job_generation_valid_jobs tgt_job_generation_valid_jobs.
Proof.
  unfold src_job_generation_valid_jobs, tgt_job_generation_valid_jobs, S.statement_job_generation_valid_jobs.
  apply jf_forall_task => tR tL Ht.
  apply jf_forall_nat => nR nL Hn.
  apply jf_forall_nat => iR iL Hi.
  apply jf_forall_job => jR jL Hj.
  apply jf_imp.
  - exact (ar_bool_truth_correspondence _ _
      (jf_job_mem_decide jR jL _ _ _ Hj (generate_jobs_at_correspondence tR tL nR nL iR iL Ht Hn Hi))).
  - apply jf_and; first exact (it_task_equality _ _ _ _ (it_job_task jR jL Hj) Ht).
    apply jf_and; first exact (sub_nat_eq_correspondence _ _ _ _ (it_job_arrival jR jL Hj) Hi).
    exact (sub_nat_le_correspondence _ _ _ _ (it_job_cost jR jL Hj) (it_task_cost tR tL Ht)).
Qed.

Definition src_arrivals_between_unique : Prop := S.statement_arrivals_between_unique.
Definition tgt_arrivals_between_unique : SProp :=
  ltac:(type_of_term I.Prosa_Implementation_Facts_JobConstructor_arrivals_between_unique).

Theorem arrivals_between_unique_correspondence :
  PropSPropRel src_arrivals_between_unique tgt_arrivals_between_unique.
Proof.
  unfold src_arrivals_between_unique, tgt_arrivals_between_unique, S.statement_arrivals_between_unique.
  apply jf_forall_tasks => tsR tsL Hts.
  apply jf_imp; first exact (jf_tasks_uniq _ _ Hts).
  apply jf_forall_nat => t1R t1L H1.
  apply jf_forall_nat => t2R t2L H2.
  exact (jf_jobs_uniq _ _ (jf_arrivals_between_rel tsR tsL t1R t1L t2R t2L Hts H1 H2)).
Qed.
