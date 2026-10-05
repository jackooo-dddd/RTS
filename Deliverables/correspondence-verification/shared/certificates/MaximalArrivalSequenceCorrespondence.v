From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import implementation.definitions.maximal_arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedMaximalArrivalSequence ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations.

Module I := ImportedMaximalArrivalSequence.

(** Definition certificates for
    [implementation/definitions/maximal_arrival_sequence.v]: for related
    inputs (arrival prefixes as Nat lists, task, instants, the [MaxArrivals]
    curve, the job generator and the task list) the source definitions and
    the compiled Lean definitions produce related values.  Every input
    relation has witnesses in both directions. *)

Lemma ms_lean_transport {A : Type} (P : A -> SProp) (x y : A) : Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma ms_subnat_source_transport (aR bR : nat) (nL : Lean.Nat) :
  Logic.eq aR bR -> SubNatRel bR nL -> SubNatRel aR nL.
Proof. intros H. destruct H. exact (fun p => p). Qed.

(** ** Nat lists *)

Lemma ms_size_canonical (xs : seq nat) :
  SubNatRel (size xs) (I.List_length_inst1 Lean.Nat (svc_nat_list_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr Lean.Nat_succ _ _ IH).
Qed.

Lemma ms_size_related (xsR : seq nat) (xsL : I.List_inst1 Lean.Nat) :
  SvcNatListRel xsR xsL -> SubNatRel (size xsR) (I.List_length_inst1 Lean.Nat xsL).
Proof.
  intro H. exact (ms_lean_transport (fun l => SubNatRel (size xsR) (I.List_length_inst1 Lean.Nat l))
    _ _ H (ms_size_canonical xsR)).
Qed.

Lemma ms_nth_canonical (xs : seq nat) :
  forall n : nat,
  SubNatRel (nth O xs n)
    (I.List_getD_inst1 Lean.Nat (svc_nat_list_to_imported xs) (sub_nat_to_imported n) svc_target_zero).
Proof.
  induction xs as [|x xs IH]; intro n.
  - destruct n; exact (@Lean.eq_refl _ _).
  - destruct n as [|n].
    + exact (@Lean.eq_refl _ _).
    + exact (IH n).
Qed.

Lemma ms_nth_related (xsR : seq nat) (xsL : I.List_inst1 Lean.Nat) nR nL :
  SvcNatListRel xsR xsL -> SubNatRel nR nL ->
  SubNatRel (nth O xsR nR) (I.List_getD_inst1 Lean.Nat xsL nL svc_target_zero).
Proof.
  intros Hx Hn.
  refine (ms_lean_transport (fun l => SubNatRel (nth O xsR nR) (I.List_getD_inst1 Lean.Nat l nL svc_target_zero))
    _ _ Hx _).
  exact (ms_lean_transport (fun m => SubNatRel (nth O xsR nR)
    (I.List_getD_inst1 Lean.Nat (svc_nat_list_to_imported xsR) m svc_target_zero))
    _ _ Hn (ms_nth_canonical xsR nR)).
Qed.

Lemma ms_list_sum_fold (xs : I.List_inst1 Lean.Nat) :
  Lean.eq (I.List_sum_inst1 Lean.Nat I.instAddNat (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass) xs)
    (svc_target_list_fold_sum xs).
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (fun v => Lean.Nat_add x v) _ _ IH).
Qed.

(** [\sum_(m <= i < n) f i] versus [sumSeq (List.range' m (n - m)) f]. *)
Lemma ms_interval_sum_related (mR nR : nat) (mL nL : Lean.Nat)
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  SubNatRel mR mL -> SubNatRel nR nL -> SvcNatFunRel fR fL ->
  SubNatRel (\sum_(mR <= i < nR) fR i)
    (I.Prosa_Util_Sum_sumSeq_inst1 Lean.Nat (I.List_range' mL (svc_target_sub nL mL) svc_target_one) fL).
Proof.
  intros Hm Hn Hf.
  refine (sub_imported_eq_trans _ _ _ (svc_interval_sum_related mR nR mL nL fR fL Hm Hn Hf) _).
  exact (sub_imported_eq_sym _ _ (ms_list_sum_fold _)).
Qed.

Theorem suffix_sum_correspondence (xsR : seq nat) (xsL : I.List_inst1 Lean.Nat) nR nL :
  SvcNatListRel xsR xsL -> SubNatRel nR nL ->
  SubNatRel (@prosa.implementation.definitions.maximal_arrival_sequence.suffix_sum xsR nR)
    (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_suffix_sum xsL nL).
Proof.
  intros Hx Hn.
  unfold prosa.implementation.definitions.maximal_arrival_sequence.suffix_sum.
  cbn [I.Prosa_Implementation_Definitions_MaximalArrivalSequence_suffix_sum].
  have Hs := ms_size_related xsR xsL Hx.
  exact (ms_interval_sum_related _ _ _ _ _ _
    (svc_target_sub_related _ _ _ _ Hs Hn) Hs
    (fun tR tL Ht => ms_nth_related xsR xsL tR tL Hx Ht)).
Qed.

(** ** Options of Nat and [supremum leq] *)

Definition ms_opt_to_imported (o : option nat) : I.Option_inst1 Lean.Nat :=
  match o with
  | None => I.Option_none_inst1 Lean.Nat
  | Some x => I.Option_some_inst1 Lean.Nat (sub_nat_to_imported x)
  end.
Definition MsOptRel (oR : option nat) (oL : I.Option_inst1 Lean.Nat) : SProp :=
  Lean.eq (ms_opt_to_imported oR) oL.

Definition ms_target_le_bool (a b : Lean.Nat) : I.Bool :=
  I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat a b) (I.Nat_decLe a b).

Lemma ms_supremum_cons_target (a : Lean.Nat) (l : I.List_inst1 Lean.Nat) :
  Lean.eq (I.Prosa_Util_Supremum_supremum_inst1 Lean.Nat ms_target_le_bool (I.List_cons_inst1 Lean.Nat a l))
    (I.Prosa_Util_Supremum_choose_superior_inst1 Lean.Nat ms_target_le_bool a
      (I.Prosa_Util_Supremum_supremum_inst1 Lean.Nat ms_target_le_bool l)).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma ms_supremum_cons_source (x : nat) (xs : seq nat) :
  Logic.eq (@prosa.util.supremum.supremum nat leq (x :: xs))
    (prosa.util.supremum.choose_superior leq x (prosa.util.supremum.supremum leq xs)).
Proof. reflexivity. Qed.

Lemma ms_logic_eq_to_lean_eq {A : Type} (x y : A) : Logic.eq x y -> Lean.eq x y.
Proof. intros []. exact (@Lean.eq_refl _ _). Qed.

Lemma ms_choose_superior_some_target (a b : Lean.Nat) :
  Lean.eq (I.Prosa_Util_Supremum_choose_superior_inst1 Lean.Nat ms_target_le_bool a (I.Option_some_inst1 Lean.Nat b))
    (I.ite (I.Option_inst1 Lean.Nat) (Lean.eq (ms_target_le_bool a b) I.Bool_true)
      (I.instDecidableEqBool (ms_target_le_bool a b) I.Bool_true)
      (I.Option_some_inst1 Lean.Nat a) (I.Option_some_inst1 Lean.Nat b)).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma ms_choose_superior_related (x : nat) (o : option nat) :
  Lean.eq (ms_opt_to_imported (@prosa.util.supremum.choose_superior nat leq x o))
    (I.Prosa_Util_Supremum_choose_superior_inst1 Lean.Nat ms_target_le_bool (sub_nat_to_imported x)
      (ms_opt_to_imported o)).
Proof.
  destruct o as [y|].
  - refine (ms_lean_transport (fun v => Lean.eq _ v) _ _
      (sub_imported_eq_sym _ _ (ms_choose_superior_some_target (sub_nat_to_imported x) (sub_nat_to_imported y))) _).
    have Hb := svc_decide_le_related x (sub_nat_to_imported x) y (sub_nat_to_imported y)
      (sub_nat_rel_canonical x) (sub_nat_rel_canonical y).
    unfold SvcBoolRel in Hb.
    refine (ms_lean_transport (fun b => Lean.eq
      (ms_opt_to_imported (prosa.util.supremum.choose_superior leq x (Some y)))
      (I.ite (I.Option_inst1 Lean.Nat) (Lean.eq b I.Bool_true) (I.instDecidableEqBool b I.Bool_true)
        (I.Option_some_inst1 Lean.Nat (sub_nat_to_imported x))
        (I.Option_some_inst1 Lean.Nat (sub_nat_to_imported y)))) _ _ Hb _).
    change (Lean.eq (ms_opt_to_imported (if leq x y then Some x else Some y))
      (I.ite (I.Option_inst1 Lean.Nat) (Lean.eq (svc_bool_to_imported (leq x y)) I.Bool_true)
        (I.instDecidableEqBool (svc_bool_to_imported (leq x y)) I.Bool_true)
        (I.Option_some_inst1 Lean.Nat (sub_nat_to_imported x))
        (I.Option_some_inst1 Lean.Nat (sub_nat_to_imported y)))).
    destruct (leq x y); exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
Qed.

Lemma ms_supremum_canonical (xs : seq nat) :
  MsOptRel (@prosa.util.supremum.supremum nat leq xs)
    (I.Prosa_Util_Supremum_supremum_inst1 Lean.Nat ms_target_le_bool (svc_nat_list_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - unfold MsOptRel in IH |- *.
    refine (sub_imported_eq_trans _ _ _
      (ms_logic_eq_to_lean_eq _ _ (f_equal ms_opt_to_imported (ms_supremum_cons_source x xs))) _).
    refine (sub_imported_eq_trans _ _ _ (ms_choose_superior_related x _) _).
    refine (sub_imported_eq_trans _ _ _ _
      (sub_imported_eq_sym _ _ (ms_supremum_cons_target (sub_nat_to_imported x) (svc_nat_list_to_imported xs)))).
    exact (sub_imported_eq_congr
      (I.Prosa_Util_Supremum_choose_superior_inst1 Lean.Nat ms_target_le_bool (sub_nat_to_imported x)) _ _ IH).
Qed.

Lemma ms_supremum_related (xsR : seq nat) (xsL : I.List_inst1 Lean.Nat) :
  SvcNatListRel xsR xsL ->
  MsOptRel (@prosa.util.supremum.supremum nat leq xsR)
    (I.Prosa_Util_Supremum_supremum_inst1 Lean.Nat ms_target_le_bool xsL).
Proof.
  intro H. exact (ms_lean_transport (fun l => MsOptRel (prosa.util.supremum.supremum leq xsR)
    (I.Prosa_Util_Supremum_supremum_inst1 Lean.Nat ms_target_le_bool l)) _ _ H (ms_supremum_canonical xsR)).
Qed.

(** ** Appending a singleton, and iteration *)

Lemma ms_append_single_canonical (xs : seq nat) (v : nat) :
  SvcNatListRel (xs ++ [:: v])
    (I.HAppend_hAppend_inst7 (I.List_inst1 Lean.Nat) (I.List_inst1 Lean.Nat) (I.List_inst1 Lean.Nat)
      (I.instHAppendOfAppend_inst1 (I.List_inst1 Lean.Nat) (I.List_instAppend_inst1 Lean.Nat))
      (svc_nat_list_to_imported xs)
      (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported v) (I.List_nil_inst1 Lean.Nat))).
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported x)) _ _ IH).
Qed.

Lemma ms_repeat_related (fR : seq nat -> seq nat) (fL : I.List_inst1 Lean.Nat -> I.List_inst1 Lean.Nat) :
  (forall xsR xsL, SvcNatListRel xsR xsL -> SvcNatListRel (fR xsR) (fL xsL)) ->
  forall n : nat,
  SvcNatListRel (iter n fR [::])
    (I.Nat_repeat_inst1 (I.List_inst1 Lean.Nat) fL (sub_nat_to_imported n) (I.List_nil_inst1 Lean.Nat)).
Proof.
  intros Hf n. induction n as [|n IH].
  - exact (@Lean.eq_refl _ _).
  - exact (Hf _ _ IH).
Qed.

(** ** The curve class (input relation with two-way coverage) *)

Section Curve.
  Context (Task : eqType).
  Let dT := svc_decidable_eq Task.

  Definition MsMaxArrivalsRel (cR : prosa.model.task.arrival.curves.MaxArrivals Task)
      (cL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT) : SProp :=
    forall tsk, SvcNatFunRel (@prosa.model.task.arrival.curves.max_arrivals Task cR tsk)
      (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT cL tsk).

  Lemma MaxArrivals_source_total cR : MsMaxArrivalsRel cR
    (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_mk Task dT
      (fun tsk n => sub_nat_to_imported (cR tsk (sub_nat_to_rocq n)))).
  Proof.
    intros tsk nR nL Hn. unfold SubNatRel.
    have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ Hn).
    rewrite sub_nat_rocq_roundtrip in E.
    exact (ms_lean_transport (fun m => Lean.eq (sub_nat_to_imported (cR tsk nR)) (sub_nat_to_imported (cR tsk m)))
      _ _ (ms_logic_eq_to_lean_eq _ _ E) (@Lean.eq_refl _ _)).
  Qed.

  Lemma MaxArrivals_target_total cL : MsMaxArrivalsRel
    (fun tsk n => sub_nat_to_rocq
      (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT cL tsk (sub_nat_to_imported n))) cL.
  Proof.
    intros tsk nR nL Hn. unfold SubNatRel.
    exact (sub_imported_eq_trans _ _ _ (sub_nat_imported_roundtrip _)
      (sub_imported_eq_congr (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT cL tsk) _ _ Hn)).
  Qed.

  Variable cR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable cL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hc : MsMaxArrivalsRel cR cL.

  Lemma ms_succ_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL -> SubNatRel tR.+1 (svc_target_add tL svc_target_one).
  Proof.
    intro Ht. apply (ms_subnat_source_transport _ (tR + 1) _ (Logic.eq_sym (addn1 tR))).
    exact (svc_target_add_related _ _ _ _ Ht (sub_nat_rel_canonical 1)).
  Qed.

  Theorem jobs_remaining_correspondence (tsk : Task) xsR xsL :
    SvcNatListRel xsR xsL ->
    MsOptRel (@prosa.implementation.definitions.maximal_arrival_sequence.jobs_remaining Task cR tsk xsR)
      (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_jobs_remaining Task dT cL tsk xsL).
  Proof.
    intro Hx.
    unfold prosa.implementation.definitions.maximal_arrival_sequence.jobs_remaining.
    cbn [I.Prosa_Implementation_Definitions_MaximalArrivalSequence_jobs_remaining].
    apply ms_supremum_related.
    apply svc_map_related.
    - intros dR dL Hd.
      exact (svc_target_sub_related _ _ _ _ (Hc tsk _ _ (ms_succ_related _ _ Hd))
        (suffix_sum_correspondence xsR xsL dR dL Hx Hd)).
    - exact (svc_range_related _ _ _ _ (sub_nat_rel_canonical O) (ms_succ_related _ _ (ms_size_related xsR xsL Hx))).
  Qed.

  Theorem next_max_arrival_correspondence (tsk : Task) xsR xsL :
    SvcNatListRel xsR xsL ->
    SubNatRel (@prosa.implementation.definitions.maximal_arrival_sequence.next_max_arrival Task cR tsk xsR)
      (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival Task dT cL tsk xsL).
  Proof.
    intro Hx.
    unfold prosa.implementation.definitions.maximal_arrival_sequence.next_max_arrival.
    cbn [I.Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival].
    have Hj := jobs_remaining_correspondence tsk xsR xsL Hx.
    refine (ms_lean_transport (fun o => SubNatRel _
      (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival_match_1
        (fun _ : I.Option_inst1 Lean.Nat => Lean.Nat) o
        (fun _ : I.Unit => I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT cL tsk
          (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Time_duration 1 (I.instOfNatNat 1)))
        (fun a : Lean.Nat => a))) _ _ Hj _).
    destruct (prosa.implementation.definitions.maximal_arrival_sequence.jobs_remaining tsk xsR) as [n|].
    - exact (sub_nat_rel_canonical n).
    - exact (Hc tsk (S O) _ (sub_nat_rel_canonical (S O))).
  Qed.

  Theorem extend_arrival_prefix_correspondence (tsk : Task) xsR xsL :
    SvcNatListRel xsR xsL ->
    SvcNatListRel (@prosa.implementation.definitions.maximal_arrival_sequence.extend_arrival_prefix Task cR tsk xsR)
      (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_extend_arrival_prefix Task dT cL tsk xsL).
  Proof.
    intro Hx.
    unfold prosa.implementation.definitions.maximal_arrival_sequence.extend_arrival_prefix.
    cbn [I.Prosa_Implementation_Definitions_MaximalArrivalSequence_extend_arrival_prefix].
    have Hn := next_max_arrival_correspondence tsk xsR xsL Hx.
    refine (ms_lean_transport (fun l => SvcNatListRel _
      (I.HAppend_hAppend_inst7 (I.List_inst1 Lean.Nat) (I.List_inst1 Lean.Nat) (I.List_inst1 Lean.Nat)
        (I.instHAppendOfAppend_inst1 (I.List_inst1 Lean.Nat) (I.List_instAppend_inst1 Lean.Nat)) l
        (I.List_cons_inst1 Lean.Nat
          (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_next_max_arrival Task dT cL tsk xsL)
          (I.List_nil_inst1 Lean.Nat)))) _ _ Hx _).
    refine (ms_lean_transport (fun v => SvcNatListRel _
      (I.HAppend_hAppend_inst7 (I.List_inst1 Lean.Nat) (I.List_inst1 Lean.Nat) (I.List_inst1 Lean.Nat)
        (I.instHAppendOfAppend_inst1 (I.List_inst1 Lean.Nat) (I.List_instAppend_inst1 Lean.Nat))
        (svc_nat_list_to_imported xsR)
        (I.List_cons_inst1 Lean.Nat v (I.List_nil_inst1 Lean.Nat)))) _ _ Hn _).
    exact (ms_append_single_canonical xsR _).
  Qed.

  Theorem maximal_arrival_prefix_correspondence (tsk : Task) tR tL :
    SubNatRel tR tL ->
    SvcNatListRel (@prosa.implementation.definitions.maximal_arrival_sequence.maximal_arrival_prefix Task cR tsk tR)
      (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix Task dT cL tsk tL).
  Proof.
    intro Ht.
    unfold prosa.implementation.definitions.maximal_arrival_sequence.maximal_arrival_prefix.
    cbn [I.Prosa_Implementation_Definitions_MaximalArrivalSequence_maximal_arrival_prefix].
    refine (ms_lean_transport (fun m => SvcNatListRel _
      (I.Nat_repeat_inst1 (I.List_inst1 Lean.Nat)
        (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_extend_arrival_prefix Task dT cL tsk)
        m (I.List_nil_inst1 Lean.Nat))) _ _ (ms_succ_related _ _ Ht) _).
    exact (ms_repeat_related _ _ (fun xsR xsL Hx => extend_arrival_prefix_correspondence tsk xsR xsL Hx) tR.+1).
  Qed.

  Theorem max_arrivals_at_correspondence (tsk : Task) tR tL :
    SubNatRel tR tL ->
    SubNatRel (@prosa.implementation.definitions.maximal_arrival_sequence.max_arrivals_at Task cR tsk tR)
      (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_max_arrivals_at Task dT cL tsk tL).
  Proof.
    intro Ht.
    unfold prosa.implementation.definitions.maximal_arrival_sequence.max_arrivals_at.
    cbn [I.Prosa_Implementation_Definitions_MaximalArrivalSequence_max_arrivals_at].
    exact (ms_nth_related _ _ _ _ (maximal_arrival_prefix_correspondence tsk tR tL Ht) Ht).
  Qed.
End Curve.

(** ** Big concatenation over a task list ([\cat_(x <- s)] versus [bigCatSeqAll]) *)

Definition ms_target_append {U : Type} (a b : I.List U) : I.List U :=
  I.HAppend_hAppend (I.List U) (I.List U) (I.List U)
    (I.instHAppendOfAppend (I.List U) (I.List_instAppend U)) a b.

Lemma ms_append_canonical (U : Type) (a b : seq U) :
  Lean.eq (svc_list_to_imported (a ++ b)) (ms_target_append (svc_list_to_imported a) (svc_list_to_imported b)).
Proof.
  induction a as [|y a IH].
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr (I.List_cons U y) _ _ IH).
Qed.

Lemma ms_bigcat_as_foldr (T U : Type) (FR : T -> seq U) (xs : seq T) :
  Logic.eq (\big[cat/[::]]_(x <- xs) FR x) (foldr (fun x acc => FR x ++ acc) [::] xs).
Proof. elim: xs => [|x xs IH]; [by rewrite big_nil | by rewrite big_cons IH]. Qed.

Lemma ms_flatmap_canonical (T U : Type) (FR : T -> seq U) (FL : T -> I.List U) :
  (forall x, SvcListRel (FR x) (FL x)) ->
  forall xs : seq T,
  SvcListRel (foldr (fun x acc => FR x ++ acc) [::] xs) (I.List_flatMap T U FL (svc_list_to_imported xs)).
Proof.
  intros HF xs. induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - unfold SvcListRel in IH |- *.
    refine (sub_imported_eq_trans _ _ _ (ms_append_canonical U (FR x) _) _).
    exact (sub_imported_eq_congr2 (@ms_target_append U) _ _ _ _ (HF x) IH).
Qed.

Lemma ms_bigcat_related (T U : Type) (FR : T -> seq U) (FL : T -> I.List U) xsR xsL :
  (forall x, SvcListRel (FR x) (FL x)) -> SvcListRel xsR xsL ->
  SvcListRel (\big[cat/[::]]_(x <- xsR) FR x) (I.Prosa_Util_Bigcat_bigCatSeqAll T U xsL FL).
Proof.
  intros HF Hxs.
  refine (ms_lean_transport (fun l => SvcListRel (\big[cat/[::]]_(x <- xsR) FR x)
    (I.Prosa_Util_Bigcat_bigCatSeqAll T U l FL)) _ _ Hxs _).
  refine (ms_lean_transport (fun s => SvcListRel s
    (I.Prosa_Util_Bigcat_bigCatSeqAll T U (svc_list_to_imported xsR) FL)) _ _
    (sub_imported_eq_sym _ _ (ms_logic_eq_to_lean_eq _ _ (ms_bigcat_as_foldr T U FR xsR))) _).
  exact (ms_flatmap_canonical T U FR FL HF xsR).
Qed.

(** ** The concrete arrival sequence (inputs: the curve, the job generator
    and the task list, each with two-way coverage) *)

Section Concrete.
  Context (Task Job : eqType).
  Let dT := svc_decidable_eq Task.
  Let dJ := svc_decidable_eq Job.

  Definition MsGeneratorRel (gR : Task -> nat -> nat -> seq Job)
      (gL : Task -> Lean.Nat -> Lean.Nat -> I.List Job) : SProp :=
    forall tsk nR nL tR tL, SubNatRel nR nL -> SubNatRel tR tL ->
      SvcListRel (gR tsk nR tR) (gL tsk nL tL).

  Lemma ms_nat_input (nR : nat) (nL : Lean.Nat) :
    SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
  Proof.
    intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
    rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
  Qed.

  Lemma Generator_source_total gR : MsGeneratorRel gR
    (fun tsk nL tL => svc_list_to_imported (gR tsk (sub_nat_to_rocq nL) (sub_nat_to_rocq tL))).
  Proof.
    intros tsk nR nL tR tL Hn Ht. unfold SvcListRel.
    rewrite (ms_nat_input nR nL Hn) (ms_nat_input tR tL Ht). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma Generator_target_total gL : MsGeneratorRel
    (fun tsk n t => svc_list_to_rocq (gL tsk (sub_nat_to_imported n) (sub_nat_to_imported t))) gL.
  Proof.
    intros tsk nR nL tR tL Hn Ht. unfold SvcListRel.
    exact (sub_imported_eq_trans _ _ _ (svc_list_target_roundtrip _)
      (sub_imported_eq_congr2 (gL tsk) _ _ _ _ Hn Ht)).
  Qed.

  Variable cR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable cL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hc : MsMaxArrivalsRel Task cR cL.
  Variable gR : Task -> nat -> nat -> seq Job.
  Variable gL : Task -> Lean.Nat -> Lean.Nat -> I.List Job.
  Hypothesis Hg : MsGeneratorRel gR gL.

  Theorem concrete_arrival_sequence_correspondence tsR tsL tR tL :
    SvcListRel tsR tsL -> SubNatRel tR tL ->
    SvcListRel
      (@prosa.implementation.definitions.maximal_arrival_sequence.concrete_arrival_sequence Task Job cR gR tsR tR)
      (I.Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence
        Task dT Job dJ cL gL tsL tL).
  Proof.
    intros Hts Ht.
    unfold prosa.implementation.definitions.maximal_arrival_sequence.concrete_arrival_sequence.
    cbn [I.Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence].
    apply ms_bigcat_related; [|exact Hts].
    intro tsk.
    exact (Hg tsk _ _ _ _ (max_arrivals_at_correspondence Task cR cL Hc tsk tR tL Ht) Ht).
  Qed.
End Concrete.

(** ** Coverage of the Nat-list and task-list inputs *)

Fixpoint ms_nat_list_to_rocq (xs : I.List_inst1 Lean.Nat) : seq nat :=
  match xs with
  | I.List_nil_inst1 => [::]
  | I.List_cons_inst1 x tail => sub_nat_to_rocq x :: ms_nat_list_to_rocq tail
  end.

Lemma NatList_source_total (xs : seq nat) : SvcNatListRel xs (svc_nat_list_to_imported xs).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma NatList_target_total (xs : I.List_inst1 Lean.Nat) : SvcNatListRel (ms_nat_list_to_rocq xs) xs.
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr2 (I.List_cons_inst1 Lean.Nat) _ _ _ _ (sub_nat_imported_roundtrip x) IH).
Qed.

Lemma TaskList_source_total (T : Type) (xs : seq T) : SvcListRel xs (svc_list_to_imported xs).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma TaskList_target_total (T : Type) (xs : I.List T) : SvcListRel (svc_list_to_rocq xs) xs.
Proof. exact (svc_list_target_roundtrip xs). Qed.
