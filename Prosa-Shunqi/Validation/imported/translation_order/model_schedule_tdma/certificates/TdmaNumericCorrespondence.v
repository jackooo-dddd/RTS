From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop div.
From prosa Require Import model.schedule.tdma.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTdmaProjectedFull.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  TdmaBaseAdapter TdmaSeqsetAdapter TdmaPolicyAdapter
  TdmaValidityCorrespondence TdmaArithmeticAdapter.

Definition tdma_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedTdmaProjectedFull.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedTdmaProjectedFull.instHAdd_inst1 Lean.Nat
      ImportedTdmaProjectedFull.instAddNat) a b.

Lemma tdma_add_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (tdma_target_add aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (aR + bR) (sub_imported_add aL bL)).
  exact (sub_add_correspondence aR aL bR bL).
Qed.

Definition tdma_target_fold {T : Type} (f : T -> Lean.Nat)
    (xs : ImportedTdmaProjectedFull.List T) : Lean.Nat :=
  ImportedTdmaProjectedFull.List_foldr_inst2 T Lean.Nat
    (fun x n => tdma_target_add (f x) n) Lean.Nat_zero xs.

Fixpoint tdma_fold_canonical {T : Type}
    (fR : T -> nat) (fL : T -> Lean.Nat)
    (Hf : forall x, SubNatRel (fR x) (fL x)) (xs : seq T) :
  SubNatRel (foldr (fun x n => fR x + n) O xs)
    (tdma_target_fold fL (ar_list_to_imported xs)).
Proof.
  destruct xs as [|x xs].
  - exact (sub_nat_rel_canonical O).
  - exact (tdma_add_related (fR x) (fL x)
      (foldr (fun y n => fR y + n) O xs)
      (tdma_target_fold fL (ar_list_to_imported xs))
      (Hf x) (@tdma_fold_canonical T fR fL Hf xs)).
Defined.

Lemma tdma_fold_related {T : Type} (fR : T -> nat)
    (fL : T -> Lean.Nat) (xsR : seq T)
    (xsL : ImportedTdmaProjectedFull.List T) :
  (forall x, SubNatRel (fR x) (fL x)) -> ArListRel xsR xsL ->
  SubNatRel (foldr (fun x n => fR x + n) O xsR)
    (tdma_target_fold fL xsL).
Proof.
  intros Hf Hxs. unfold ArListRel in Hxs.
  exact (sub_imported_eq_trans _ _ _
    (@tdma_fold_canonical T fR fL Hf xsR)
    (sub_imported_eq_congr (tdma_target_fold fL) _ _ Hxs)).
Qed.

Lemma tdma_mathcomp_big_seq_as_fold {T : Type}
    (xs : seq T) (f : T -> nat) :
  Logic.eq (\sum_(x <- xs) f x)
    (foldr (fun x n => f x + n) O xs).
Proof.
  elim: xs => [|x xs IH].
  - rewrite big_nil. reflexivity.
  - rewrite big_cons /= IH. reflexivity.
Qed.

Lemma tdma_mathcomp_big_filtered_as_fold {T : Type}
    (xs : seq T) (P : T -> bool) (f : T -> nat) :
  Logic.eq (\sum_(x <- xs | P x) f x)
    (foldr (fun x n => f x + n) O [seq x <- xs | P x]).
Proof.
  elim: xs => [|x xs IH].
  - rewrite big_nil. reflexivity.
  - rewrite big_cons /= IH. case: (P x); reflexivity.
Qed.

Definition tdma_target_filter {T : Type}
    (P : T -> ImportedTdmaProjectedFull.Bool)
    (xs : ImportedTdmaProjectedFull.List T) :
    ImportedTdmaProjectedFull.List T :=
  ImportedTdmaProjectedFull.List_filter T P xs.

Lemma tdma_filter_nil {T : Type}
    (P : T -> ImportedTdmaProjectedFull.Bool) :
  Lean.eq
    (tdma_target_filter P (ImportedTdmaProjectedFull.List_nil T))
    (ImportedTdmaProjectedFull.List_nil T).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma tdma_filter_cons {T : Type}
    (P : T -> ImportedTdmaProjectedFull.Bool) (x : T)
    (xs : ImportedTdmaProjectedFull.List T) :
  Lean.eq
    (tdma_target_filter P (ImportedTdmaProjectedFull.List_cons T x xs))
    (match P x with
     | ImportedTdmaProjectedFull.Bool_true =>
         ImportedTdmaProjectedFull.List_cons T x (tdma_target_filter P xs)
     | ImportedTdmaProjectedFull.Bool_false => tdma_target_filter P xs
     end).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma tdma_bool_and_related aR aL bR bL :
  ArBoolRel aR aL -> ArBoolRel bR bL ->
  ArBoolRel (aR && bR) (ImportedTdmaProjectedFull.Bool_and aL bL).
Proof.
  intros Ha Hb. destruct aR, bR; cbn in *;
    destruct aL, bL; try exact (@Lean.eq_refl _ _);
    try exact (ar_false_elim _ (ar_false_ne_true Ha));
    try exact (ar_false_elim _ (ar_false_ne_true Hb));
    try exact (ar_false_elim _ (ar_false_ne_true
      (sub_imported_eq_sym _ _ Ha)));
    try exact (ar_false_elim _ (ar_false_ne_true
      (sub_imported_eq_sym _ _ Hb))).
Qed.

Definition tdma_target_ne (Task : eqType) (x y : Task) :
    ImportedTdmaProjectedFull.Bool :=
  ImportedTdmaProjectedFull.Decidable_decide
    (ImportedTdmaProjectedFull.Ne Task x y)
    (ImportedTdmaProjectedFull.instDecidableNot (Lean.eq x y)
      (ar_decidable_eq Task x y)).

Lemma tdma_ne_observation (Task : eqType) (x y : Task) :
  ArBoolRel (x != y) (tdma_target_ne Task x y).
Proof.
  unfold tdma_target_ne, ar_decidable_eq, ArBoolRel.
  destruct (@eqP Task x y); cbn; exact (@Lean.eq_refl _ _).
Qed.

Lemma tdma_filter_canonical {T : Type}
    (PR : T -> bool) (PL : T -> ImportedTdmaProjectedFull.Bool)
    (HP : forall x, ArBoolRel (PR x) (PL x)) (xs : seq T) :
  ArListRel [seq x <- xs | PR x]
    (tdma_target_filter PL (ar_list_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - unfold ArListRel. exact (sub_imported_eq_sym _ _ (tdma_filter_nil PL)).
  - unfold ArListRel in *.
    have Hpx := HP x.
    refine (sub_imported_eq_trans _ _ _ _
      (sub_imported_eq_sym _ _ (tdma_filter_cons PL x
        (ar_list_to_imported xs)))).
    destruct (PR x) eqn:Hpr; destruct (PL x) eqn:Hpl;
      cbn in *;
      rewrite Hpr;
      try exact (ar_false_elim _ (ar_false_ne_true Hpx));
      try exact (ar_false_elim _ (ar_false_ne_true
        (sub_imported_eq_sym _ _ Hpx))).
    + exact (sub_imported_eq_congr
        (ImportedTdmaProjectedFull.List_cons T x) _ _ IH).
    + exact IH.
Qed.

Lemma tdma_filter_related {T : Type}
    (PR : T -> bool) (PL : T -> ImportedTdmaProjectedFull.Bool)
    (xsR : seq T) (xsL : ImportedTdmaProjectedFull.List T) :
  (forall x, ArBoolRel (PR x) (PL x)) -> ArListRel xsR xsL ->
  ArListRel [seq x <- xsR | PR x] (tdma_target_filter PL xsL).
Proof.
  intros HP Hxs. unfold ArListRel in *.
  exact (sub_imported_eq_trans _ _ _
    (tdma_filter_canonical PR PL HP xsR)
    (sub_imported_eq_congr (tdma_target_filter PL) _ _ Hxs)).
Qed.

Section TdmaNumeric.
  Context (Task : eqType).
  Context (policyR : prosa.model.schedule.tdma.TDMAPolicy Task).
  Context (policyL : ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy
    Task (ar_decidable_eq Task)).
  Context (Hpolicy : TdmaPolicyRel Task policyR policyL).
  Context (tsR : @prosa.util.seqset.set Task).
  Context (tsL : ImportedTdmaProjectedFull.Prosa_Util_Seqset_set Task
    (ar_decidable_eq Task)).
  Context (Hts : RocqSeqSetRel Task tsR tsL).

  Theorem TDMA_cycle_correspondence :
    SubNatRel
      (@prosa.model.schedule.tdma.TDMA_cycle Task tsR policyR)
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMA_cycle
        Task (ar_decidable_eq Task) policyL tsL).
  Proof.
    rewrite /prosa.model.schedule.tdma.TDMA_cycle.
    rewrite (tdma_mathcomp_big_seq_as_fold _ _).
    change (SubNatRel
      (foldr (fun x n => @prosa.model.schedule.tdma.task_time_slot
        Task policyR x + n) O tsR)
      (tdma_target_fold
        (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot
          Task (ar_decidable_eq Task) policyL)
        (ImportedTdmaProjectedFull.Prosa_Util_Seqset_set_val
          Task (ar_decidable_eq Task) tsL))).
    apply tdma_fold_related.
    - exact (tdma_slot_related _ _ _ Hpolicy).
    - exact (tdma_set_list_related Task tsR tsL Hts).
  Qed.

  Definition tdma_source_offset_pred (tsk prev : Task) : bool :=
    @prosa.model.schedule.tdma.slot_order Task policyR prev tsk
      && (prev != tsk).

  Definition tdma_target_offset_pred (tsk prev : Task) :
      ImportedTdmaProjectedFull.Bool :=
    ImportedTdmaProjectedFull.Bool_and
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy_slot_order
        Task (ar_decidable_eq Task) policyL prev tsk)
      (tdma_target_ne Task prev tsk).

  Lemma tdma_offset_pred_related tsk prev :
    ArBoolRel (tdma_source_offset_pred tsk prev)
      (tdma_target_offset_pred tsk prev).
  Proof.
    apply tdma_bool_and_related.
    - exact (tdma_order_related _ _ _ Hpolicy prev tsk).
    - exact (tdma_ne_observation Task prev tsk).
  Qed.

  Theorem task_slot_offset_correspondence tsk :
    SubNatRel
      (@prosa.model.schedule.tdma.task_slot_offset Task tsR policyR tsk)
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_task_slot_offset
        Task (ar_decidable_eq Task) policyL tsL tsk).
  Proof.
    rewrite /prosa.model.schedule.tdma.task_slot_offset.
    rewrite (tdma_mathcomp_big_filtered_as_fold _ _ _).
    change (SubNatRel
      (foldr (fun x n => @prosa.model.schedule.tdma.task_time_slot
        Task policyR x + n) O
        [seq x <- tsR | tdma_source_offset_pred tsk x])
      (tdma_target_fold
        (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot
          Task (ar_decidable_eq Task) policyL)
        (tdma_target_filter (tdma_target_offset_pred tsk)
          (ImportedTdmaProjectedFull.Prosa_Util_Seqset_set_val
            Task (ar_decidable_eq Task) tsL)))).
    apply tdma_fold_related.
    - exact (tdma_slot_related _ _ _ Hpolicy).
    - apply tdma_filter_related.
      + exact (tdma_offset_pred_related tsk).
      + exact (tdma_set_list_related Task tsR tsL Hts).
  Qed.

  Theorem task_in_time_slot_correspondence tsk tR tL :
    SubNatRel tR tL ->
    ArBoolRel
      (@prosa.model.schedule.tdma.task_in_time_slot
        Task tsR policyR tsk tR)
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_task_in_time_slot
        Task (ar_decidable_eq Task) policyL tsL tsk tL).
  Proof.
    intro Ht.
    rewrite /prosa.model.schedule.tdma.task_in_time_slot.
    change (ArBoolRel
      (ltn
        (((tR + @prosa.model.schedule.tdma.TDMA_cycle Task tsR policyR)
            - (@prosa.model.schedule.tdma.task_slot_offset
                Task tsR policyR tsk %%
               @prosa.model.schedule.tdma.TDMA_cycle Task tsR policyR))
          %% @prosa.model.schedule.tdma.TDMA_cycle Task tsR policyR)
        (@prosa.model.schedule.tdma.task_time_slot Task policyR tsk))
      (tdma_nat_lt_bool
        (tdma_nat_mod
          (tdma_nat_sub
            (tdma_nat_add tL
              (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMA_cycle
                Task (ar_decidable_eq Task) policyL tsL))
            (tdma_nat_mod
              (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_task_slot_offset
                Task (ar_decidable_eq Task) policyL tsL tsk)
              (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMA_cycle
                Task (ar_decidable_eq Task) policyL tsL)))
          (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMA_cycle
            Task (ar_decidable_eq Task) policyL tsL))
        (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot
          Task (ar_decidable_eq Task) policyL tsk))).
    apply tdma_nat_lt_bool_related.
    - apply tdma_nat_mod_related.
      + apply tdma_nat_sub_related.
        * apply tdma_nat_add_related.
          -- exact Ht.
          -- exact TDMA_cycle_correspondence.
        * apply tdma_nat_mod_related.
          -- exact (task_slot_offset_correspondence tsk).
          -- exact TDMA_cycle_correspondence.
      + exact TDMA_cycle_correspondence.
    - exact (tdma_slot_related _ _ _ Hpolicy tsk).
  Qed.
End TdmaNumeric.

Print Assumptions tdma_add_related.
Print Assumptions tdma_fold_related.
Print Assumptions TDMA_cycle_correspondence.
Print Assumptions task_slot_offset_correspondence.
Print Assumptions task_in_time_slot_correspondence.
