(* Re-bound copy of the accepted certificates/model_task_arrivals/ArrivalsSeqOperations.v:
   only the imported module (ImportedArrivals -> ImportedCurves) and the
   certificate logical path are renamed. *)
(* Re-bound copy of the accepted behavior/arrival_sequence ArrivalSequenceOperations.v
   for the model/task/arrivals artifact; only module names differ. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import behavior.arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedCurves
  ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ArrivalsSeqBaseAdapter.

(** Minimal operation-level correspondence layer for the actual compiled
    Arrival Sequence artifact.  These proofs are deliberately separated from
    the 14 declaration certificates so later Behavior files can reuse the
    same JobArrival, ordered-list, Boolean, Nat-order, filter, uniqueness, and
    half-open big-concatenation interfaces. *)

Definition ar_target_false_elim (Q : SProp)
    (H : ImportedCurves.False) : Q :=
  match H return Q with end.

Definition ar_target_false_to_strict
    (H : ImportedCurves.False) : StrictlyInhabited Logic.False :=
  match H with end.

Lemma ar_bool_eq_correspondence aR aL bR bL :
  ArBoolRel aR aL -> ArBoolRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Ha) Hb).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (ar_bool_to_imported aR)
        (ar_bool_to_imported bR) :=
      sub_imported_eq_trans _ _ _ Ha
        (sub_imported_eq_trans _ _ _ Heq
          (sub_imported_eq_sym _ _ Hb)).
    have Hdecoded := f_equal ar_bool_to_rocq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (ar_bool_source_roundtrip aR) in Hdecoded.
    rewrite (ar_bool_source_roundtrip bR) in Hdecoded.
    exact Hdecoded.
Qed.

Lemma ar_bool_and_related aR aL bR bL :
  ArBoolRel aR aL -> ArBoolRel bR bL ->
  ArBoolRel (aR && bR) (ImportedCurves.Bool_and aL bL).
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

Lemma ar_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedCurves.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  ArBoolRel b (ImportedCurves.Decidable_decide Q d).
Proof.
  intro Hrel. unfold ArBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (ar_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (ar_target_false_elim _ (ar_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Definition ar_target_decide_mem (T : eqType) (x : T)
    (xs : ImportedCurves.List T) : ImportedCurves.Bool :=
  ImportedCurves.Decidable_decide (ar_target_mem x xs)
    (ImportedCurves.List_instDecidableMemOfLawfulBEq T
      (ImportedCurves.instBEqOfDecidableEq T (ar_decidable_eq T))
      (ImportedCurves.instLawfulBEq T (ar_decidable_eq T)) x xs).

Lemma ar_decide_mem_related (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedCurves.List T) :
  ArListRel xsR xsL ->
  ArBoolRel (x \in xsR) (ar_target_decide_mem T x xsL).
Proof.
  intro Hxs. apply ar_decide_bool_correspondence.
  exact (ar_membership_correspondence T x xsR xsL Hxs).
Qed.

Definition ArPredRel {T : Type} (PR : T -> bool)
    (PL : T -> ImportedCurves.Bool) : SProp :=
  forall x, ArBoolRel (PR x) (PL x).

Definition ar_pred_to_imported {T : Type} (PR : T -> bool) :
    T -> ImportedCurves.Bool := fun x => ar_bool_to_imported (PR x).

Lemma ar_pred_canonical {T : Type} (PR : T -> bool) :
  ArPredRel PR (ar_pred_to_imported PR).
Proof. intro x. exact (@Lean.eq_refl _ _). Qed.

Definition ar_target_append {T : Type}
    (xs ys : ImportedCurves.List T) :
    ImportedCurves.List T :=
  ImportedCurves.HAppend_hAppend
    (ImportedCurves.List T) (ImportedCurves.List T)
    (ImportedCurves.List T)
    (ImportedCurves.instHAppendOfAppend
      (ImportedCurves.List T)
      (ImportedCurves.List_instAppend T)) xs ys.

Lemma ar_append_canonical (T : Type) (xs ys : seq T) :
  Lean.eq (ar_target_append (ar_list_to_imported xs)
    (ar_list_to_imported ys)) (ar_list_to_imported (xs ++ ys)).
Proof.
  induction xs as [|x xs IH].
  - exact
      (ImportedCurves.Prosa_Validation_BigcatInterface_production_append_nil
        T (ar_list_to_imported ys)).
  - refine (sub_imported_eq_trans _ _ _
      (ImportedCurves.Prosa_Validation_BigcatInterface_production_append_cons
        T x (ar_list_to_imported xs) (ar_list_to_imported ys)) _).
    exact (sub_imported_eq_congr
      (ImportedCurves.List_cons T x) _ _ IH).
Qed.

Lemma ar_append_related (T : Type)
    (xsR ysR : seq T)
    (xsL ysL : ImportedCurves.List T) :
  ArListRel xsR xsL -> ArListRel ysR ysL ->
  ArListRel (xsR ++ ysR) (ar_target_append xsL ysL).
Proof.
  intros Hxs Hys. unfold ArListRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (ar_append_canonical T xsR ysR))
    (sub_imported_eq_congr2 ar_target_append _ _ _ _ Hxs Hys)).
Qed.

Definition ar_target_filter {T : Type}
    (P : T -> ImportedCurves.Bool)
    (xs : ImportedCurves.List T) : ImportedCurves.List T :=
  ImportedCurves.List_filter T P xs.

Definition ar_filter_match {T : Type} (b : ImportedCurves.Bool)
    (x : T) (tail : ImportedCurves.List T) :
    ImportedCurves.List T :=
  ImportedCurves.Prosa_Validation_BigcatInterface_production_filter_cons_match_1
    (fun _ : ImportedCurves.Bool => ImportedCurves.List T) b
    (fun _ : ImportedCurves.Unit =>
      ImportedCurves.List_cons T x tail)
    (fun _ : ImportedCurves.Unit => tail).

Lemma ar_filter_match_canonical {T : Type} (b : bool) (x : T)
    (tail : ImportedCurves.List T) :
  Lean.eq (ar_filter_match (ar_bool_to_imported b) x tail)
    (match b with
     | true => ImportedCurves.List_cons T x tail
     | false => tail
     end).
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma ar_filter_branch_canonical {T : Type} (b : bool) (x : T)
    (filtered : seq T) (tail : ImportedCurves.List T) :
  Lean.eq tail (ar_list_to_imported filtered) ->
  Lean.eq
    (match b with
     | true => ImportedCurves.List_cons T x tail
     | false => tail
     end)
    (ar_list_to_imported
      (match b with true => x :: filtered | false => filtered end)).
Proof.
  intro IH. destruct b; cbn.
  - exact (sub_imported_eq_congr
      (ImportedCurves.List_cons T x) _ _ IH).
  - exact IH.
Qed.

Lemma ar_source_filter_cons {T : Type} (P : T -> bool)
    (x : T) (xs : seq T) :
  Logic.eq
    (match P x with
     | true => x :: [seq y <- xs | P y]
     | false => [seq y <- xs | P y]
     end)
    [seq y <- x :: xs | P y].
Proof. cbn. destruct (P x); reflexivity. Qed.

Lemma ar_filter_canonical (T : Type) (PR : T -> bool)
    (PL : T -> ImportedCurves.Bool) : ArPredRel PR PL ->
  forall xs : seq T,
  Lean.eq (ar_target_filter PL (ar_list_to_imported xs))
    (ar_list_to_imported [seq x <- xs | PR x]).
Proof.
  intro HP. induction xs as [|x xs IH].
  - exact
      (ImportedCurves.Prosa_Validation_BigcatInterface_production_filter_nil
        T PL).
  - refine (sub_imported_eq_trans _ _ _
      (ImportedCurves.Prosa_Validation_BigcatInterface_production_filter_cons
        T PL x (ar_list_to_imported xs)) _).
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (fun b => ar_filter_match b x
          (ar_target_filter PL (ar_list_to_imported xs))) _ _
        (sub_imported_eq_sym _ _ (HP x))) _).
    refine (sub_imported_eq_trans _ _ _
      (ar_filter_match_canonical (PR x) x
        (ar_target_filter PL (ar_list_to_imported xs))) _).
    refine (sub_imported_eq_trans _ _ _
      (ar_filter_branch_canonical (PR x) x
        [seq y <- xs | PR y]
        (ar_target_filter PL (ar_list_to_imported xs)) IH) _).
    exact (coq_eq_to_imported_eq _ _
      (f_equal ar_list_to_imported (ar_source_filter_cons PR x xs))).
Qed.

Lemma ar_filter_related (T : Type) (PR : T -> bool)
    (PL : T -> ImportedCurves.Bool) (xsR : seq T)
    (xsL : ImportedCurves.List T) :
  ArPredRel PR PL -> ArListRel xsR xsL ->
  ArListRel [seq x <- xsR | PR x] (ar_target_filter PL xsL).
Proof.
  intros HP Hxs. unfold ArListRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (ar_filter_canonical T PR PL HP xsR))
    (sub_imported_eq_congr (ar_target_filter PL) _ _ Hxs)).
Qed.

Lemma ar_list_eq_correspondence (T : Type)
    (xsR ysR : seq T)
    (xsL ysL : ImportedCurves.List T) :
  ArListRel xsR xsL -> ArListRel ysR ysL ->
  PropSPropRel (Logic.eq xsR ysR) (Lean.eq xsL ysL).
Proof.
  intros Hxs Hys. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Hxs) Hys).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (ar_list_to_imported xsR)
        (ar_list_to_imported ysR) :=
      sub_imported_eq_trans _ _ _ Hxs
        (sub_imported_eq_trans _ _ _ Heq
          (sub_imported_eq_sym _ _ Hys)).
    have Hdecoded := f_equal ar_list_to_rocq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (ar_list_source_roundtrip xsR) in Hdecoded.
    rewrite (ar_list_source_roundtrip ysR) in Hdecoded.
    exact Hdecoded.
Qed.

Definition ar_nodup_transport {T : Type}
    (xs ys : ImportedCurves.List T) :
  Lean.eq xs ys -> ImportedCurves.List_Nodup T xs ->
  ImportedCurves.List_Nodup T ys :=
  fun Hxy H =>
    match Hxy in Lean.eq _ zs return
      ImportedCurves.List_Nodup T zs with
    | Lean.eq_refl => H
    end.

Definition ar_and_left_truth (a b : bool) :
    SubNatTruth (a && b) -> SubNatTruth a :=
  match a, b return SubNatTruth (a && b) -> SubNatTruth a with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => fun H => H
  end.

Definition ar_and_right_truth (a b : bool) :
    SubNatTruth (a && b) -> SubNatTruth b :=
  match a, b return SubNatTruth (a && b) -> SubNatTruth b with
  | true, true => fun _ => sub_nat_truth_intro
  | true, false => fun H => H
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Definition ar_neg_mem_contra (b : bool) :
    SubNatTruth (~~ b) -> SubNatTruth b -> ImportedCurves.False :=
  match b return SubNatTruth (~~ b) -> SubNatTruth b ->
      ImportedCurves.False with
  | true => fun H _ => match H with end
  | false => fun _ H => match H with end
  end.

Fixpoint ar_uniq_truth_forward (T : eqType) (xs : seq T) :
    SubNatTruth (uniq xs) ->
    ImportedCurves.List_Nodup T (ar_list_to_imported xs).
Proof.
  destruct xs as [|x xs].
  - intro Hnil.
    exact (ImportedCurves.List_Pairwise_nil T
      (ImportedCurves.Ne T)).
  - intro Huniq. apply ImportedCurves.List_Pairwise_cons.
    + intros y Hy Hxy.
      have HyR := sprop_to_prop _ _
        (ar_membership_correspondence T y xs (ar_list_to_imported xs)
          (@Lean.eq_refl _ _)) Hy.
      have Hcoq : Logic.eq x y := imported_eq_to_coq_eq x y Hxy.
      subst y.
      exact (ar_neg_mem_contra (x \in xs)
        (ar_and_left_truth _ _ Huniq) (sub_nat_prop_to_truth _ HyR)).
    + exact (ar_uniq_truth_forward T xs
        (ar_and_right_truth _ _ Huniq)).
Defined.

Definition ar_uniq_forward (T : eqType) (xs : seq T) :
    uniq xs -> ImportedCurves.List_Nodup T
      (ar_list_to_imported xs) :=
  fun H => ar_uniq_truth_forward T xs (sub_nat_prop_to_truth _ H).

Lemma ar_imported_nodup_backward (T : eqType)
    (xs : ImportedCurves.List T) :
  ImportedCurves.List_Nodup T xs ->
  StrictlyInhabited (uniq (ar_list_to_rocq xs)).
Proof.
  intro Hnodup. induction Hnodup as [|y ys Hhead Htail IH].
  - exact (strictly_inhabits (Logic.eq_refl true)).
  - destruct IH as [IHuniq]. apply strictly_inhabits.
    apply/andP. split; last exact IHuniq.
    apply/negP. intro Hmem.
    have HmemL := prop_to_sprop _ _
      (ar_membership_correspondence T y (ar_list_to_rocq ys) ys
        (ar_list_target_roundtrip ys)) Hmem.
    have Hneq := Hhead y HmemL.
    exact (interpret_strict Logic.False
      (ar_target_false_to_strict (Hneq (@Lean.eq_refl T y)))).
Qed.

Lemma ar_uniq_correspondence (T : eqType)
    (xsR : seq T) (xsL : ImportedCurves.List T) :
  ArListRel xsR xsL ->
  PropSPropRel (uniq xsR) (ImportedCurves.List_Nodup T xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Huniq. exact (ar_nodup_transport _ _ Hxs
      (ar_uniq_forward T xsR Huniq)).
  - intro Hnodup.
    have Hcanonical := ar_nodup_transport _ _
      (sub_imported_eq_sym _ _ Hxs) Hnodup.
    have Hstrict := ar_imported_nodup_backward T
      (ar_list_to_imported xsR) Hcanonical.
    destruct Hstrict as [Huniq]. apply strictly_inhabits.
    rewrite (ar_list_source_roundtrip xsR) in Huniq.
    exact Huniq.
Qed.

Definition ar_target_le (a b : Lean.Nat) : SProp :=
  ImportedCurves.LE_le_inst1 Lean.Nat
    ImportedCurves.instLENat a b.

Definition ar_target_lt (a b : Lean.Nat) : SProp :=
  ImportedCurves.LT_lt_inst1 Lean.Nat
    ImportedCurves.instLTNat a b.

Definition ar_target_decide_le (a b : Lean.Nat) :
    ImportedCurves.Bool :=
  ImportedCurves.Decidable_decide (ar_target_le a b)
    (ImportedCurves.Nat_decLe a b).

Definition ar_target_decide_lt (a b : Lean.Nat) :
    ImportedCurves.Bool :=
  ImportedCurves.Decidable_decide (ar_target_lt a b)
    (ImportedCurves.Nat_decLt a b).

Lemma ar_decide_le_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  ArBoolRel (leq aR bR) (ar_target_decide_le aL bL).
Proof.
  intros Ha Hb. apply ar_decide_bool_correspondence.
  unfold ar_target_le.
  exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma ar_decide_lt_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  ArBoolRel (ltn aR bR) (ar_target_decide_lt aL bL).
Proof.
  intros Ha Hb. apply ar_decide_bool_correspondence.
  unfold ar_target_lt.
  exact (sub_nat_lt_correspondence aR aL bR bL Ha Hb).
Qed.

Definition ArJobArrivalRel (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T)
    (arrivalL : ImportedCurves.Prosa_Behavior_Job_JobArrival T
      (ar_decidable_eq T)) : SProp :=
  forall j : T,
    SubNatRel (@prosa.behavior.job.job_arrival T arrivalR j)
      (ImportedCurves.Prosa_Behavior_Job_JobArrival_job_arrival T
        (ar_decidable_eq T) arrivalL j).

Definition ar_import_job_arrival (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T) :
    ImportedCurves.Prosa_Behavior_Job_JobArrival T
      (ar_decidable_eq T) :=
  ImportedCurves.Prosa_Behavior_Job_JobArrival_mk T
    (ar_decidable_eq T)
    (fun j => sub_nat_to_imported
      (@prosa.behavior.job.job_arrival T arrivalR j)).

Lemma ar_job_arrival_import_certificate (T : eqType)
    (arrivalR : prosa.behavior.job.JobArrival T) :
  ArJobArrivalRel T arrivalR (ar_import_job_arrival T arrivalR).
Proof. intros j. exact (sub_nat_rel_canonical _). Qed.

Definition ArArrivalSequenceRel (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T)
    (arrL :
      ImportedCurves.Prosa_Behavior_Arrival_sequence_arrival_sequence T
        (ar_decidable_eq T)) : SProp :=
  forall tR tL, SubNatRel tR tL -> ArListRel (arrR tR) (arrL tL).

Definition ar_arrival_sequence_to_imported (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T) :
    ImportedCurves.Prosa_Behavior_Arrival_sequence_arrival_sequence T
      (ar_decidable_eq T) :=
  fun tL => ar_list_to_imported (arrR (sub_nat_to_rocq tL)).

Lemma ar_arrival_sequence_canonical (T : eqType)
    (arrR : prosa.behavior.arrival_sequence.arrival_sequence T) :
  ArArrivalSequenceRel T arrR (ar_arrival_sequence_to_imported T arrR).
Proof.
  intros tR tL Ht. unfold ArListRel, ar_arrival_sequence_to_imported.
  have Hdecoded := f_equal sub_nat_to_rocq
    (imported_eq_to_coq_eq _ _ Ht).
  rewrite (sub_nat_rocq_roundtrip tR) in Hdecoded.
  rewrite <- Hdecoded. exact (@Lean.eq_refl _ _).
Qed.

Definition ArNatListFamilyRel {T : Type} (fR : nat -> seq T)
    (fL : Lean.Nat -> ImportedCurves.List T) : SProp :=
  forall iR iL, SubNatRel iR iL -> ArListRel (fR iR) (fL iL).

Definition ar_target_bigCat_nat {T : Type}
    (m n : Lean.Nat) (f : Lean.Nat -> ImportedCurves.List T) :
    ImportedCurves.List T :=
  ImportedCurves.Prosa_Util_Notation_bigCat T m n f.

Definition ar_target_bigCat_nat_delta {T : Type}
    (m d : Lean.Nat) (f : Lean.Nat -> ImportedCurves.List T) :
    ImportedCurves.List T :=
  ar_target_bigCat_nat m (Lean.Nat_add m d) f.

Lemma ar_bigCatNat_delta_related_rel (T : Type)
    (fR : nat -> seq T)
    (fL : Lean.Nat -> ImportedCurves.List T) (m d : nat) :
  ArNatListFamilyRel fR fL ->
  ArListRel (\cat_(m <= i < m + d) fR i)
    (ar_target_bigCat_nat_delta
      (sub_nat_to_imported m) (sub_nat_to_imported d) fL).
Proof.
  intro Hf. induction d as [|d IH].
  - rewrite addn0 big_geq //.
    unfold ArListRel, ar_target_bigCat_nat_delta,
      ar_target_bigCat_nat. cbn.
    exact (sub_imported_eq_sym _ _
      (ImportedCurves.Prosa_Validation_BigcatInterface_production_bigCat_same
        T (sub_nat_to_imported m) fL)).
  - rewrite addnS big_nat_recr.
    exact (leq_addr d m).
    have Happ := ar_append_related T
      (\cat_(m <= i < m + d) fR i) (fR (m + d))
      (ar_target_bigCat_nat_delta
        (sub_nat_to_imported m) (sub_nat_to_imported d) fL)
      (fL (Lean.Nat_add
        (sub_nat_to_imported m) (sub_nat_to_imported d)))
      IH (Hf (m + d)
        (Lean.Nat_add (sub_nat_to_imported m) (sub_nat_to_imported d))
        (sub_add_correspondence m (sub_nat_to_imported m)
          d (sub_nat_to_imported d)
          (sub_nat_rel_canonical m) (sub_nat_rel_canonical d))).
    unfold ArListRel, ar_target_bigCat_nat_delta,
      ar_target_bigCat_nat in Happ |- *.
    exact (sub_imported_eq_trans _ _ _ Happ
      (sub_imported_eq_sym _ _
        (ImportedCurves.Prosa_Validation_BigcatInterface_production_bigCat_add_succ
          T (sub_nat_to_imported m) (sub_nat_to_imported d) fL))).
Qed.

Lemma ar_bigCatNat_related_rel (T : Type)
    (fR : nat -> seq T)
    (fL : Lean.Nat -> ImportedCurves.List T) (m n : nat) :
  ArNatListFamilyRel fR fL ->
  ArListRel (\cat_(m <= i < n) fR i)
    (ar_target_bigCat_nat (sub_nat_to_imported m)
      (sub_nat_to_imported n) fL).
Proof.
  intro Hf. unfold ArListRel.
  apply coq_eq_to_imported_eq.
  case Hmn: (m <= n)%N.
  - have HmnP : (m <= n)%N by exact Hmn.
    have Hn : m + (n - m) = n by rewrite addnC subnK.
    rewrite -Hn.
    have Hdelta := ar_bigCatNat_delta_related_rel T fR fL
      m (n - m) Hf.
    have HdeltaP := imported_eq_to_coq_eq _ _ Hdelta.
    unfold ArListRel, ar_target_bigCat_nat_delta,
      ar_target_bigCat_nat in HdeltaP |- *.
    etransitivity; first exact HdeltaP.
    apply imported_eq_to_coq_eq.
    exact (sub_imported_eq_congr
      (fun upper => ImportedCurves.Prosa_Util_Notation_bigCat T
        (sub_nat_to_imported m) upper fL) _ _
      (sub_imported_eq_sym _ _
        (sub_add_correspondence m (sub_nat_to_imported m)
          (n - m) (sub_nat_to_imported (n - m))
          (sub_nat_rel_canonical m) (sub_nat_rel_canonical (n - m))))).
  - have Hlt : (n < m)%N by rewrite ltnNge Hmn.
    have Hnm : (n <= m)%N := ltnW Hlt.
    rewrite big_geq //.
    have HleL := prop_to_sprop _ _
      (sub_nat_le_correspondence n (sub_nat_to_imported n)
        m (sub_nat_to_imported m)
        (sub_nat_rel_canonical n) (sub_nat_rel_canonical m)) Hnm.
    unfold ar_target_bigCat_nat.
    apply imported_eq_to_coq_eq.
    exact (sub_imported_eq_sym _ _
      (ImportedCurves.Prosa_Validation_BigcatInterface_production_bigCat_of_le
        T (sub_nat_to_imported m) (sub_nat_to_imported n) fL HleL)).
Qed.

Lemma ar_bigCatNat_related_any (T : Type)
    (fR : nat -> seq T)
    (fL : Lean.Nat -> ImportedCurves.List T)
    (mR nR : nat) (mL nL : Lean.Nat) :
  ArNatListFamilyRel fR fL -> SubNatRel mR mL -> SubNatRel nR nL ->
  ArListRel (\cat_(mR <= i < nR) fR i)
    (ar_target_bigCat_nat mL nL fL).
Proof.
  intros Hf Hm Hn. unfold ArListRel.
  exact (sub_imported_eq_trans _ _ _
    (ar_bigCatNat_related_rel T fR fL mR nR Hf)
    (sub_imported_eq_congr2
      (fun m n => ar_target_bigCat_nat m n fL) _ _ _ _ Hm Hn)).
Qed.

Lemma ar_exists_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL ->
    PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (exists nR, PR nR)
    (ImportedCurves.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [nR Hn].
    exact (ImportedCurves.Exists_intro Lean.Nat PL
      (sub_nat_to_imported nR)
      (prop_to_sprop _ _
        (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) Hn)).
  - intros [nL Hn]. apply strictly_inhabits.
    exists (sub_nat_to_rocq nL).
    exact (sprop_to_prop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL)) Hn).
Qed.

Lemma ar_and_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P /\ Q) (And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p q]. exact (And_intro PL QL
      (prop_to_sprop _ _ HP p) (prop_to_sprop _ _ HQ q)).
  - intros [p q]. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ HP p).
    + exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma ar_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. apply (prop_to_sprop _ _ HQ).
    exact (H (sprop_to_prop _ _ HP p)).
  - intro H. apply strictly_inhabits. intro p.
    apply (sprop_to_prop _ _ HQ).
    exact (H (prop_to_sprop _ _ HP p)).
Qed.

Lemma ar_forall_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (HP x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _ (HP x) (HL x)).
Qed.

Lemma ar_forall_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL ->
    PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall nR, PR nR) (forall nL, PL nL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR nL. exact (prop_to_sprop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL))
      (HR (sub_nat_to_rocq nL))).
  - intro HL. apply strictly_inhabits. intro nR.
    exact (sprop_to_prop _ _
      (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR))
      (HL (sub_nat_to_imported nR))).
Qed.

Print Assumptions ar_decide_mem_related.
Print Assumptions ar_filter_related.
Print Assumptions ar_uniq_correspondence.
Print Assumptions ar_decide_le_related.
Print Assumptions ar_decide_lt_related.
Print Assumptions ar_job_arrival_import_certificate.
Print Assumptions ar_arrival_sequence_canonical.
Print Assumptions ar_bigCatNat_related_any.
Print Assumptions ar_exists_nat_correspondence.
Print Assumptions ar_and_correspondence.
Print Assumptions ar_imp_correspondence.
Print Assumptions ar_forall_identity_correspondence.
Print Assumptions ar_forall_nat_correspondence.
