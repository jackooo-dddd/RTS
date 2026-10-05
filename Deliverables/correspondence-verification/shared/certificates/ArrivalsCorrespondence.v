From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import model.task.arrivals.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedArrivals ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ArrivalsSeqBaseAdapter ArrivalsSeqOperations
  ArrivalsSeqCorrespondence.

Module I := ImportedArrivals.

(** Correspondence certificates for [model/task/arrivals.v] on the actual
    imported Lean artifact.  The arrival-sequence, filter, Bool and Nat order
    bridges are the accepted ArrivalSequence chain re-bound to this artifact;
    this file adds the missing list operations (size/length, big sum/List.sum,
    index/idxOf, nth/getD) and Nat subtraction, all proved by induction or by
    kernel conversion on the imported definitions.  No source or target
    theorem is used. *)

(** ** Generic transports *)

Lemma ari_logic_eq_to_lean_eq {A : Type} (x y : A) :
  Logic.eq x y -> Lean.eq x y.
Proof. intros []. exact (@Lean.eq_refl _ _). Qed.

Lemma ari_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma ari_subnat_source_transport (aR bR : nat) (nL : Lean.Nat) :
  Logic.eq aR bR -> SubNatRel bR nL -> SubNatRel aR nL.
Proof. intros H. destruct H. exact (fun p => p). Qed.

(** ** Equality decision on an [eqType] carrier *)

Lemma ari_decide_eq_related (T : eqType) (x y : T) :
  ArBoolRel (x == y)
    (I.Decidable_decide (Lean.eq x y) (ar_decidable_eq T x y)).
Proof.
  apply ari_logic_eq_to_lean_eq.
  unfold ar_decidable_eq. case: eqP => H; reflexivity.
Qed.

(** ** Nat subtraction (re-bound from the accepted TDMA arithmetic adapter) *)

Definition ari_nat_sub (a b : Lean.Nat) : Lean.Nat :=
  I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHSub_inst1 Lean.Nat I.instSubNat) a b.

Fixpoint ari_iterated_pred (a b : nat) : nat :=
  match b with
  | O => a
  | S b' => Nat.pred (ari_iterated_pred a b')
  end.

Lemma ari_iterated_pred_is_subn (a b : nat) :
  Logic.eq (ari_iterated_pred a b) (a - b).
Proof.
  revert a. induction b as [|b IH]; intro a; cbn [ari_iterated_pred].
  - rewrite subn0. reflexivity.
  - rewrite (IH a). exact (Logic.eq_sym (subnS a b)).
Qed.

Definition ari_nat_pred_canonical (n : nat) :
  Lean.eq (I.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (I.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma ari_nat_sub_iterated_pred (a b : nat) :
  Lean.eq (ari_nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (ari_iterated_pred a b)).
Proof.
  revert a. induction b as [|b IH]; intro a.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr I.Nat_pred _ _ (IH a))
      (ari_nat_pred_canonical (ari_iterated_pred a b))).
Qed.

Lemma ari_nat_sub_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (ari_nat_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  refine (sub_imported_eq_trans _ _ _ _
    (sub_imported_eq_congr2 ari_nat_sub _ _ _ _ Ha Hb)).
  refine (sub_imported_eq_trans _ _ _
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported (Logic.eq_sym (ari_iterated_pred_is_subn aR bR)))) _).
  exact (sub_imported_eq_sym _ _ (ari_nat_sub_iterated_pred aR bR)).
Qed.

(** ** size / List.length *)

Lemma ari_size_canonical (T : Type) (xs : seq T) :
  Lean.eq (sub_nat_to_imported (size xs)) (I.List_length T (ar_list_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr Lean.Nat_succ _ _ IH).
Qed.

Lemma ari_size_related (T : Type) (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL -> SubNatRel (size xsR) (I.List_length T xsL).
Proof.
  intro Hxs. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _ (ari_size_canonical T xsR)
    (sub_imported_eq_congr (I.List_length T) _ _ Hxs)).
Qed.

(** ** \sum over a sequence / List.sum ∘ List.map *)

Definition ari_list_sum (T : Type) (f : T -> Lean.Nat) (xs : I.List T) : Lean.Nat :=
  I.List_sum_inst1 Lean.Nat I.instAddNat
    (I.MulZeroClass_toZero_inst1 Lean.Nat I.Nat_instMulZeroClass)
    (I.List_map_inst2 T Lean.Nat f xs).

Lemma ari_sum_nil (T : Type) (FR : T -> nat) :
  Logic.eq (\sum_(x <- [::]) FR x) O.
Proof. rewrite big_nil. reflexivity. Qed.

Lemma ari_sum_cons (T : Type) (FR : T -> nat) (x : T) (xs : seq T) :
  Logic.eq (\sum_(y <- x :: xs) FR y) (FR x + \sum_(y <- xs) FR y).
Proof. rewrite big_cons. reflexivity. Qed.

Lemma ari_sum_canonical (T : Type) (FR : T -> nat) (FL : T -> Lean.Nat) :
  (forall x, SubNatRel (FR x) (FL x)) ->
  forall xs : seq T,
  SubNatRel (\sum_(x <- xs) FR x) (ari_list_sum T FL (ar_list_to_imported xs)).
Proof.
  intros HF xs. induction xs as [|x xs IH].
  - apply (ari_subnat_source_transport _ O _ (ari_sum_nil T FR)).
    exact (@Lean.eq_refl _ _).
  - apply (ari_subnat_source_transport _ (FR x + \sum_(y <- xs) FR y) _
      (ari_sum_cons T FR x xs)).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma ari_sum_related (T : Type) (FR : T -> nat) (FL : T -> Lean.Nat)
    (xsR : seq T) (xsL : I.List T) :
  (forall x, SubNatRel (FR x) (FL x)) -> ArListRel xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (ari_list_sum T FL xsL).
Proof.
  intros HF Hxs.
  exact (ari_lean_transport (fun l => SubNatRel (\sum_(x <- xsR) FR x) (ari_list_sum T FL l))
    _ _ Hxs (ari_sum_canonical T FR FL HF xsR)).
Qed.

(** ** index / List.idxOf *)

Definition ari_beq (T : eqType) (y : T) : T -> I.Bool :=
  fun x => I.BEq_beq T (I.instBEqOfDecidableEq T (ar_decidable_eq T)) x y.

Lemma ari_beq_related (T : eqType) (x y : T) :
  ArBoolRel (x == y) (ari_beq T y x).
Proof. exact (ari_decide_eq_related T x y). Qed.

Lemma ari_add_succ_shift (n k : nat) : Logic.eq (n + k.+1) (n + 1 + k).
Proof. rewrite addnS addn1 addSn. reflexivity. Qed.

Lemma ari_find_go_canonical (T : eqType) (y : T) :
  forall (xs : seq T) (n : nat),
  Lean.eq (sub_nat_to_imported (n + find (pred1 y) xs))
    (I.List_findIdx_go T (ari_beq T y) (ar_list_to_imported xs) (sub_nat_to_imported n)).
Proof.
  induction xs as [|x xs IH]; intro n.
  - exact (ari_logic_eq_to_lean_eq _ _ (f_equal sub_nat_to_imported (addn0 n))).
  - cbn [find ar_list_to_imported].
    refine (ari_lean_transport
      (fun b => Lean.eq
        (sub_nat_to_imported (n + (if pred1 y x then O else (find (pred1 y) xs).+1)))
        (I.cond Lean.Nat b (sub_nat_to_imported n)
          (I.List_findIdx_go T (ari_beq T y) (ar_list_to_imported xs)
            (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
              (I.instHAdd_inst1 Lean.Nat I.instAddNat) (sub_nat_to_imported n)
              (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))))))
      _ _ (ari_beq_related T x y) _).
    cbn [pred1 SimplPred]. unfold ar_bool_to_imported.
    change (x == y) with (pred1 y x).
    destruct (pred1 y x); cbn [I.cond].
    + exact (ari_logic_eq_to_lean_eq _ _ (f_equal sub_nat_to_imported (addn0 n))).
    + refine (sub_imported_eq_trans _ _ _ _
        (sub_imported_eq_congr
          (I.List_findIdx_go T (ari_beq T y) (ar_list_to_imported xs)) _ _
          (sub_add_correspondence n _ 1 _ (sub_nat_rel_canonical n)
            (@Lean.eq_refl _ _)))).
      refine (sub_imported_eq_trans _ _ _ _ (IH (n + 1))).
      exact (ari_logic_eq_to_lean_eq _ _
        (f_equal sub_nat_to_imported (ari_add_succ_shift n _))).
Qed.

Lemma ari_index_related (T : eqType) (y : T) (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL ->
  SubNatRel (index y xsR)
    (I.List_idxOf T (I.instBEqOfDecidableEq T (ar_decidable_eq T)) y xsL).
Proof.
  intro Hxs.
  exact (ari_lean_transport
    (fun l => SubNatRel (index y xsR)
      (I.List_idxOf T (I.instBEqOfDecidableEq T (ar_decidable_eq T)) y l))
    _ _ Hxs (ari_find_go_canonical T y xsR O)).
Qed.

(** ** nth / List.getD *)

Lemma ari_nth_canonical (T : Type) (d : T) :
  forall (xs : seq T) (n : nat),
  Lean.eq (nth d xs n) (I.List_getD T (ar_list_to_imported xs) (sub_nat_to_imported n) d).
Proof.
  induction xs as [|x xs IH]; intro n.
  - destruct n; exact (@Lean.eq_refl _ _).
  - destruct n as [|n].
    + exact (@Lean.eq_refl _ _).
    + exact (IH n).
Qed.

Lemma ari_nth_related (T : Type) (d : T) (xsR : seq T) (xsL : I.List T)
    (nR : nat) (nL : Lean.Nat) :
  ArListRel xsR xsL -> SubNatRel nR nL ->
  Lean.eq (nth d xsR nR) (I.List_getD T xsL nL d).
Proof.
  intros Hxs Hn.
  refine (ari_lean_transport (fun l => Lean.eq (nth d xsR nR) (I.List_getD T l nL d))
    _ _ Hxs _).
  exact (ari_lean_transport
    (fun m => Lean.eq (nth d xsR nR) (I.List_getD T (ar_list_to_imported xsR) m d))
    _ _ Hn (ari_nth_canonical T d xsR nR)).
Qed.

(** ** Declaration correspondences *)

Section ArrivalsCorrespondence.
  Context (Job Task : eqType).
  Let dJ := ar_decidable_eq Job.
  Let dT := ar_decidable_eq Task.

  (** Input relations (data only). *)
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma job_of_task_related (tskR tskL : Task) :
    Lean.eq tskR tskL ->
    ArPredRel (fun j => @prosa.model.task.concept.job_of_task Job Task jtR tskR j)
      (fun j => I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tskL j).
  Proof.
    intros Htsk j.
    refine (ari_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tskR j)
        (I.Decidable_decide (Lean.eq v tskL) (dT v tskL))) _ _ (Hjt j) _).
    refine (ari_lean_transport
      (fun w => ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tskR j)
        (I.Decidable_decide (Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j) w)
          (dT (@prosa.model.task.concept.job_task Job Task jtR j) w))) _ _ Htsk _).
    exact (ari_decide_eq_related Task _ tskR).
  Qed.

  Lemma task_arrivals_between_correspondence (tskR tskL : Task)
      t1R t1L t2R t2L :
    Lean.eq tskR tskL -> SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    ArListRel (@task_arrivals_between Job Task jtR arrR tskR t1R t2R)
      (I.Prosa_Model_Task_Arrivals_task_arrivals_between Job dJ Task dT jtL arrL tskL t1L t2L).
  Proof.
    intros Htsk H1 H2.
    exact (ar_filter_related Job _ _ _ _ (job_of_task_related tskR tskL Htsk)
      (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2)).
  Qed.

  Lemma ari_succ_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel tR.+1
      (I.HAdd_hAdd_inst7 I.Prosa_Behavior_Time_instant I.Prosa_Behavior_Time_instant
        I.Prosa_Behavior_Time_instant
        (I.instHAdd_inst1 I.Prosa_Behavior_Time_instant I.instAddNat) tL
        (I.OfNat_ofNat_inst1 I.Prosa_Behavior_Time_instant 1 (I.instOfNatNat 1))).
  Proof.
    intro Ht.
    apply (ari_subnat_source_transport _ (tR + 1) _ (Logic.eq_sym (addn1 tR))).
    exact (sub_add_correspondence _ _ 1 _ Ht (@Lean.eq_refl _ _)).
  Qed.

  Lemma task_arrivals_up_to_correspondence (tskR tskL : Task) tR tL :
    Lean.eq tskR tskL -> SubNatRel tR tL ->
    ArListRel (@task_arrivals_up_to Job Task jtR arrR tskR tR)
      (I.Prosa_Model_Task_Arrivals_task_arrivals_up_to Job dJ Task dT jtL arrL tskL tL).
  Proof.
    intros Htsk Ht.
    exact (task_arrivals_between_correspondence tskR tskL _ _ _ _ Htsk
      (sub_nat_rel_canonical O) (ari_succ_related tR tL Ht)).
  Qed.

  Lemma task_arrivals_before_correspondence (tskR tskL : Task) tR tL :
    Lean.eq tskR tskL -> SubNatRel tR tL ->
    ArListRel (@task_arrivals_before Job Task jtR arrR tskR tR)
      (I.Prosa_Model_Task_Arrivals_task_arrivals_before Job dJ Task dT jtL arrL tskL tL).
  Proof.
    intros Htsk Ht.
    exact (task_arrivals_between_correspondence tskR tskL _ _ _ _ Htsk
      (sub_nat_rel_canonical O) Ht).
  Qed.

  Lemma task_arrivals_at_correspondence (tskR tskL : Task) tR tL :
    Lean.eq tskR tskL -> SubNatRel tR tL ->
    ArListRel (@task_arrivals_at Job Task jtR arrR tskR tR)
      (I.Prosa_Model_Task_Arrivals_task_arrivals_at Job dJ Task dT jtL arrL tskL tL).
  Proof.
    intros Htsk Ht.
    exact (ar_filter_related Job _ _ _ _ (job_of_task_related tskR tskL Htsk)
      (arrivals_at_correspondence_certificate Job arrR arrL Harr _ _ Ht)).
  Qed.

  Lemma number_of_task_arrivals_correspondence (tskR tskL : Task) t1R t1L t2R t2L :
    Lean.eq tskR tskL -> SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@number_of_task_arrivals Job Task jtR arrR tskR t1R t2R)
      (I.Prosa_Model_Task_Arrivals_number_of_task_arrivals Job dJ Task dT jtL arrL tskL t1L t2L).
  Proof.
    intros Htsk H1 H2.
    exact (ari_size_related Job _ _
      (task_arrivals_between_correspondence tskR tskL _ _ _ _ Htsk H1 H2)).
  Qed.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).

  Lemma cost_of_task_arrivals_correspondence (tskR tskL : Task) t1R t1L t2R t2L :
    Lean.eq tskR tskL -> SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@cost_of_task_arrivals Job Task jtR costR arrR tskR t1R t2R)
      (I.Prosa_Model_Task_Arrivals_cost_of_task_arrivals Job dJ Task dT jtL costL arrL tskL t1L t2L).
  Proof.
    intros Htsk H1 H2.
    exact (ari_sum_related Job _ _ _ _ Hcost
      (task_arrivals_between_correspondence tskR tskL _ _ _ _ Htsk H1 H2)).
  Qed.

  Variable dlR : prosa.behavior.job.JobDeadline Job.
  Variable dlL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
  Hypothesis Hdl : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
      (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).

  Lemma task_arrivals_with_deadline_within_correspondence (tskR tskL : Task)
      t1R t1L t2R t2L :
    Lean.eq tskR tskL -> SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    ArListRel (@task_arrivals_with_deadline_within Job Task jtR arrR tskR dlR t1R t2R)
      (I.Prosa_Model_Task_Arrivals_task_arrivals_with_deadline_within
        Job dJ Task dT jtL arrL tskL dlL t1L t2L).
  Proof.
    intros Htsk H1 H2.
    refine (ar_filter_related Job _ _ _ _ _
      (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2)).
    intro j.
    exact (ar_bool_and_related _ _ _ _ (job_of_task_related tskR tskL Htsk j)
      (ar_decide_le_related _ _ _ _ (Hdl j) H2)).
  Qed.

  Lemma number_of_task_arrivals_with_deadline_within_correspondence
      (tskR tskL : Task) t1R t1L t2R t2L :
    Lean.eq tskR tskL -> SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@number_of_task_arrivals_with_deadline_within Job Task jtR arrR tskR dlR t1R t2R)
      (I.Prosa_Model_Task_Arrivals_number_of_task_arrivals_with_deadline_within
        Job dJ Task dT jtL arrL tskL dlL t1L t2L).
  Proof.
    intros Htsk H1 H2.
    exact (ari_size_related Job _ _
      (task_arrivals_with_deadline_within_correspondence tskR tskL _ _ _ _ Htsk H1 H2)).
  Qed.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

  Lemma task_arrivals_up_to_job_arrival_correspondence (j : Job) :
    ArListRel (@task_arrivals_up_to_job_arrival Job Task jtR jaR arrR j)
      (I.Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival
        Job dJ Task dT jtL jaL arrL j).
  Proof. exact (task_arrivals_up_to_correspondence _ _ _ _ (Hjt j) (Hja j)). Qed.

  Lemma task_arrivals_before_job_arrival_correspondence (j : Job) :
    ArListRel (@task_arrivals_before_job_arrival Job Task jtR jaR arrR j)
      (I.Prosa_Model_Task_Arrivals_task_arrivals_before_job_arrival
        Job dJ Task dT jtL jaL arrL j).
  Proof. exact (task_arrivals_before_correspondence _ _ _ _ (Hjt j) (Hja j)). Qed.

  Lemma task_arrivals_at_job_arrival_correspondence (j : Job) :
    ArListRel (@task_arrivals_at_job_arrival Job Task jtR jaR arrR j)
      (I.Prosa_Model_Task_Arrivals_task_arrivals_at_job_arrival
        Job dJ Task dT jtL jaL arrL j).
  Proof. exact (task_arrivals_at_correspondence _ _ _ _ (Hjt j) (Hja j)). Qed.

  Lemma job_index_correspondence (j : Job) :
    SubNatRel (@job_index Task Job jaR jtR arrR j)
      (I.Prosa_Model_Task_Arrivals_job_index Task dT Job dJ jaL jtL arrL j).
  Proof.
    exact (ari_index_related Job j _ _ (task_arrivals_up_to_job_arrival_correspondence j)).
  Qed.

  Lemma prev_job_correspondence (j : Job) :
    Lean.eq (@prev_job Job Task jtR jaR arrR j)
      (I.Prosa_Model_Task_Arrivals_prev_job Job dJ Task dT jtL jaL arrL j).
  Proof.
    exact (ari_nth_related Job j _ _ _ _
      (task_arrivals_up_to_job_arrival_correspondence j)
      (ari_nat_sub_related _ _ 1 _ (job_index_correspondence j) (@Lean.eq_refl _ _))).
  Qed.
End ArrivalsCorrespondence.

Print Assumptions task_arrivals_between_correspondence.
Print Assumptions cost_of_task_arrivals_correspondence.
Print Assumptions prev_job_correspondence.
