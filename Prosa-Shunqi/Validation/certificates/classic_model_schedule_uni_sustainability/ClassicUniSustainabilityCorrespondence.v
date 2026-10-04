From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.schedule.uni.schedule classic.model.schedule.uni.schedulability classic.model.schedule.uni.sustainability.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniSustainability.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniSustainabilityBase ClassicUniSustainabilityList ClassicUniSustainabilityList1.



Module I := ImportedClassicUniSustainability.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/sustainability.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by its decision procedure
    ([ct_decidable_eq]); labels by the constructor bijection; parameter functions pointwise through [SubNatRel]; job
    parameters through their label and the canonical conversion of their function field; schedules and arrival
    sequences pointwise.  Equalities of job parameters and of parameter functions use Rocq functional
    extensionality (user decision 2026-10-03, ranks 86 and 166 only). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma csu_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma csu_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma csu_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) csu_false_rel). Qed.

Lemma csu_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma csu_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma csu_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma csu_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma csu_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma csu_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (csu_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => csu_unmap_rel T l) PR PL).
Qed.

Definition CsuParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma csu_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CsuParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (csu_forall_cover _ _ (CsuParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint csu_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (csu_natl s') end.

Definition csu_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma csu_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma csu_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma csu_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma csu_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH csu_cl_append. reflexivity.
Qed.

Lemma csu_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsuFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CsuArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition csu_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition csu_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma csu_arr_canonical aR : CsuArrRel aR (csu_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /csu_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma csu_arr_surjective aL : CsuArrRel (csu_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma csu_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CsuArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (csu_forall_cover _ _ CsuArrRel csu_arr_to_target csu_arr_to_source csu_arr_canonical csu_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

End ArrivalDefs2.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition csu_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition csu_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma csu_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma csu_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (csu_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CsuSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition csu_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition csu_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma csu_sched_canonical sR : CsuSchedRel sR (csu_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /csu_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma csu_sched_surjective sL : CsuSchedRel (csu_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /csu_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma csu_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CsuSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (csu_forall_cover _ _ CsuSchedRel csu_sched_to_target csu_sched_to_source csu_sched_canonical csu_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma csu_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CsuSchedRel Job sR (csu_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CsuSchedRel Job (csu_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (csu_sched_canonical Job) (csu_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CsuSchedRel Job sR sL.

End USchedDefs.

(* ------------------------------------------------------------------ *)
(** * Functional extensionality (user decision 2026-10-03: admitted for this file and rank 166 only)

    Job-parameter records hold functions; relating Rocq [=] with Lean [Eq] on such records and on parameter
    functions needs extensional equality of functions, which Lean proves (quotients) and Rocq takes as the axiom
    [functional_extensionality_dep]. *)
From Stdlib Require Import FunctionalExtensionality.

(** the [eqType] structure of the labels (HB instance of the source module) *)
Import (canonicals) Sustainability.

Notation cfc_EQ H := (imported_eq_to_coq_eq _ _ H).

(** SProp evidence boxed into Prop (the inverse direction of [StrictlyInhabited]). *)
Inductive CsuBox (Q : SProp) : Prop := csu_box : Q -> CsuBox Q.
Definition csu_unbox (Q : SProp) (b : CsuBox Q) : Q := match b with csu_box q => q end.

Lemma csu_box_rel (Q : SProp) : PropSPropRel (CsuBox Q) Q.
Proof. apply prop_sprop_rel_intro; [exact (csu_unbox Q) | intro q; apply strictly_inhabits; exact (csu_box Q q)]. Qed.

Lemma csu_strict_rel (P : Prop) : PropSPropRel P (StrictlyInhabited P).
Proof. apply prop_sprop_rel_intro; [exact (fun p => strictly_inhabits p) | intro s; exact s]. Qed.

(** Propositions (Rocq [Prop]) against Lean propositions (imported [SProp]), related by [PropSPropRel]. *)
Lemma csu_forall_prop (PR : Prop -> Prop) (PL : SProp -> SProp) :
  (forall P Q, PropSPropRel P Q -> PropSPropRel (PR P) (PL Q)) -> PropSPropRel (forall P, PR P) (forall Q, PL Q).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR Q. exact (prop_to_sprop _ _ (H (CsuBox Q) Q (csu_box_rel Q)) (HR _)).
  - intros HL. apply strictly_inhabits. intro P. exact (sprop_to_prop _ _ (H P (StrictlyInhabited P) (csu_strict_rel P)) (HL _)).
Qed.

(** Predicates on a common type, pointwise by [PropSPropRel]. *)
Lemma csu_forall_pred (T : Type) (PR : (T -> Prop) -> Prop) (PL : (T -> SProp) -> SProp) :
  (forall pR pL, (forall x, PropSPropRel (pR x) (pL x)) -> PropSPropRel (PR pR) (PL pL)) ->
  PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR pL. exact (prop_to_sprop _ _ (H (fun x => CsuBox (pL x)) pL (fun x => csu_box_rel (pL x))) (HR _)).
  - intros HL. apply strictly_inhabits. intro pR.
    exact (sprop_to_prop _ _ (H pR (fun x => StrictlyInhabited (pR x)) (fun x => csu_strict_rel (pR x))) (HL _)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Job-parameter labels: the constructor bijection *)

Notation LLab := (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label).

Definition csu_lab (l : Sustainability.parameter_label) : LLab :=
  match l with
  | Sustainability.JOB_ARRIVAL => I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_ARRIVAL
  | Sustainability.JOB_COST => I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_COST
  | Sustainability.JOB_DEADLINE => I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_DEADLINE
  | Sustainability.JOB_JITTER => I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_JITTER
  | Sustainability.JOB_SUSPENSION => I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_SUSPENSION
  end.

Definition csu_unlab (l : LLab) : Sustainability.parameter_label :=
  match l with
  | I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_ARRIVAL => Sustainability.JOB_ARRIVAL
  | I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_COST => Sustainability.JOB_COST
  | I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_DEADLINE => Sustainability.JOB_DEADLINE
  | I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_JITTER => Sustainability.JOB_JITTER
  | I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_SUSPENSION => Sustainability.JOB_SUSPENSION
  end.

(** Transparent (the label transport below computes on constructors). *)
Definition csu_lab_unlab (l : LLab) : Logic.eq (csu_lab (csu_unlab l)) l :=
  match l as l0 return Logic.eq (csu_lab (csu_unlab l0)) l0 with
  | I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_ARRIVAL => Logic.eq_refl
  | I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_COST => Logic.eq_refl
  | I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_DEADLINE => Logic.eq_refl
  | I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_JITTER => Logic.eq_refl
  | I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_JOB_SUSPENSION => Logic.eq_refl
  end.

Definition csu_unlab_lab (l : Sustainability.parameter_label) : Logic.eq (csu_unlab (csu_lab l)) l :=
  match l as l0 return Logic.eq (csu_unlab (csu_lab l0)) l0 with
  | Sustainability.JOB_ARRIVAL => Logic.eq_refl
  | Sustainability.JOB_COST => Logic.eq_refl
  | Sustainability.JOB_DEADLINE => Logic.eq_refl
  | Sustainability.JOB_JITTER => Logic.eq_refl
  | Sustainability.JOB_SUSPENSION => Logic.eq_refl
  end.

Lemma csu_lab_inj l1 l2 : Logic.eq (csu_lab l1) (csu_lab l2) -> Logic.eq l1 l2.
Proof. move=> E. by rewrite -(csu_unlab_lab l1) E csu_unlab_lab. Qed.

(** Label-valued terms are related through the bijection. *)
Definition CsuLabRel (lR : Sustainability.parameter_label) (lL : LLab) : SProp := Lean.eq (csu_lab lR) lL.

Lemma csu_forall_lab (PR : Sustainability.parameter_label -> Prop) (PL : LLab -> SProp) :
  (forall lR lL, CsuLabRel lR lL -> PropSPropRel (PR lR) (PL lL)) -> PropSPropRel (forall l, PR l) (forall l, PL l).
Proof.
  exact (csu_forall_cover _ _ CsuLabRel csu_lab csu_unlab (fun l => @Lean.eq_refl _ _)
           (fun l => coq_eq_to_imported_eq _ _ (csu_lab_unlab l)) PR PL).
Qed.

Lemma csu_exists_lab (PR : Sustainability.parameter_label -> Prop) (PL : LLab -> SProp) :
  (forall lR lL, CsuLabRel lR lL -> PropSPropRel (PR lR) (PL lL)) -> PropSPropRel (exists l, PR l) (I.Exists LLab PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [l Hl]. exact (I.Exists_intro _ _ (csu_lab l) (prop_to_sprop _ _ (H l _ (@Lean.eq_refl _ _)) Hl)).
  - intros [lL HL]. apply strictly_inhabits. exists (csu_unlab lL).
    exact (sprop_to_prop _ _ (H _ _ (coq_eq_to_imported_eq _ _ (csu_lab_unlab lL))) HL).
Qed.

Lemma csu_lab_eq_rel aR aL (Ha : CsuLabRel aR aL) bR bL (Hb : CsuLabRel bR bL) :
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  destruct Ha, Hb. apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. exact (csu_lab_inj _ _ (imported_eq_to_coq_eq _ _ E)).
Qed.

Lemma csu_lab_eqb_rel aR aL (Ha : CsuLabRel aR aL) bR bL (Hb : CsuLabRel bR bL) d :
  CtBoolRel (aR == bR) (I.Decidable_decide (Lean.eq aL bL) d).
Proof.
  apply: ct_decide_bool. have E := csu_lab_eq_rel aR aL Ha bR bL Hb. apply prop_sprop_rel_intro.
  - move=> /eqP H. exact (prop_to_sprop _ _ E H).
  - move=> H. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ E H).
Qed.

(** Sequences of labels, elementwise through the bijection. *)
Lemma csu_forall_labs (PR : seq Sustainability.parameter_label -> Prop) (PL : I.List_inst1 LLab -> SProp) :
  (forall sR sL, ClListRel1 csu_lab sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl1_forall_list csu_lab csu_unlab csu_lab_unlab PR PL). Qed.

Lemma csu_labs_mem lR lL (Hl : CsuLabRel lR lL) sR sL (Hs : ClListRel1 csu_lab sR sL) :
  PropSPropRel (lR \in sR) (I.Membership_mem_inst3 LLab (I.List_inst1 LLab) (I.List_instMembership_inst1 LLab) sL lL).
Proof.
  destruct Hl. exact (cl1_mem_rel_list Sustainability.parameter_label LLab csu_lab csu_unlab csu_unlab_lab lR sR sL Hs).
Qed.

Lemma csu_labs_notin lR lL (Hl : CsuLabRel lR lL) sR sL (Hs : ClListRel1 csu_lab sR sL) :
  PropSPropRel (is_true (lR \notin sR)) (I.Not (I.Membership_mem_inst3 LLab (I.List_inst1 LLab) (I.List_instMembership_inst1 LLab) sL lL)).
Proof.
  have M := csu_labs_mem lR lL Hl sR sL Hs. apply prop_sprop_rel_intro.
  - move=> /negP N HL. exact (ct_coq_false_to_target (N (sprop_to_prop _ _ M HL))).
  - intro N. apply strictly_inhabits. apply/negP => Hm.
    exact (interpret_strict _ (ct_target_false_to_strict (N (prop_to_sprop _ _ M Hm)))).
Qed.

Lemma csu_labs_cons aR aL (Ha : CsuLabRel aR aL) sR sL (Hs : ClListRel1 csu_lab sR sL) :
  ClListRel1 csu_lab (aR :: sR) (I.List_cons_inst1 LLab aL sL).
Proof. destruct Ha. rewrite -(cfc_EQ Hs). exact (@Lean.eq_refl _ _). Qed.

Lemma csu_labs_nil : ClListRel1 csu_lab [::] (I.List_nil_inst1 LLab).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma csu_labs_uniq sR sL (Hs : ClListRel1 csu_lab sR sL) : PropSPropRel (uniq sR) (I.List_Nodup_inst1 LLab sL).
Proof. exact (cl1_uniq_rel_list _ _ csu_lab csu_unlab csu_unlab_lab csu_lab_unlab sR sL Hs). Qed.

(* ------------------------------------------------------------------ *)
(** * Job-parameter functions: [type_of_label] related per label *)

Section Tol.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LTol l := (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_type_of_label Job dJ l).
Notation RTol l := (@Sustainability.type_of_label Job l).

Definition csu_tol_to_target (l : Sustainability.parameter_label) : RTol l -> LTol (csu_lab l) :=
  match l as l0 return RTol l0 -> LTol (csu_lab l0) with
  | Sustainability.JOB_ARRIVAL => fun f j => sub_nat_to_imported (f j)
  | Sustainability.JOB_COST => fun f j => sub_nat_to_imported (f j)
  | Sustainability.JOB_DEADLINE => fun f j => sub_nat_to_imported (f j)
  | Sustainability.JOB_JITTER => fun f j => sub_nat_to_imported (f j)
  | Sustainability.JOB_SUSPENSION => fun f j t => sub_nat_to_imported (f j (sub_nat_to_rocq t))
  end.

Definition csu_tol_to_source (l : Sustainability.parameter_label) : LTol (csu_lab l) -> RTol l :=
  match l as l0 return LTol (csu_lab l0) -> RTol l0 with
  | Sustainability.JOB_ARRIVAL => fun g j => sub_nat_to_rocq (g j)
  | Sustainability.JOB_COST => fun g j => sub_nat_to_rocq (g j)
  | Sustainability.JOB_DEADLINE => fun g j => sub_nat_to_rocq (g j)
  | Sustainability.JOB_JITTER => fun g j => sub_nat_to_rocq (g j)
  | Sustainability.JOB_SUSPENSION => fun g j t => sub_nat_to_rocq (g j (sub_nat_to_imported t))
  end.

Definition CsuTolRel (l : Sustainability.parameter_label) : RTol l -> LTol (csu_lab l) -> SProp :=
  match l as l0 return RTol l0 -> LTol (csu_lab l0) -> SProp with
  | Sustainability.JOB_ARRIVAL => fun f g => forall j, SubNatRel (f j) (g j)
  | Sustainability.JOB_COST => fun f g => forall j, SubNatRel (f j) (g j)
  | Sustainability.JOB_DEADLINE => fun f g => forall j, SubNatRel (f j) (g j)
  | Sustainability.JOB_JITTER => fun f g => forall j, SubNatRel (f j) (g j)
  | Sustainability.JOB_SUSPENSION => fun f g => forall j tR tL, SubNatRel tR tL -> SubNatRel (f j tR) (g j tL)
  end.

Lemma csu_tol_canonical l f : CsuTolRel l f (csu_tol_to_target l f).
Proof.
  destruct l; cbn; intros; try exact (sub_nat_rel_canonical _).
  match goal with Ht : SubNatRel ?tR ?tL |- _ => rewrite (cl_nat_logic _ _ Ht) sub_nat_rocq_roundtrip end.
  exact (sub_nat_rel_canonical _).
Qed.

Lemma csu_tol_surjective l g : CsuTolRel l (csu_tol_to_source l g) g.
Proof.
  destruct l; cbn; intros; try exact (sub_nat_rel_surjective _).
  match goal with Ht : SubNatRel ?tR ?tL |- _ => rewrite (cl_nat_logic _ _ Ht) end.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma csu_tol_tgt_src l g : Logic.eq (csu_tol_to_target l (csu_tol_to_source l g)) g.
Proof.
  destruct l; cbn; apply: functional_extensionality => j.
  1-4: exact (Logic.eq_sym (cl_nat_logic _ _ (sub_nat_rel_surjective (g j)))).
  apply: functional_extensionality => t. rewrite -(cl_nat_logic _ _ (sub_nat_rel_surjective t)).
  exact (Logic.eq_sym (cl_nat_logic _ _ (sub_nat_rel_surjective (g j t)))).
Qed.

Lemma csu_tol_src_tgt l f : Logic.eq (csu_tol_to_source l (csu_tol_to_target l f)) f.
Proof.
  destruct l; cbn; apply: functional_extensionality => j.
  1-4: exact (sub_nat_rocq_roundtrip _).
  apply: functional_extensionality => t. by rewrite !sub_nat_rocq_roundtrip.
Qed.

Lemma csu_tol_fun_tgt l f g : CsuTolRel l f g -> Logic.eq g (csu_tol_to_target l f).
Proof.
  destruct l; cbn => H; apply: functional_extensionality => j.
  1-4: exact (cl_nat_logic _ _ (H j)).
  apply: functional_extensionality => t.
  exact (cl_nat_logic _ _ (H j _ t (sub_nat_rel_surjective t))).
Qed.

Lemma csu_tol_fun_src l f g : CsuTolRel l f g -> Logic.eq f (csu_tol_to_source l g).
Proof.
  move=> H. rewrite (csu_tol_fun_tgt l f g H). exact (Logic.eq_sym (csu_tol_src_tgt l f)).
Qed.

Lemma csu_tol_eq_rel l fR fL (Hf : CsuTolRel l fR fL) gR gL (Hg : CsuTolRel l gR gL) :
  PropSPropRel (Logic.eq fR gR) (Lean.eq fL gL).
Proof.
  rewrite (csu_tol_fun_tgt l fR fL Hf) (csu_tol_fun_tgt l gR gL Hg). apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits.
    rewrite -(csu_tol_src_tgt l fR) -(csu_tol_src_tgt l gR). exact (f_equal _ (imported_eq_to_coq_eq _ _ E)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Job parameters: related through the canonical conversion of the function field *)

Notation LJp := (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_job_parameter Job dJ).
Notation RJp := (@Sustainability.job_parameter Job).

Definition csu_jp_to_target (p : RJp) : LJp :=
  I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_job_parameter_param Job dJ (csu_lab (Sustainability.p_label p)) (csu_tol_to_target _ (Sustainability.p_function p)).

Definition csu_cast (x : LLab) (v : LTol x) : LTol (csu_lab (csu_unlab x)) :=
  match Logic.eq_sym (csu_lab_unlab x) in Logic.eq _ z return LTol z with Logic.eq_refl => v end.

Definition csu_jp_to_source (q : LJp) : RJp :=
  Sustainability.param (csu_unlab (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_job_parameter_p_label Job dJ q))
    (csu_tol_to_source _ (csu_cast _ (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_job_parameter_p_function Job dJ q))).

Lemma csu_jp_src_tgt p : Logic.eq (csu_jp_to_source (csu_jp_to_target p)) p.
Proof. destruct p as [l f]; destruct l; rewrite /csu_jp_to_source /=; f_equal; exact (csu_tol_src_tgt _ f). Qed.

Lemma csu_jp_tgt_src q : Logic.eq (csu_jp_to_target (csu_jp_to_source q)) q.
Proof.
  destruct q as [l g]; destruct l; rewrite /csu_jp_to_target /=; f_equal;
    apply: functional_extensionality => j;
    first [ exact (Logic.eq_sym (cl_nat_logic _ _ (sub_nat_rel_surjective _)))
          | apply: functional_extensionality => t; rewrite -(cl_nat_logic _ _ (sub_nat_rel_surjective t));
            exact (Logic.eq_sym (cl_nat_logic _ _ (sub_nat_rel_surjective _))) ].
Qed.

Lemma csu_jp_inj p1 p2 : Logic.eq (csu_jp_to_target p1) (csu_jp_to_target p2) -> Logic.eq p1 p2.
Proof. move=> E. by rewrite -(csu_jp_src_tgt p1) -(csu_jp_src_tgt p2) E. Qed.

Definition CsuJpRel (p : RJp) (q : LJp) : SProp := Lean.eq (csu_jp_to_target p) q.

Lemma csu_forall_jp (PR : RJp -> Prop) (PL : LJp -> SProp) :
  (forall pR pL, CsuJpRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (csu_forall_cover _ _ CsuJpRel csu_jp_to_target csu_jp_to_source (fun p => @Lean.eq_refl _ _)
           (fun q => coq_eq_to_imported_eq _ _ (csu_jp_tgt_src q)) PR PL).
Qed.

Lemma csu_forall_jps (PR : seq RJp -> Prop) (PL : I.List LJp -> SProp) :
  (forall sR sL, ClListRel csu_jp_to_target sR sL -> PropSPropRel (PR sR) (PL sL)) ->
  PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl_forall_list csu_jp_to_target csu_jp_to_source csu_jp_tgt_src PR PL). Qed.

Lemma csu_exists_jps (PR : seq RJp -> Prop) (PL : I.List LJp -> SProp) :
  (forall sR sL, ClListRel csu_jp_to_target sR sL -> PropSPropRel (PR sR) (PL sL)) ->
  PropSPropRel (exists s, PR s) (I.Exists (I.List LJp) PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [s Hs]. exact (I.Exists_intro _ _ (cl_map csu_jp_to_target s) (prop_to_sprop _ _ (H s _ (@Lean.eq_refl _ _)) Hs)).
  - intros [sL HL]. apply strictly_inhabits. exists (cl_unmap csu_jp_to_source sL).
    exact (sprop_to_prop _ _ (H _ _ (cl_lean_eq _ _ _ (cl_map_unmap csu_jp_to_target csu_jp_to_source csu_jp_tgt_src sL))) HL).
Qed.

Lemma csu_jp_label pR pL (H : CsuJpRel pR pL) : CsuLabRel (Sustainability.p_label pR) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_job_parameter_p_label Job dJ pL).
Proof. destruct H. exact (@Lean.eq_refl _ _). Qed.

Lemma csu_jp_eq_rel aR aL (Ha : CsuJpRel aR aL) bR bL (Hb : CsuJpRel bR bL) :
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  destruct Ha, Hb. apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. exact (csu_jp_inj _ _ (imported_eq_to_coq_eq _ _ E)).
Qed.

(** [List.In] against Lean list membership. *)
Fixpoint csu_in_forward (x : RJp) (s : seq RJp) {struct s} :
  List.In x s -> I.List_Mem LJp (csu_jp_to_target x) (cl_map csu_jp_to_target s) :=
  match s as s0 return List.In x s0 -> I.List_Mem LJp (csu_jp_to_target x) (cl_map csu_jp_to_target s0) with
  | [::] => fun H => match H with end
  | y :: s' => fun H =>
      match H with
      | or_introl E =>
          match E in Logic.eq _ z return I.List_Mem LJp (csu_jp_to_target z) (I.List_cons LJp (csu_jp_to_target y) (cl_map csu_jp_to_target s')) with
          | Logic.eq_refl => I.List_Mem_head LJp (csu_jp_to_target y) _
          end
      | or_intror H' => I.List_Mem_tail LJp (csu_jp_to_target x) (csu_jp_to_target y) _ (csu_in_forward x s' H')
      end
  end.

Fixpoint csu_in_backward (a : LJp) (l : I.List LJp) (H : I.List_Mem LJp a l) :
  StrictlyInhabited (List.In (csu_jp_to_source a) (cl_unmap csu_jp_to_source l)) :=
  match H with
  | I.List_Mem_head l' => strictly_inhabits (or_introl Logic.eq_refl)
  | I.List_Mem_tail y l' Ht =>
      match csu_in_backward a l' Ht with
      | strictly_inhabits Hm => strictly_inhabits (or_intror Hm)
      end
  end.

Lemma csu_in_rel xR xL (Hx : CsuJpRel xR xL) sR sL (Hs : ClListRel csu_jp_to_target sR sL) :
  PropSPropRel (List.In xR sR) (I.Membership_mem LJp (I.List LJp) (I.List_instMembership LJp) sL xL).
Proof.
  destruct Hx. rewrite -(cfc_EQ Hs). apply prop_sprop_rel_intro; first exact (csu_in_forward xR sR).
  intro H. have S := csu_in_backward _ _ H.
  rewrite csu_jp_src_tgt (cl_unmap_map csu_jp_to_target csu_jp_to_source csu_jp_src_tgt) in S. exact S.
Qed.

End Tol.

(* ------------------------------------------------------------------ *)
(** * Logical connectives not in the base library *)

Lemma csu_not_rel (P : Prop) (Q : SProp) : PropSPropRel P Q -> PropSPropRel (~ P) (I.Not Q).
Proof.
  intro M. apply prop_sprop_rel_intro.
  - intros N q. exact (ct_coq_false_to_target (N (sprop_to_prop _ _ M q))).
  - intro N. apply strictly_inhabits. intro p. exact (interpret_strict _ (ct_target_false_to_strict (N (prop_to_sprop _ _ M p)))).
Qed.

Lemma csu_iff (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [f g]. apply I.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ (f (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP (g (sprop_to_prop _ _ HQ q))).
  - intros [f g]. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ (f (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP (g (prop_to_sprop _ _ HQ q))).
Qed.

Lemma csu_ite_dec (A : Type) (P : SProp) (dec : I.Decidable P) bR (Hb : CtBoolRel bR (I.Decidable_decide P dec)) (a b : A) :
  Logic.eq (I.ite A P dec a b) (if bR then a else b).
Proof.
  have E := ct_bool_rel_logic _ _ Hb. clear Hb. move: E.
  case: dec => [h|h] E; destruct bR; try reflexivity; discriminate E.
Qed.

Section SusDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LTol l := (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_type_of_label Job dJ l).
Notation RTol l := (@Sustainability.type_of_label Job l).
Notation LJp := (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_job_parameter Job dJ).
Notation RJp := (@Sustainability.job_parameter Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Notation tgt := (csu_jp_to_target Job).
Notation src := (csu_jp_to_source Job).
Notation JpsRel := (ClListRel (csu_jp_to_target Job)).

(** Related schedules and arrival sequences are each other's conversions (extensionally). *)
Lemma csu_sched_fun_src sR sL (H : CsuSchedRel Job sR sL) : Logic.eq sR (csu_sched_to_source Job sL).
Proof.
  apply: functional_extensionality => t. rewrite /csu_sched_to_source.
  rewrite -(imported_eq_to_coq_eq _ _ (H t _ (sub_nat_rel_canonical t))). by rewrite cl_unopt_opt.
Qed.

Lemma csu_sched_fun_tgt sR sL (H : CsuSchedRel Job sR sL) : Logic.eq sL (csu_sched_to_target Job sR).
Proof.
  apply: functional_extensionality => t. rewrite /csu_sched_to_target.
  exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ (H _ t (sub_nat_rel_surjective t)))).
Qed.

Lemma csu_arr_fun_src aR aL (H : CsuArrRel Job aR aL) : Logic.eq aR (csu_arr_to_source Job aL).
Proof.
  apply: functional_extensionality => t. rewrite /csu_arr_to_source.
  rewrite (cl_list_logic _ _ _ (H t _ (sub_nat_rel_canonical t))).
  exact (Logic.eq_sym (cl_unmap_map cid cid (fun _ => Logic.eq_refl _) _)).
Qed.

Lemma csu_arr_fun_tgt aR aL (H : CsuArrRel Job aR aL) : Logic.eq aL (csu_arr_to_target Job aR).
Proof.
  apply: functional_extensionality => t. rewrite /csu_arr_to_target.
  exact (cl_list_logic _ _ _ (H _ t (sub_nat_rel_surjective t))).
Qed.

Lemma csu_jps_fun_src sR sL (H : JpsRel sR sL) : Logic.eq sR (cl_unmap src sL).
Proof. rewrite (cl_list_logic _ _ _ H). exact (Logic.eq_sym (cl_unmap_map tgt src (csu_jp_src_tgt Job) sR)). Qed.

Lemma csu_exists_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CsuArrRel Job aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (exists a, PR a) (I.Exists LArr PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [a Ha]. exact (I.Exists_intro _ _ (csu_arr_to_target Job a) (prop_to_sprop _ _ (H a _ (csu_arr_canonical Job a)) Ha)).
  - intros [aL HL]. apply strictly_inhabits. exists (csu_arr_to_source Job aL).
    exact (sprop_to_prop _ _ (H _ _ (csu_arr_surjective Job aL)) HL).
Qed.

Lemma csu_exists_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CsuSchedRel Job sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (exists s, PR s) (I.Exists LSched PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [s Hs]. exact (I.Exists_intro _ _ (csu_sched_to_target Job s) (prop_to_sprop _ _ (H s _ (csu_sched_canonical Job s)) Hs)).
  - intros [sL HL]. apply strictly_inhabits. exists (csu_sched_to_source Job sL).
    exact (sprop_to_prop _ _ (H _ _ (csu_sched_surjective Job sL)) HL).
Qed.

(** [is_schedulable]: related on related arguments. *)
Definition CsuIsRel (iR : seq RJp -> UniprocessorSchedule.schedule Job -> Job -> bool)
    (iL : I.List LJp -> LSched -> Job -> I.Bool) : SProp :=
  forall sR sL, JpsRel sR sL -> forall schR schL, CsuSchedRel Job schR schL -> forall j, CtBoolRel (iR sR schR j) (iL sL schL j).

Lemma csu_forall_is (PR : (seq RJp -> UniprocessorSchedule.schedule Job -> Job -> bool) -> Prop)
    (PL : (I.List LJp -> LSched -> Job -> I.Bool) -> SProp) :
  (forall iR iL, CsuIsRel iR iL -> PropSPropRel (PR iR) (PL iL)) -> PropSPropRel (forall i, PR i) (forall i, PL i).
Proof.
  apply: (csu_forall_cover _ _ CsuIsRel
            (fun iR sL schL j => ct_b2l (iR (cl_unmap src sL) (csu_sched_to_source Job schL) j))
            (fun iL sR schR j => ct_l2b (iL (cl_map tgt sR) (csu_sched_to_target Job schR) j))).
  - intros iR sR sL Hs schR schL Hsch j.
    rewrite -(csu_jps_fun_src sR sL Hs) -(csu_sched_fun_src schR schL Hsch). exact (ct_bool_canonical _).
  - intros iL sR sL Hs schR schL Hsch j.
    rewrite (cl_list_logic _ _ _ Hs) (csu_sched_fun_tgt schR schL Hsch). exact (ct_bool_surjective _).
Qed.

(** [belongs_to_task_model]: related on related arguments. *)
Definition CsuBtmRel (bR : seq RJp -> ArrivalSequence.arrival_sequence Job -> UniprocessorSchedule.schedule Job -> Prop)
    (bL : I.List LJp -> LArr -> LSched -> SProp) : SProp :=
  forall sR sL, JpsRel sR sL -> forall aR aL, CsuArrRel Job aR aL -> forall schR schL, CsuSchedRel Job schR schL ->
    StrictlyInhabited (PropSPropRel (bR sR aR schR) (bL sL aL schL)).

Lemma csu_forall_btm (PR : (seq RJp -> ArrivalSequence.arrival_sequence Job -> UniprocessorSchedule.schedule Job -> Prop) -> Prop)
    (PL : (I.List LJp -> LArr -> LSched -> SProp) -> SProp) :
  (forall bR bL, CsuBtmRel bR bL -> PropSPropRel (PR bR) (PL bL)) -> PropSPropRel (forall b, PR b) (forall b, PL b).
Proof.
  apply: (csu_forall_cover _ _ CsuBtmRel
            (fun bR sL aL schL => StrictlyInhabited (bR (cl_unmap src sL) (csu_arr_to_source Job aL) (csu_sched_to_source Job schL)))
            (fun bL sR aR schR => CsuBox (bL (cl_map tgt sR) (csu_arr_to_target Job aR) (csu_sched_to_target Job schR)))).
  - intros bR sR sL Hs aR aL Ha schR schL Hsch. apply strictly_inhabits.
    rewrite -(csu_jps_fun_src sR sL Hs) -(csu_arr_fun_src aR aL Ha) -(csu_sched_fun_src schR schL Hsch).
    exact (csu_strict_rel _).
  - intros bL sR sL Hs aR aL Ha schR schL Hsch. apply strictly_inhabits.
    rewrite (cl_list_logic _ _ _ Hs) (csu_arr_fun_tgt aR aL Ha) (csu_sched_fun_tgt schR schL Hsch).
    exact (csu_box_rel _).
Qed.

Lemma csu_btm_app bR bL (H : CsuBtmRel bR bL) sR sL (Hs : JpsRel sR sL) aR aL (Ha : CsuArrRel Job aR aL)
    schR schL (Hsch : CsuSchedRel Job schR schL) : PropSPropRel (bR sR aR schR) (bL sL aL schL).
Proof. exact (interpret_strict _ (H sR sL Hs aR aL Ha schR schL Hsch)). Qed.

(** [has_better_params] at a label: related on related parameter functions. *)
Definition CsuHbRel (l : Sustainability.parameter_label) (hR : RTol l -> RTol l -> Prop) (hL : LTol (csu_lab l) -> LTol (csu_lab l) -> SProp)
  : SProp :=
  forall fR fL, CsuTolRel Job l fR fL -> forall gR gL, CsuTolRel Job l gR gL ->
    StrictlyInhabited (PropSPropRel (hR fR gR) (hL fL gL)).

Lemma csu_forall_hb l (PR : (RTol l -> RTol l -> Prop) -> Prop) (PL : (LTol (csu_lab l) -> LTol (csu_lab l) -> SProp) -> SProp) :
  (forall hR hL, CsuHbRel l hR hL -> PropSPropRel (PR hR) (PL hL)) -> PropSPropRel (forall h, PR h) (forall h, PL h).
Proof.
  apply: (csu_forall_cover _ _ (CsuHbRel l)
            (fun hR fL gL => StrictlyInhabited (hR (csu_tol_to_source Job l fL) (csu_tol_to_source Job l gL)))
            (fun hL fR gR => CsuBox (hL (csu_tol_to_target Job l fR) (csu_tol_to_target Job l gR)))).
  - intros hR fR fL Hf gR gL Hg. apply strictly_inhabits.
    rewrite -(csu_tol_fun_src Job l fR fL Hf) -(csu_tol_fun_src Job l gR gL Hg). exact (csu_strict_rel _).
  - intros hL fR fL Hf gR gL Hg. apply strictly_inhabits.
    rewrite (csu_tol_fun_tgt Job l fR fL Hf) (csu_tol_fun_tgt Job l gR gL Hg). exact (csu_box_rel _).
Qed.

Lemma csu_hb_app l hR hL (H : CsuHbRel l hR hL) fR fL (Hf : CsuTolRel Job l fR fL) gR gL (Hg : CsuTolRel Job l gR gL) :
  PropSPropRel (hR fR gR) (hL fL gL).
Proof. exact (interpret_strict _ (H fR fL Hf gR gL Hg)). Qed.

(** Job-parameter functions (the [Job -> time] and suspension binders of the examples). *)
Lemma csu_forall_tol l (PR : RTol l -> Prop) (PL : LTol (csu_lab l) -> SProp) :
  (forall fR fL, CsuTolRel Job l fR fL -> PropSPropRel (PR fR) (PL fL)) -> PropSPropRel (forall f, PR f) (forall f, PL f).
Proof. exact (csu_forall_cover _ _ (CsuTolRel Job l) (csu_tol_to_target Job l) (csu_tol_to_source Job l)
                (csu_tol_canonical Job l) (csu_tol_surjective Job l) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Job-parameter lookup *)

Lemma csu_default_tgt l : Logic.eq (csu_tol_to_target Job l (@Sustainability.default_val Job l)) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_default_val Job dJ (csu_lab l)).
Proof. destruct l; cbn; repeat (apply: functional_extensionality => ?); reflexivity. Qed.

Lemma csu_get_same l f : Logic.eq (@Sustainability.get_param_function Job l (Sustainability.param l f)) f.
Proof.
  rewrite /Sustainability.get_param_function /=.
  case: (Sustainability.parameter_label_eq_dec l l) => [E|NE]; last by exfalso; apply: NE.
  by rewrite (Eqdep_dec.UIP_dec Sustainability.parameter_label_eq_dec E Logic.eq_refl).
Qed.

Lemma csu_get_other l l' f : l' <> l -> Logic.eq (@Sustainability.get_param_function Job l (Sustainability.param l' f)) (@Sustainability.default_val Job l).
Proof.
  move=> NE. rewrite /Sustainability.get_param_function /=.
  by case: (Sustainability.parameter_label_eq_dec l' l) => [E|_]; first by exfalso; apply: NE.
Qed.

Lemma csu_find_param_nil l :
  Logic.eq (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_find_param Job dJ (csu_lab l) (I.List_nil LJp))
           (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_job_parameter_param Job dJ (csu_lab l) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_default_val Job dJ (csu_lab l))).
Proof. exact (cfc_EQ (I.Prosa_Validation_ClassicUniSustainabilityInterface_xsu_find_param_nil Job dJ (csu_lab l))). Qed.

Theorem Sustainability_find_param_correspondence l sR sL (Hs : JpsRel sR sL) :
  CsuJpRel Job (@Sustainability.find_param Job l sR) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_find_param Job dJ (csu_lab l) sL).
Proof.
  rewrite -(cfc_EQ Hs). clear Hs. apply: coq_eq_to_imported_eq.
  elim: sR => [|p s IH].
  - rewrite /Sustainability.find_param /= csu_find_param_nil /csu_jp_to_target /=. by rewrite csu_default_tgt.
  - change (cl_map tgt (p :: s)) with (I.List_cons LJp (tgt p) (cl_map tgt s)).
    rewrite (cfc_EQ (I.Prosa_Validation_ClassicUniSustainabilityInterface_xsu_find_param_cons Job dJ (csu_lab l) (tgt p) (cl_map tgt s))).
    have Hb : CtBoolRel (Sustainability.p_label p == l)
                (I.Decidable_decide (Lean.eq (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_job_parameter_p_label Job dJ (tgt p)) (csu_lab l))
                   (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_instDecidableEqParameter_label (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_job_parameter_p_label Job dJ (tgt p)) (csu_lab l))) :=
      csu_lab_eqb_rel _ _ (csu_jp_label Job p _ (@Lean.eq_refl _ _)) _ _ (@Lean.eq_refl _ _) _.
    rewrite (csu_ite_dec _ _ _ _ Hb) -IH /Sustainability.find_param /=.
    by case: (Sustainability.p_label p == l).
Qed.

Theorem Sustainability_default_val_correspondence l : CsuTolRel Job l (@Sustainability.default_val Job l) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_default_val Job dJ (csu_lab l)).
Proof. rewrite -csu_default_tgt. exact (csu_tol_canonical Job l _). Qed.

Theorem Sustainability_get_param_function_correspondence l pR pL (H : CsuJpRel Job pR pL) :
  CsuTolRel Job l (@Sustainability.get_param_function Job l pR) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_get_param_function Job dJ (csu_lab l) pL).
Proof.
  destruct H. destruct pR as [l' f].
  change (csu_jp_to_target Job (Sustainability.param l' f)) with (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_job_parameter_param Job dJ (csu_lab l') (csu_tol_to_target Job l' f)).
  destruct (Sustainability.parameter_label_eq_dec l' l) as [E|NE].
  - subst l'. rewrite csu_get_same (cfc_EQ (I.Prosa_Validation_ClassicUniSustainabilityInterface_xsu_get_param_same Job dJ (csu_lab l) _)).
    exact (csu_tol_canonical Job l f).
  - assert (NEL : I.Not (Lean.eq (csu_lab l') (csu_lab l))).
    { intro E. exact (ct_coq_false_to_target (NE (csu_lab_inj _ _ (imported_eq_to_coq_eq _ _ E)))). }
    rewrite (csu_get_other _ _ _ NE) (cfc_EQ (I.Prosa_Validation_ClassicUniSustainabilityInterface_xsu_get_param_other Job dJ (csu_lab l) (csu_lab l') _ NEL)).
    exact (Sustainability_default_val_correspondence l).
Qed.

Theorem Sustainability_return_param_correspondence l sR sL (Hs : JpsRel sR sL) :
  CsuTolRel Job l (@Sustainability.return_param Job l sR) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_return_param Job dJ (csu_lab l) sL).
Proof. exact (Sustainability_get_param_function_correspondence l _ _ (Sustainability_find_param_correspondence l sR sL Hs)). Qed.

(* ------------------------------------------------------------------ *)
(** * Labels of parameter lists *)

Theorem Sustainability_labels_of_correspondence sR sL (Hs : JpsRel sR sL) :
  ClListRel1 csu_lab (@Sustainability.labels_of Job sR) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_labels_of Job dJ sL).
Proof.
  rewrite -(cfc_EQ Hs). clear Hs. apply: coq_eq_to_imported_eq.
  elim: sR => [|p s IH]; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 LLab (csu_lab (Sustainability.p_label p)) (cl1_map csu_lab (@Sustainability.labels_of Job s)))
                   (I.List_cons_inst1 LLab (csu_lab (Sustainability.p_label p)) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_labels_of Job dJ (cl_map tgt s)))).
  by rewrite IH.
Qed.

Theorem Sustainability_has_unique_labels_correspondence sR sL (Hs : JpsRel sR sL) :
  CtBoolRel (@Sustainability.has_unique_labels Job sR) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_has_unique_labels Job dJ sL).
Proof. exact (ct_decide_bool _ _ _ (csu_labs_uniq _ _ (Sustainability_labels_of_correspondence sR sL Hs))). Qed.

End SusDefs.

(* ------------------------------------------------------------------ *)
(** * Relation search for the remaining definitions and the statements *)

Ltac csu_crel :=
  first
  [ assumption
  | csu_crel_x
  | lazymatch goal with
    | |- PropSPropRel (forall x : @Sustainability.job_parameter _, _) _ => apply: csu_forall_jp; intros ? ? ?; csu_crel
    | |- PropSPropRel (forall x : seq (@Sustainability.job_parameter _), _) _ => apply: csu_forall_jps; intros ? ? ?; csu_crel
    | |- PropSPropRel (forall x : Sustainability.parameter_label, _) _ =>
        apply: csu_forall_lab; let H := fresh "HL" in intros ? ? H; destruct H; csu_crel
    | |- PropSPropRel (forall x : _, _) (forall y : LLab, _) =>
        apply: csu_forall_lab; let H := fresh "HL" in intros ? ? H; destruct H; csu_crel
    | |- PropSPropRel (forall x : seq Sustainability.parameter_label, _) _ => apply: csu_forall_labs; intros ? ? ?; csu_crel
    | |- PropSPropRel (forall x : ArrivalSequence.arrival_sequence _, _) _ => apply: csu_forall_arr; intros ? ? ?; csu_crel
    | |- PropSPropRel (forall x : UniprocessorSchedule.schedule _, _) _ => apply: csu_forall_sched; intros ? ? ?; csu_crel
    | |- PropSPropRel (forall x : seq _ -> UniprocessorSchedule.schedule _ -> _ -> bool, _) _ =>
        apply: csu_forall_is; intros ? ? ?; csu_crel
    | |- PropSPropRel (forall x : seq _ -> ArrivalSequence.arrival_sequence _ -> UniprocessorSchedule.schedule _ -> Prop, _) _ =>
        apply: csu_forall_btm; intros ? ? ?; csu_crel
    | |- PropSPropRel (forall x : @Sustainability.type_of_label _ ?l -> @Sustainability.type_of_label _ ?l -> Prop, _) _ =>
        apply: csu_forall_hb; intros ? ? ?; csu_crel
    | |- PropSPropRel (forall x : @Sustainability.type_of_label _ ?l, _) _ => apply: csu_forall_tol; intros ? ? ?; csu_crel
    | |- PropSPropRel (forall x : Prop, _) _ => apply: csu_forall_prop; intros ? ? ?; csu_crel
    | |- PropSPropRel (forall x : ?T -> Prop, _) _ => apply: csu_forall_pred; intros ? ? ?; csu_crel
    | |- PropSPropRel (forall x : ?T, _) _ =>
        tryif (lazymatch type of T with Prop => idtac end) then (eapply ct_imp; [csu_crel | csu_crel])
        else (apply: ct_forall_identity; intro; csu_crel)
    | |- PropSPropRel (exists x : seq _, _) _ => apply: csu_exists_jps; intros ? ? ?; csu_crel
    | |- PropSPropRel (exists x : ArrivalSequence.arrival_sequence _, _) _ => apply: csu_exists_arr; intros ? ? ?; csu_crel
    | |- PropSPropRel (exists x : UniprocessorSchedule.schedule _, _) _ => apply: csu_exists_sched; intros ? ? ?; csu_crel
    | |- PropSPropRel (exists x, _) _ => apply: ct_exists_identity; intro; csu_crel
    | |- PropSPropRel (_ /\ _) _ => eapply ct_and; csu_crel
    | |- PropSPropRel (_ \/ _) _ => eapply ct_or; csu_crel
    | |- PropSPropRel (_ <-> _) _ => eapply csu_iff; csu_crel
    | |- PropSPropRel (~ _) _ => eapply csu_not_rel; csu_crel
    | |- PropSPropRel (List.In _ _) _ => eapply csu_in_rel; csu_crel
    | |- PropSPropRel (@Logic.eq (@Sustainability.job_parameter _) _ _) _ => eapply csu_jp_eq_rel; csu_crel
    | |- PropSPropRel (@Logic.eq Sustainability.parameter_label _ _) _ => eapply csu_lab_eq_rel; csu_crel
    | |- PropSPropRel (@Logic.eq (@Sustainability.type_of_label _ _) _ _) _ => eapply csu_tol_eq_rel; csu_crel
    | |- PropSPropRel (is_true (~~ (_ \in _))) _ => eapply csu_labs_notin; csu_crel
    | |- PropSPropRel (is_true (_ \in _)) _ => eapply csu_labs_mem; csu_crel
    | |- PropSPropRel (is_true _) _ => eapply ct_bool_truth; csu_crel
    | |- PropSPropRel (?h _ _ _) _ =>
        first [ match goal with H : CsuBtmRel _ h _ |- _ => eapply (csu_btm_app _ _ _ H); csu_crel end | csu_crel_p ]
    | |- PropSPropRel (?h _ _) _ =>
        first [ match goal with H : CsuHbRel _ _ h _ |- _ => eapply (csu_hb_app _ _ _ _ H); csu_crel end | csu_crel_p ]
    | |- PropSPropRel _ _ => csu_crel_p
    | |- CtBoolRel (~~ _) _ => eapply ct_bool_not; csu_crel
    | |- CtBoolRel (?i _ _ _) _ => match goal with H : CsuIsRel _ i _ |- _ => eapply H; csu_crel end
    | |- CtBoolRel (@Sustainability.has_unique_labels _ _) _ => eapply Sustainability_has_unique_labels_correspondence; csu_crel
    | |- CsuTolRel _ _ (@Sustainability.return_param _ _ _) _ => eapply Sustainability_return_param_correspondence; csu_crel
    | |- CsuLabRel (Sustainability.p_label _) _ => eapply csu_jp_label; csu_crel
    | |- CsuLabRel _ _ => exact (@Lean.eq_refl _ _)
    | |- ClListRel1 csu_lab (_ :: _) _ => eapply csu_labs_cons; csu_crel
    | |- ClListRel1 csu_lab [::] _ => exact csu_labs_nil
    | |- ClListRel1 csu_lab (@Sustainability.labels_of _ _) _ => eapply Sustainability_labels_of_correspondence; csu_crel
    | |- ClListRel (csu_jp_to_target _) _ _ => csu_crel_l
    | |- CsuJpRel _ _ _ => exact (@Lean.eq_refl _ _)
    | |- CsuSchedRel _ _ _ => assumption
    | |- CsuArrRel _ _ _ => assumption
    end ]
with csu_crel_p := fail
with csu_crel_l := fail
with csu_crel_x := fail.

Section SusMore.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LJp := (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_job_parameter Job dJ).
Notation JpsRel := (ClListRel (csu_jp_to_target Job)).

Lemma csu_param_rel l f g (H : CsuTolRel Job l f g) :
  CsuJpRel Job (Sustainability.param l f) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_job_parameter_param Job dJ (csu_lab l) g).
Proof. rewrite (csu_tol_fun_tgt Job l f g H). exact (@Lean.eq_refl _ _). Qed.

Lemma csu_jps_cons pR pL (H : CsuJpRel Job pR pL) sR sL (Hs : JpsRel sR sL) : JpsRel (pR :: sR) (I.List_cons LJp pL sL).
Proof. destruct H. rewrite -(cfc_EQ Hs). exact (@Lean.eq_refl _ _). Qed.

Lemma csu_jps_nil : JpsRel [::] (I.List_nil LJp).
Proof. exact (@Lean.eq_refl _ _). Qed.

End SusMore.

Ltac csu_crel_l ::= first [ eapply csu_jps_cons; csu_crel | exact (csu_jps_nil _) ].

Ltac csu_crel_x ::=
  lazymatch goal with
  | |- PropSPropRel (forall x : _ -> Time.time -> Time.duration, _) _ =>
      apply: (csu_forall_tol _ Sustainability.JOB_SUSPENSION); intros ? ? ?; csu_crel
  | |- PropSPropRel (forall x : _ -> Time.time, _) _ => apply: (csu_forall_tol _ Sustainability.JOB_COST); intros ? ? ?; csu_crel
  | |- PropSPropRel (@Logic.eq _ (@Sustainability.return_param _ ?l _) _) _ => eapply (csu_tol_eq_rel _ l); csu_crel
  | |- PropSPropRel (?p ?x) _ => match goal with H : forall y, PropSPropRel (p y) _ |- _ => exact (H x) end
  | |- CsuJpRel _ (Sustainability.param _ _) _ => eapply csu_param_rel; csu_crel
  end.

(* ------------------------------------------------------------------ *)
(** * Definitions (Prop-valued) *)

Section SusProps.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation JpsRel := (ClListRel (csu_jp_to_target Job)).

Theorem Sustainability_differ_only_by_correspondence vR vL (Hv : ClListRel1 csu_lab vR vL) s1R s1L (H1 : JpsRel s1R s1L)
    s2R s2L (H2 : JpsRel s2R s2L) :
  PropSPropRel (@Sustainability.differ_only_by Job vR s1R s2R) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_differ_only_by Job dJ vL s1L s2L).
Proof. rewrite /Sustainability.differ_only_by. unfold I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_differ_only_by. csu_crel. Qed.
Ltac csu_crel_p ::= first [ eapply Sustainability_differ_only_by_correspondence; csu_crel ].

Theorem Sustainability_corresponding_labels_correspondence sR sL (Hs : JpsRel sR sL) lR lL (Hl : ClListRel1 csu_lab lR lL) :
  PropSPropRel (@Sustainability.corresponding_labels Job sR lR) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_corresponding_labels Job dJ sL lL).
Proof. rewrite /Sustainability.corresponding_labels. unfold I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_corresponding_labels. csu_crel. Qed.
Ltac csu_crel_p ::= first [ eapply Sustainability_differ_only_by_correspondence; csu_crel | eapply Sustainability_corresponding_labels_correspondence; csu_crel ].

Theorem Sustainability_sustainable_param_becomes_better_correspondence sp hR hL (Hh : CsuHbRel Job sp hR hL)
    pR pL (Hp : JpsRel pR pL) qR qL (Hq : JpsRel qR qL) :
  PropSPropRel (@Sustainability.sustainable_param_becomes_better Job sp hR pR qR)
    (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_sustainable_param_becomes_better Job dJ (csu_lab sp) hL pL qL).
Proof. rewrite /Sustainability.sustainable_param_becomes_better. unfold I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_sustainable_param_becomes_better. cbv zeta. csu_crel. Qed.
Ltac csu_crel_p ::= first [ eapply Sustainability_differ_only_by_correspondence; csu_crel | eapply Sustainability_corresponding_labels_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_better_correspondence; csu_crel ].

Theorem Sustainability_sustainable_param_becomes_worse_correspondence sp hR hL (Hh : CsuHbRel Job sp hR hL)
    pR pL (Hp : JpsRel pR pL) qR qL (Hq : JpsRel qR qL) :
  PropSPropRel (@Sustainability.sustainable_param_becomes_worse Job sp hR pR qR)
    (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_sustainable_param_becomes_worse Job dJ (csu_lab sp) hL pL qL).
Proof. rewrite /Sustainability.sustainable_param_becomes_worse. unfold I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_sustainable_param_becomes_worse. cbv zeta. csu_crel. Qed.
Ltac csu_crel_p ::= first [ eapply Sustainability_differ_only_by_correspondence; csu_crel | eapply Sustainability_corresponding_labels_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_better_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_worse_correspondence; csu_crel ].

Theorem Sustainability_sustainable_and_varying_params_in_correspondence sp vR vL (Hv : ClListRel1 csu_lab vR vL) pR pL (Hp : JpsRel pR pL) :
  PropSPropRel (@Sustainability.sustainable_and_varying_params_in Job sp vR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_sustainable_and_varying_params_in Job dJ (csu_lab sp) vL pL).
Proof. rewrite /Sustainability.sustainable_and_varying_params_in. unfold I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_sustainable_and_varying_params_in. csu_crel. Qed.
Ltac csu_crel_p ::= first [ eapply Sustainability_differ_only_by_correspondence; csu_crel | eapply Sustainability_corresponding_labels_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_better_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_worse_correspondence; csu_crel | eapply Sustainability_sustainable_and_varying_params_in_correspondence; csu_crel ].

Theorem Sustainability_has_consistent_labels_correspondence aR aL (Ha : ClListRel1 csu_lab aR aL) sp vR vL (Hv : ClListRel1 csu_lab vR vL)
    pR pL (Hp : JpsRel pR pL) :
  PropSPropRel (@Sustainability.has_consistent_labels Job aR sp vR pR) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_has_consistent_labels Job dJ aL (csu_lab sp) vL pL).
Proof. rewrite /Sustainability.has_consistent_labels. unfold I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_has_consistent_labels. csu_crel. Qed.
Ltac csu_crel_p ::= first [ eapply Sustainability_differ_only_by_correspondence; csu_crel | eapply Sustainability_corresponding_labels_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_better_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_worse_correspondence; csu_crel | eapply Sustainability_sustainable_and_varying_params_in_correspondence; csu_crel | eapply Sustainability_has_consistent_labels_correspondence; csu_crel ].

Theorem Sustainability_jobs_are_schedulable_with_correspondence iR iL (Hi : CsuIsRel Job iR iL) bR bL (Hb : CsuBtmRel Job bR bL)
    pR pL (Hp : JpsRel pR pL) :
  PropSPropRel (@Sustainability.jobs_are_schedulable_with Job iR bR pR) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_jobs_are_schedulable_with Job dJ iL bL pL).
Proof. rewrite /Sustainability.jobs_are_schedulable_with. unfold I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_jobs_are_schedulable_with. csu_crel. Qed.
Ltac csu_crel_p ::= first [ eapply Sustainability_differ_only_by_correspondence; csu_crel | eapply Sustainability_corresponding_labels_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_better_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_worse_correspondence; csu_crel | eapply Sustainability_sustainable_and_varying_params_in_correspondence; csu_crel | eapply Sustainability_has_consistent_labels_correspondence; csu_crel | eapply Sustainability_jobs_are_schedulable_with_correspondence; csu_crel ].

Theorem Sustainability_jobs_are_not_schedulable_with_correspondence iR iL (Hi : CsuIsRel Job iR iL) bR bL (Hb : CsuBtmRel Job bR bL)
    pR pL (Hp : JpsRel pR pL) :
  PropSPropRel (@Sustainability.jobs_are_not_schedulable_with Job iR bR pR) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_jobs_are_not_schedulable_with Job dJ iL bL pL).
Proof. rewrite /Sustainability.jobs_are_not_schedulable_with. unfold I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_jobs_are_not_schedulable_with. csu_crel. Qed.
Ltac csu_crel_p ::= first [ eapply Sustainability_differ_only_by_correspondence; csu_crel | eapply Sustainability_corresponding_labels_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_better_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_worse_correspondence; csu_crel | eapply Sustainability_sustainable_and_varying_params_in_correspondence; csu_crel | eapply Sustainability_has_consistent_labels_correspondence; csu_crel | eapply Sustainability_jobs_are_schedulable_with_correspondence; csu_crel | eapply Sustainability_jobs_are_not_schedulable_with_correspondence; csu_crel ].

Theorem Sustainability_jobs_are_V_schedulable_with_correspondence aR aL (Ha : ClListRel1 csu_lab aR aL) iR iL (Hi : CsuIsRel Job iR iL)
    bR bL (Hb : CsuBtmRel Job bR bL) sp vR vL (Hv : ClListRel1 csu_lab vR vL) pR pL (Hp : JpsRel pR pL) :
  PropSPropRel (@Sustainability.jobs_are_V_schedulable_with Job aR iR bR sp vR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_jobs_are_V_schedulable_with Job dJ aL iL bL (csu_lab sp) vL pL).
Proof. rewrite /Sustainability.jobs_are_V_schedulable_with. unfold I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_jobs_are_V_schedulable_with. csu_crel. Qed.
Ltac csu_crel_p ::= first [ eapply Sustainability_differ_only_by_correspondence; csu_crel | eapply Sustainability_corresponding_labels_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_better_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_worse_correspondence; csu_crel | eapply Sustainability_sustainable_and_varying_params_in_correspondence; csu_crel | eapply Sustainability_has_consistent_labels_correspondence; csu_crel | eapply Sustainability_jobs_are_schedulable_with_correspondence; csu_crel | eapply Sustainability_jobs_are_not_schedulable_with_correspondence; csu_crel | eapply Sustainability_jobs_are_V_schedulable_with_correspondence; csu_crel ].

Theorem Sustainability_weakly_sustainable_correspondence aR aL (Ha : ClListRel1 csu_lab aR aL) iR iL (Hi : CsuIsRel Job iR iL)
    bR bL (Hb : CsuBtmRel Job bR bL) sp hR hL (Hh : CsuHbRel Job sp hR hL) vR vL (Hv : ClListRel1 csu_lab vR vL) :
  PropSPropRel (@Sustainability.weakly_sustainable Job aR iR bR sp hR vR) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_weakly_sustainable Job dJ aL iL bL (csu_lab sp) hL vL).
Proof. rewrite /Sustainability.weakly_sustainable. unfold I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_weakly_sustainable. csu_crel. Qed.
Ltac csu_crel_p ::= first [ eapply Sustainability_differ_only_by_correspondence; csu_crel | eapply Sustainability_corresponding_labels_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_better_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_worse_correspondence; csu_crel | eapply Sustainability_sustainable_and_varying_params_in_correspondence; csu_crel | eapply Sustainability_has_consistent_labels_correspondence; csu_crel | eapply Sustainability_jobs_are_schedulable_with_correspondence; csu_crel | eapply Sustainability_jobs_are_not_schedulable_with_correspondence; csu_crel | eapply Sustainability_jobs_are_V_schedulable_with_correspondence; csu_crel | eapply Sustainability_weakly_sustainable_correspondence; csu_crel ].

Theorem Sustainability_weakly_sustainable_contrapositive_correspondence aR aL (Ha : ClListRel1 csu_lab aR aL) iR iL (Hi : CsuIsRel Job iR iL)
    bR bL (Hb : CsuBtmRel Job bR bL) sp hR hL (Hh : CsuHbRel Job sp hR hL) vR vL (Hv : ClListRel1 csu_lab vR vL) :
  PropSPropRel (@Sustainability.weakly_sustainable_contrapositive Job aR iR bR sp hR vR)
    (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_weakly_sustainable_contrapositive Job dJ aL iL bL (csu_lab sp) hL vL).
Proof. rewrite /Sustainability.weakly_sustainable_contrapositive. unfold I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_weakly_sustainable_contrapositive. csu_crel. Qed.
Ltac csu_crel_p ::= first [ eapply Sustainability_differ_only_by_correspondence; csu_crel | eapply Sustainability_corresponding_labels_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_better_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_worse_correspondence; csu_crel | eapply Sustainability_sustainable_and_varying_params_in_correspondence; csu_crel | eapply Sustainability_has_consistent_labels_correspondence; csu_crel | eapply Sustainability_jobs_are_schedulable_with_correspondence; csu_crel | eapply Sustainability_jobs_are_not_schedulable_with_correspondence; csu_crel | eapply Sustainability_jobs_are_V_schedulable_with_correspondence; csu_crel | eapply Sustainability_weakly_sustainable_correspondence; csu_crel | eapply Sustainability_weakly_sustainable_contrapositive_correspondence; csu_crel ].

Theorem Sustainability_strongly_sustainable_correspondence aR aL (Ha : ClListRel1 csu_lab aR aL) iR iL (Hi : CsuIsRel Job iR iL)
    bR bL (Hb : CsuBtmRel Job bR bL) sp hR hL (Hh : CsuHbRel Job sp hR hL) :
  PropSPropRel (@Sustainability.strongly_sustainable Job aR iR bR sp hR) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_strongly_sustainable Job dJ aL iL bL (csu_lab sp) hL).
Proof. rewrite /Sustainability.strongly_sustainable. unfold I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_strongly_sustainable. csu_crel. Qed.
Ltac csu_crel_p ::= first [ eapply Sustainability_differ_only_by_correspondence; csu_crel | eapply Sustainability_corresponding_labels_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_better_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_worse_correspondence; csu_crel | eapply Sustainability_sustainable_and_varying_params_in_correspondence; csu_crel | eapply Sustainability_has_consistent_labels_correspondence; csu_crel | eapply Sustainability_jobs_are_schedulable_with_correspondence; csu_crel | eapply Sustainability_jobs_are_not_schedulable_with_correspondence; csu_crel | eapply Sustainability_jobs_are_V_schedulable_with_correspondence; csu_crel | eapply Sustainability_weakly_sustainable_correspondence; csu_crel | eapply Sustainability_weakly_sustainable_contrapositive_correspondence; csu_crel | eapply Sustainability_strongly_sustainable_correspondence; csu_crel ].

End SusProps.

(* Ltac redefinitions are local to the section: re-install the final one for the statements below. *)
Ltac csu_crel_p ::= first [ eapply Sustainability_differ_only_by_correspondence; csu_crel | eapply Sustainability_corresponding_labels_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_better_correspondence; csu_crel | eapply Sustainability_sustainable_param_becomes_worse_correspondence; csu_crel | eapply Sustainability_sustainable_and_varying_params_in_correspondence; csu_crel | eapply Sustainability_has_consistent_labels_correspondence; csu_crel | eapply Sustainability_jobs_are_schedulable_with_correspondence; csu_crel | eapply Sustainability_jobs_are_not_schedulable_with_correspondence; csu_crel | eapply Sustainability_jobs_are_V_schedulable_with_correspondence; csu_crel | eapply Sustainability_weakly_sustainable_correspondence; csu_crel | eapply Sustainability_weakly_sustainable_contrapositive_correspondence; csu_crel | eapply Sustainability_strongly_sustainable_correspondence; csu_crel ].

(* ------------------------------------------------------------------ *)
(** * Types: labels, parameter functions, job parameters *)

Theorem Sustainability_parameter_label_correspondence :
  (forall l, Logic.eq (csu_unlab (csu_lab l)) l) /\ (forall l, Logic.eq (csu_lab (csu_unlab l)) l).
Proof. exact (conj csu_unlab_lab csu_lab_unlab). Qed.

Theorem Sustainability_type_of_label_correspondence (Job : eqType) l :
  And (forall f, CsuTolRel Job l f (csu_tol_to_target Job l f)) (forall g, CsuTolRel Job l (csu_tol_to_source Job l g) g).
Proof. exact (And_intro _ _ (csu_tol_canonical Job l) (csu_tol_surjective Job l)). Qed.

Theorem Sustainability_job_parameter_correspondence (Job : eqType) :
  (forall p, Logic.eq (csu_jp_to_source Job (csu_jp_to_target Job p)) p) /\
  (forall q, Logic.eq (csu_jp_to_target Job (csu_jp_to_source Job q)) q).
Proof. exact (conj (csu_jp_src_tgt Job) (csu_jp_tgt_src Job)). Qed.

(** [eqlabelP] (Rocq: [Equality.axiom parameter_label_beq]; Lean: the [BoolReflect] value of the same Boolean test):
    the Boolean label tests agree on related labels. *)
Theorem Sustainability_eqlabelP_correspondence :
  forall x y, CtBoolRel (Sustainability.parameter_label_beq x y) (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_parameter_label_beq (csu_lab x) (csu_lab y)).
Proof. intros x y; destruct x, y; exact (@Lean.eq_refl _ _). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_return_param_works1 (Job : eqType) : Prop :=
  ltac:(type_of_term (@Sustainability.return_param_works1 Job)).
Definition tgt_return_param_works1 (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_return_param_works1 Job (ct_decidable_eq Job))).
Theorem Sustainability_return_param_works1_correspondence (Job : eqType) :
  PropSPropRel (src_return_param_works1 Job) (tgt_return_param_works1 Job).
Proof. unfold src_return_param_works1, tgt_return_param_works1. csu_crel. Qed.

Definition src_return_param_works2 (Job : eqType) : Prop :=
  ltac:(type_of_term (@Sustainability.return_param_works2 Job)).
Definition tgt_return_param_works2 (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_return_param_works2 Job (ct_decidable_eq Job))).
Theorem Sustainability_return_param_works2_correspondence (Job : eqType) :
  PropSPropRel (src_return_param_works2 Job) (tgt_return_param_works2 Job).
Proof. unfold src_return_param_works2, tgt_return_param_works2. csu_crel. Qed.

Definition src_found_param_label (Job : eqType) : Prop :=
  ltac:(type_of_term (@Sustainability.found_param_label Job)).
Definition tgt_found_param_label (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_found_param_label Job (ct_decidable_eq Job))).
Theorem Sustainability_found_param_label_correspondence (Job : eqType) :
  PropSPropRel (src_found_param_label Job) (tgt_found_param_label Job).
Proof. unfold src_found_param_label, tgt_found_param_label. csu_crel. Qed.

Definition src_weak_sustainability_equivalence (Job : eqType) : Prop :=
  ltac:(type_of_term (@Sustainability.weak_sustainability_equivalence Job)).
Definition tgt_weak_sustainability_equivalence (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Sustainability_Sustainability_weak_sustainability_equivalence Job (ct_decidable_eq Job))).
Theorem Sustainability_weak_sustainability_equivalence_correspondence (Job : eqType) :
  PropSPropRel (src_weak_sustainability_equivalence Job) (tgt_weak_sustainability_equivalence Job).
Proof. unfold src_weak_sustainability_equivalence, tgt_weak_sustainability_equivalence. csu_crel. Qed.
