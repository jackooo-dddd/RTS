From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div.
From prosa Require Import util.seqset classic.model.time classic.util.list classic.util.div_mod classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.policy_tdma classic.model.schedule.uni.schedule classic.model.schedule.uni.response_time classic.model.schedule.uni.basic.platform_tdma classic.model.schedule.uni.end_time classic.analysis.uni.basic.tdma_wcrt_analysis classic.implementation.uni.basic.extraction_tdma.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicExtractionTdma.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicExtractionTdmaBase ClassicExtractionTdmaList ClassicExtractionTdmaList1.



Module I := ImportedClassicExtractionTdma.
Local Open Scope nat_scope.

(** Certificates for [classic/implementation/uni/basic/extraction_tdma.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: times and task parameters by [SubNatRel].  The Rocq [CoInductive Task_T] (one non-recursive
    constructor, translated as a Lean [inductive] with the same constructor) is related constructor-wise with
    field-wise [SubNatRel] (an injective embedding with a left inverse, total in both directions); task lists
    elementwise ([ClListRel]); the fixpoints [In], [schedulability_test], [cycle] by induction on the list against
    the kernel-checked Lean equations exported with the artifact (fixture [xt_*]); the WCRT formula through the
    accepted rank-92 certificate (re-bound library). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cxt_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cxt_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cxt_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cxt_false_rel). Qed.

Lemma cxt_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cxt_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cxt_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cxt_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cxt_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cxt_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cxt_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cxt_unmap_rel T l) PR PL).
Qed.

Definition CxtParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cxt_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CxtParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cxt_forall_cover _ _ (CxtParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cxt_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cxt_natl s') end.

Definition cxt_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cxt_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cxt_one) (cxt_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cxt_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cxt_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cxt_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cxt_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cxt_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cxt_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cxt_cl_append. reflexivity.
Qed.

Lemma cxt_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CxtFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CxtArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cxt_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cxt_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cxt_arr_canonical aR : CxtArrRel aR (cxt_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cxt_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cxt_arr_surjective aL : CxtArrRel (cxt_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cxt_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CxtArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cxt_forall_cover _ _ CxtArrRel cxt_arr_to_target cxt_arr_to_source cxt_arr_canonical cxt_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cxt_arrives_in aR aL (Ha : CxtArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cxt_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cxt_has_arrived pR pL (Hp : CxtParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cxt_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cxt_snatl s') end.

Lemma cxt_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cxt_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cxt_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cxt_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cxt_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cxt_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cxt_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CxtFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cxt_fun_canonical FR FL (HF : CxtFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cxt_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cxt_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CxtFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cxt_nat_sub_canonical nR mR.
  rewrite cxt_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cxt_foldr_add FL FR (cxt_fun_canonical FR FL HF)).
  by rewrite cxt_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cxt_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cxt_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cxt_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cxt_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cxt_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CxtSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cxt_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cxt_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cxt_sched_canonical sR : CxtSchedRel sR (cxt_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cxt_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cxt_sched_surjective sL : CxtSchedRel (cxt_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cxt_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cxt_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CxtSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cxt_forall_cover _ _ CxtSchedRel cxt_sched_to_target cxt_sched_to_source cxt_sched_canonical cxt_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cxt_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CxtSchedRel Job sR (cxt_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CxtSchedRel Job (cxt_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cxt_sched_canonical Job) (cxt_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CxtSchedRel Job sR sL.

Lemma cxt_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cxt_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cxt_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cxt_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cxt_US_scheduled_at j tR tL Ht)). Qed.

Lemma cxt_service_at_fun j : CxtFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cxt_US_service_at j kR kL Hk). Qed.

Lemma cxt_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cxt_ico _ _ _ _ _ _ H1 H2 (cxt_service_at_fun j)). Qed.

Lemma cxt_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cxt_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cxt_US_completed_by cR cL (Hc : CxtParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cxt_US_service j tR tL Ht)). Qed.

Lemma cxt_US_pending aR aL (Ha : CxtParRel Job aR aL) cR cL (Hc : CxtParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cxt_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cxt_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cxt_US_backlogged aR aL (Ha : CxtParRel Job aR aL) cR cL (Hc : CxtParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.backlogged aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_backlogged Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cxt_US_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (cxt_US_scheduled_at j tR tL Ht))).
Qed.

Lemma cxt_US_jobs_must_arrive_to_execute aR aL (Ha : CxtParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cxt_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cxt_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma cxt_US_completed_jobs_dont_execute cR cL (Hc : CxtParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cxt_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

End JobDefs.

(* ------------------------------------------------------------------ *)
(** * Nat subtraction / Euclidean division bridge (re-bound copy of the accepted NatSubCorrespondence and
    DivModCorrespondence, through the exported [DivModInterface] equations) *)

(** Adapter for the operations that occur in the actual freshly imported
    [Prosa.Util.Nat] theorem types. *)
Definition nat_target_add (a b : Lean.Nat) : Lean.Nat :=
  I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHAdd_inst1 Lean.Nat I.instAddNat) a b.

Definition nat_target_sub (a b : Lean.Nat) : Lean.Nat :=
  I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHSub_inst1 Lean.Nat I.instSubNat) a b.

Definition nat_target_le (a b : Lean.Nat) : SProp :=
  I.LE_le_inst1 Lean.Nat I.instLENat a b.

Lemma nat_target_add_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (nat_target_add aL bL).
Proof.
  intros Ha Hb. exact (sub_add_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma nat_target_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (nat_target_le aL bL).
Proof.
  intros Ha Hb. exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

(** The actual compiled Lean subtraction is a course-of-values recursion on
    the amount being subtracted.  Its two computation equations are
    definitionally true in the imported artifact. *)
Lemma nat_target_sub_zero (a : Lean.Nat) :
  Lean.eq (nat_target_sub a Lean.Nat_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma nat_target_sub_succ (a b : Lean.Nat) :
  Lean.eq (nat_target_sub a (Lean.Nat_succ b))
    (I.Nat_pred (nat_target_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (I.Nat_pred (nat_target_sub a b))).
Qed.

Fixpoint rocq_iterated_pred (a b : nat) : nat :=
  match b with
  | O => a
  | S b' => Nat.pred (rocq_iterated_pred a b')
  end.

Lemma rocq_iterated_pred_is_subn (a b : nat) :
  Logic.eq (rocq_iterated_pred a b) (a - b).
Proof.
  revert a. induction b as [|b IH]; intro a; cbn [rocq_iterated_pred].
  - rewrite subn0. reflexivity.
  - rewrite (IH a). exact (Logic.eq_sym (subnS a b)).
Qed.

Definition nat_target_pred_canonical (n : nat) :
  Lean.eq (I.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (I.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma nat_target_sub_iterated_pred (a b : nat) :
  Lean.eq
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (rocq_iterated_pred a b)).
Proof.
  induction b as [|b IH].
  - exact (nat_target_sub_zero (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _
      (nat_target_sub_succ _ _)
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr I.Nat_pred _ _ IH)
        (nat_target_pred_canonical (rocq_iterated_pred a b)))).
Qed.

(** Direct computation proof for truncated subtraction.  This covers both
    branches: a positive residual and truncation to zero. *)
Lemma nat_target_sub_canonical (a b : nat) :
  Lean.eq
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  exact (sub_imported_eq_trans _ _ _
    (nat_target_sub_iterated_pred a b)
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported (rocq_iterated_pred_is_subn a b)))).
Qed.

Lemma nat_target_sub_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (nat_target_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (nat_target_sub_canonical aR bR))
    (sub_imported_eq_congr2 nat_target_sub _ _ _ _ Ha Hb)).
Qed.

(** Explicit branch witnesses requested by the translation policy. *)
Lemma nat_target_sub_nontruncated a b :
  is_true (leq b a) ->
  SubNatRel (a - b)
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof. intros _. apply nat_target_sub_correspondence; apply sub_nat_rel_canonical. Qed.

Lemma rocq_sub_truncates a b :
  is_true (ltn a b) -> Logic.eq (a - b) O.
Proof.
  move: a. elim: b => [|b IH] [|a] //= H. exact: IH.
Qed.

Lemma nat_target_sub_truncated a b :
  is_true (ltn a b) ->
  SubNatRel O
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  intro Hlt. have Hz : Logic.eq (a - b) O := rocq_sub_truncates a b Hlt.
  rewrite <- Hz. apply nat_target_sub_correspondence; apply sub_nat_rel_canonical.
Qed.

(** Operation-level bridge for the exact [Nat.div]/[Nat.mod] interface
    exported from the compiled [Prosa.Util.Div_mod] artifact.  The proof uses
    the two Euclidean characterizations on each side; it does not unfold the
    implementation-specific Lean [Nat.brecOn]/[Nat.below] recursion. *)

Definition dm_imported_add (a b : Lean.Nat) : Lean.Nat :=
  I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHAdd_inst1 Lean.Nat I.instAddNat) a b.

Definition dm_imported_mul (a b : Lean.Nat) : Lean.Nat :=
  I.HMul_hMul_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHMul_inst1 Lean.Nat I.instMulNat) a b.

Definition dm_imported_div (a b : Lean.Nat) : Lean.Nat :=
  I.HDiv_hDiv_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHDiv_inst1 Lean.Nat I.Nat_instDiv) a b.

Definition dm_imported_sub (a b : Lean.Nat) : Lean.Nat :=
  I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHSub_inst1 Lean.Nat I.instSubNat) a b.

Definition dm_imported_mod (a b : Lean.Nat) : Lean.Nat :=
  I.HMod_hMod_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHMod_inst1 Lean.Nat I.Nat_instMod) a b.

Definition dm_imported_lt (a b : Lean.Nat) : SProp :=
  I.LT_lt_inst1 Lean.Nat I.instLTNat a b.

Definition dm_imported_le (a b : Lean.Nat) : SProp :=
  I.LE_le_inst1 Lean.Nat I.instLENat a b.

Definition dm_imported_dvd (a b : Lean.Nat) : SProp :=
  I.Dvd_dvd_inst1 Lean.Nat I.Nat_instDvd a b.

Definition dm_imported_zero : Lean.Nat :=
  I.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (I.instOfNatNat Lean.Nat_zero).

Definition dm_imported_one : Lean.Nat :=
  I.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ Lean.Nat_zero)
    (I.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition dm_imported_div_floor (a b : Lean.Nat) : Lean.Nat :=
  I.Prosa_Classic_Util_DivMod_div_floor a b.

Definition dm_imported_div_ceil (a b : Lean.Nat) : Lean.Nat :=
  I.Prosa_Classic_Util_DivMod_div_ceil a b.

Definition dm_coq_false_to_target (H : Logic.False) :
    I.False :=
  match H return I.False with end.

Lemma dm_add_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (dm_imported_add aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (aR + bR) (sub_imported_add aL bL)).
  exact (sub_add_correspondence aR aL bR bL).
Qed.

Lemma dm_mul_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR * bR) (dm_imported_mul aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (aR * bR) (sub_imported_mul aL bL)).
  exact (sub_mul_correspondence aR aL bR bL).
Qed.

Lemma dm_sub_zero (a : Lean.Nat) :
  Lean.eq (dm_imported_sub a Lean.Nat_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma dm_sub_succ (a b : Lean.Nat) :
  Lean.eq (dm_imported_sub a (Lean.Nat_succ b))
    (I.Nat_pred (dm_imported_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (I.Nat_pred (dm_imported_sub a b))).
Qed.

Definition dm_pred_canonical (n : nat) :
  Lean.eq (I.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (I.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma dm_sub_iterated_pred (a b : nat) :
  Lean.eq
    (dm_imported_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (rocq_iterated_pred a b)).
Proof.
  revert a. induction b as [|b IH]; intro a.
  - exact (dm_sub_zero (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _
      (dm_sub_succ _ _)
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr I.Nat_pred _ _ (IH a))
        (dm_pred_canonical (rocq_iterated_pred a b)))).
Qed.

Lemma dm_sub_canonical (a b : nat) :
  Lean.eq
    (dm_imported_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  exact (sub_imported_eq_trans _ _ _
    (dm_sub_iterated_pred a b)
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported (rocq_iterated_pred_is_subn a b)))).
Qed.

Lemma dm_sub_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (dm_imported_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (dm_sub_canonical aR bR))
    (sub_imported_eq_congr2 dm_imported_sub _ _ _ _ Ha Hb)).
Qed.

Lemma dm_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (dm_imported_le aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    PropSPropRel (is_true (leq aR bR)) (sub_imported_le aL bL)).
  exact (sub_nat_le_correspondence aR aL bR bL).
Qed.

Lemma dm_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (dm_imported_lt aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    PropSPropRel (is_true (ltn aR bR)) (sub_imported_lt aL bL)).
  exact (sub_nat_lt_correspondence aR aL bR bL).
Qed.

Lemma dm_eq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof. exact (sub_nat_eq_correspondence aR aL bR bL). Qed.

Lemma dm_succ_correspondence nR nL :
  SubNatRel nR nL ->
  SubNatRel nR.+1 (dm_imported_add nL dm_imported_one).
Proof.
  intro Hn. have H := dm_add_correspondence nR nL 1 dm_imported_one
    Hn (sub_nat_rel_canonical 1).
  rewrite addn1 in H. exact H.
Qed.

Lemma dm_div_mod_decoded_canonical (x y : nat) :
  Logic.eq
    (sub_nat_to_rocq
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y)))
    (x %/ y) /\
  Logic.eq
    (sub_nat_to_rocq
      (dm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y)))
    (x %% y).
Proof.
  case Hy: y => [|y'].
  - subst y. split.
    + rewrite divn0.
      have H :=
        I.Prosa_Validation_DivModInterface_production_div_zero
          (sub_nat_to_imported x).
      exact (f_equal sub_nat_to_rocq
        (imported_eq_to_coq_eq _ _ H)).
    + rewrite modn0.
      have H :=
        I.Prosa_Validation_DivModInterface_production_mod_zero
          (sub_nat_to_imported x).
      transitivity
        (sub_nat_to_rocq (sub_nat_to_imported x)).
      * exact (f_equal sub_nat_to_rocq
          (imported_eq_to_coq_eq _ _ H)).
      * exact (sub_nat_rocq_roundtrip x).
  - have Hypos : is_true (ltn O y'.+1) by done.
    set xL := sub_nat_to_imported x.
    set yL := sub_nat_to_imported y'.+1.
    set qL := dm_imported_div xL yL.
    set rL := dm_imported_mod xL yL.
    have HrLtR : is_true (ltn (sub_nat_to_rocq rL) y'.+1).
    { exact (sprop_to_prop _ _
        (dm_lt_correspondence (sub_nat_to_rocq rL) rL y'.+1 yL
          (sub_nat_rel_surjective rL) (sub_nat_rel_canonical y'.+1))
        (I.Prosa_Validation_DivModInterface_production_mod_lt
          xL yL
          (prop_to_sprop _ _
            (dm_lt_correspondence O dm_imported_zero y'.+1 yL
              (sub_nat_rel_canonical O) (sub_nat_rel_canonical y'.+1))
            Hypos))). }
    have HdecompR : Logic.eq
        (y'.+1 * sub_nat_to_rocq qL + sub_nat_to_rocq rL) x.
    { exact (sprop_to_prop _ _
        (dm_eq_correspondence
          (y'.+1 * sub_nat_to_rocq qL + sub_nat_to_rocq rL)
          (dm_imported_add (dm_imported_mul yL qL) rL)
          x xL
          (dm_add_correspondence _ _ _ _
            (dm_mul_correspondence y'.+1 yL
              (sub_nat_to_rocq qL) qL
              (sub_nat_rel_canonical y'.+1)
              (sub_nat_rel_surjective qL))
            (sub_nat_rel_surjective rL))
          (sub_nat_rel_canonical x))
        (I.Prosa_Validation_DivModInterface_production_div_add_mod
          xL yL)). }
    have Hx : Logic.eq x
        (sub_nat_to_rocq qL * y'.+1 + sub_nat_to_rocq rL).
    { rewrite mulnC. exact (Logic.eq_sym HdecompR). }
    have Hedge : Logic.eq (edivn x y'.+1)
        (sub_nat_to_rocq qL, sub_nat_to_rocq rL).
    { rewrite Hx. exact (@edivn_eq y'.+1 (sub_nat_to_rocq qL)
        (sub_nat_to_rocq rL) HrLtR). }
    have Hq := f_equal (@Datatypes.fst nat nat) Hedge.
    change (Logic.eq (divn x (S y')) (sub_nat_to_rocq qL)) in Hq.
    have Hr := f_equal (@Datatypes.snd nat nat) Hedge.
    change (Logic.eq (Datatypes.snd (edivn x (S y')))
      (sub_nat_to_rocq rL)) in Hr.
    rewrite <- (modn_def x y'.+1) in Hr.
    split; exact (Logic.eq_sym Hq) || exact (Logic.eq_sym Hr).
Qed.

Lemma dm_div_canonical (x y : nat) :
  Lean.eq
    (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported (x %/ y)).
Proof.
  have Hdecoded := proj1 (dm_div_mod_decoded_canonical x y).
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_nat_imported_roundtrip
        (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))))
    (coq_eq_to_imported_eq _ _ (f_equal sub_nat_to_imported Hdecoded))).
Qed.

Lemma dm_mod_canonical (x y : nat) :
  Lean.eq
    (dm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported (x %% y)).
Proof.
  have Hdecoded := proj2 (dm_div_mod_decoded_canonical x y).
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_nat_imported_roundtrip
        (dm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y))))
    (coq_eq_to_imported_eq _ _ (f_equal sub_nat_to_imported Hdecoded))).
Qed.

Lemma dm_div_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %/ yR) (dm_imported_div xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (dm_div_canonical xR yR))
    (sub_imported_eq_congr2 dm_imported_div _ _ _ _ Hx Hy)).
Qed.

Lemma dm_mod_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %% yR) (dm_imported_mod xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (dm_mod_canonical xR yR))
    (sub_imported_eq_congr2 dm_imported_mod _ _ _ _ Hx Hy)).
Qed.

Lemma dm_dvd_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  PropSPropRel (is_true (yR %| xR)) (dm_imported_dvd yL xL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro HdvdR.
    apply (I.Iff_mpr _ _
      (I.Prosa_Validation_DivModInterface_production_dvd_iff_mod_eq_zero
        xL yL)).
    apply (prop_to_sprop _ _
      (dm_eq_correspondence (xR %% yR) (dm_imported_mod xL yL)
        O dm_imported_zero
        (dm_mod_correspondence xR xL yR yL Hx Hy)
        (sub_nat_rel_canonical O))).
    move: HdvdR. rewrite /dvdn. by move/eqP.
  - intro HdvdL. apply strictly_inhabits.
    rewrite /dvdn. apply/eqP.
    apply (sprop_to_prop _ _
      (dm_eq_correspondence (xR %% yR) (dm_imported_mod xL yL)
        O dm_imported_zero
        (dm_mod_correspondence xR xL yR yL Hx Hy)
        (sub_nat_rel_canonical O))).
    exact (I.Iff_mp _ _
      (I.Prosa_Validation_DivModInterface_production_dvd_iff_mod_eq_zero
        xL yL) HdvdL).
Qed.

Lemma dm_div_floor_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %/ yR) (dm_imported_div_floor xL yL).
Proof.
  intros Hx Hy.
  change (SubNatRel (xR %/ yR) (dm_imported_div xL yL)).
  exact (dm_div_correspondence xR xL yR yL Hx Hy).
Qed.

Lemma dm_bool_false_no_truth (b : bool) :
  Logic.eq b false -> is_true b -> Logic.False.
Proof. destruct b; cbn; intros Hfalse Htruth; discriminate. Qed.

Definition dm_not_dvd_canonical (x y : nat)
    (Hfalse : Logic.eq (y %| x) false) :
    I.Not
      (dm_imported_dvd (sub_nat_to_imported y) (sub_nat_to_imported x)) :=
  fun HdvdL =>
    dm_coq_false_to_target
      (dm_bool_false_no_truth (y %| x) Hfalse
        (sprop_to_prop _ _
        (dm_dvd_correspondence x (sub_nat_to_imported x)
          y (sub_nat_to_imported y)
          (sub_nat_rel_canonical x) (sub_nat_rel_canonical y)) HdvdL)).

Lemma dm_div_succ_canonical (x y : nat) :
  Lean.eq
    (dm_imported_add
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
      dm_imported_one)
    (sub_nat_to_imported ((x %/ y).+1)).
Proof.
  have Hrel := dm_add_correspondence
    (x %/ y) (dm_imported_div (sub_nat_to_imported x)
      (sub_nat_to_imported y))
    1 dm_imported_one
    (dm_div_correspondence x (sub_nat_to_imported x)
      y (sub_nat_to_imported y)
      (sub_nat_rel_canonical x) (sub_nat_rel_canonical y))
    (sub_nat_rel_canonical 1).
  unfold SubNatRel in Hrel.
  rewrite addn1 in Hrel.
  exact (sub_imported_eq_sym _ _ Hrel).
Qed.

Lemma dm_div_ceil_canonical (x y : nat) :
  Lean.eq
    (dm_imported_div_ceil (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported
      (if y %| x then x %/ y else (x %/ y).+1)).
Proof.
  have Hbody :=
    I.Prosa_Validation_DivModInterface_production_div_ceil_eq
      (sub_nat_to_imported x) (sub_nat_to_imported y).
  destruct (y %| x) eqn:HdvdR.
  - have HdvdR' : is_true (y %| x) by rewrite HdvdR.
    have HdvdL := prop_to_sprop _ _
      (dm_dvd_correspondence x (sub_nat_to_imported x)
        y (sub_nat_to_imported y)
        (sub_nat_rel_canonical x) (sub_nat_rel_canonical y)) HdvdR'.
    have Hif := I.if_pos
      (dm_imported_dvd (sub_nat_to_imported y) (sub_nat_to_imported x))
      (I.Nat_decidable_dvd
        (sub_nat_to_imported y) (sub_nat_to_imported x)) HdvdL
      Lean.Nat
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
      (dm_imported_add
        (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
        dm_imported_one).
    exact (sub_imported_eq_trans _ _ _ Hbody
      (sub_imported_eq_trans _ _ _ Hif (dm_div_canonical x y))).
  - have Hif := I.if_neg
      (dm_imported_dvd (sub_nat_to_imported y) (sub_nat_to_imported x))
      (I.Nat_decidable_dvd
        (sub_nat_to_imported y) (sub_nat_to_imported x))
      (dm_not_dvd_canonical x y HdvdR)
      Lean.Nat
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
      (dm_imported_add
        (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
        dm_imported_one).
    exact (sub_imported_eq_trans _ _ _ Hbody
      (sub_imported_eq_trans _ _ _ Hif (dm_div_succ_canonical x y))).
Qed.

Lemma dm_div_ceil_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel
    (if yR %| xR then xR %/ yR else (xR %/ yR).+1)
    (dm_imported_div_ceil xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (dm_div_ceil_canonical xR yR))
    (sub_imported_eq_congr2 dm_imported_div_ceil _ _ _ _ Hx Hy)).
Qed.

(** The imported target uses propositional [ite] for [Nat] order, whereas
    MathComp computes the corresponding branch with a Boolean test.  Keep
    the negative transport at top level: eliminating an imported [SProp]
    directly inside a local proof would violate Rocq's SProp restriction. *)
Definition dm_not_le_related (aR : nat) (aL : Lean.Nat)
    (bR : nat) (bL : Lean.Nat)
    (Ha : SubNatRel aR aL) (Hb : SubNatRel bR bL)
    (Hfalse : Logic.eq (leq aR bR) false) :
    I.Not (dm_imported_le aL bL) :=
  fun HleL =>
    dm_coq_false_to_target
      (dm_bool_false_no_truth (leq aR bR) Hfalse
        (sprop_to_prop _ _
          (dm_le_correspondence aR aL bR bL Ha Hb) HleL)).

Lemma dm_mod_elim_rhs_canonical (a b c : nat) :
  Lean.eq
    (I.ite Lean.Nat
      (dm_imported_le (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (I.Nat_decLe (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (dm_imported_sub
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_to_imported b))
      (dm_imported_sub
        (dm_imported_add
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
          (sub_nat_to_imported c))
        (sub_nat_to_imported b)))
    (sub_nat_to_imported
      (if leq b (a %% c) then a %% c - b else a %% c + c - b)).
Proof.
  destruct (leq b (a %% c)) eqn:HleR.
  - have HleR' : is_true (leq b (a %% c)) by rewrite HleR.
    have HleL := prop_to_sprop _ _
      (dm_le_correspondence b (sub_nat_to_imported b)
        (a %% c)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_rel_canonical b)
        (dm_mod_correspondence a (sub_nat_to_imported a)
          c (sub_nat_to_imported c)
          (sub_nat_rel_canonical a) (sub_nat_rel_canonical c))) HleR'.
    have Hif := I.if_pos
      (dm_imported_le (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (I.Nat_decLe (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      HleL Lean.Nat
      (dm_imported_sub
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_to_imported b))
      (dm_imported_sub
        (dm_imported_add
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
          (sub_nat_to_imported c))
        (sub_nat_to_imported b)).
    exact (sub_imported_eq_trans _ _ _ Hif
      (sub_imported_eq_sym _ _
        (dm_sub_correspondence (a %% c)
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
          b (sub_nat_to_imported b)
          (dm_mod_correspondence a (sub_nat_to_imported a)
            c (sub_nat_to_imported c)
            (sub_nat_rel_canonical a) (sub_nat_rel_canonical c))
          (sub_nat_rel_canonical b)))).
  - have Hif := I.if_neg
      (dm_imported_le (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (I.Nat_decLe (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (dm_not_le_related b (sub_nat_to_imported b)
        (a %% c)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_rel_canonical b)
        (dm_mod_correspondence a (sub_nat_to_imported a)
          c (sub_nat_to_imported c)
          (sub_nat_rel_canonical a) (sub_nat_rel_canonical c)) HleR)
      Lean.Nat
      (dm_imported_sub
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_to_imported b))
      (dm_imported_sub
        (dm_imported_add
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
          (sub_nat_to_imported c))
        (sub_nat_to_imported b)).
    exact (sub_imported_eq_trans _ _ _ Hif
      (sub_imported_eq_sym _ _
        (dm_sub_correspondence (a %% c + c)
          (dm_imported_add
            (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
            (sub_nat_to_imported c))
          b (sub_nat_to_imported b)
          (dm_add_correspondence (a %% c)
            (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
            c (sub_nat_to_imported c)
            (dm_mod_correspondence a (sub_nat_to_imported a)
              c (sub_nat_to_imported c)
              (sub_nat_rel_canonical a) (sub_nat_rel_canonical c))
            (sub_nat_rel_canonical c))
          (sub_nat_rel_canonical b)))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section TdmaSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cxt_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicExtractionTdmaInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicExtractionTdmaInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cxt_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cxt_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cxt_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicExtractionTdmaInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicExtractionTdmaInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicExtractionTdmaInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cxt_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cxt_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End TdmaSums.

(* ------------------------------------------------------------------ *)
(** * Task sets, slots and slot orders *)

Section TdmaRel.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Notation LSet := (I.Prosa_Util_Seqset_set Task dT).

Definition CxtSetRel (sR : {set Task}) (sL : LSet) : SProp :=
  ClListRel cid (@prosa.util.seqset._set_seq Task sR) (I.Prosa_Util_Seqset_set_val Task dT sL).

Lemma cxt_uniq_rel (xs : seq Task) : PropSPropRel (uniq xs) (I.List_Nodup Task (cl_map cid xs)).
Proof. exact (cl_uniq_rel Task Task cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) xs). Qed.

Definition cxt_set_to_target (sR : {set Task}) : LSet :=
  match sR with
  | @prosa.util.seqset.Build_set _ xs Hu =>
      I.Prosa_Util_Seqset_set_mk Task dT (cl_map cid xs) (prop_to_sprop _ _ (cxt_uniq_rel xs) Hu)
  end.

Lemma cxt_import_uniq (xs : I.List Task) (Hn : I.List_Nodup Task xs) : uniq (cl_unmap cid xs).
Proof.
  apply (sprop_to_prop _ _ (cxt_uniq_rel (cl_unmap cid xs))).
  rewrite (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) xs). exact Hn.
Qed.

Definition cxt_set_to_source (sL : LSet) : {set Task} :=
  match sL with
  | I.Prosa_Util_Seqset_set_mk xs Hn => @prosa.util.seqset.Build_set Task (cl_unmap cid xs) (cxt_import_uniq xs Hn)
  end.

Lemma cxt_set_canonical sR : CxtSetRel sR (cxt_set_to_target sR).
Proof. destruct sR. exact (@Lean.eq_refl _ _). Qed.

Lemma cxt_set_surjective sL : CxtSetRel (cxt_set_to_source sL) sL.
Proof.
  destruct sL as [xs Hn]. unfold CxtSetRel. cbn.
  exact (coq_eq_to_imported_eq _ _ (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) xs)).
Qed.

Lemma cxt_forall_set (PR : {set Task} -> Prop) (PL : LSet -> SProp) :
  (forall sR sL, CxtSetRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cxt_forall_cover _ _ CxtSetRel cxt_set_to_target cxt_set_to_source cxt_set_canonical cxt_set_surjective PR PL). Qed.

Definition CxtOrdRel (oR : rel Task) (oL : Task -> Task -> I.Bool) : SProp := forall a b, CtBoolRel (oR a b) (oL a b).

Definition cxt_ord_to_target (oR : rel Task) : Task -> Task -> I.Bool := fun a b => ct_b2l (oR a b).
Definition cxt_ord_to_source (oL : Task -> Task -> I.Bool) : rel Task := fun a b => ct_l2b (oL a b).

Lemma cxt_ord_canonical oR : CxtOrdRel oR (cxt_ord_to_target oR).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cxt_ord_surjective oL : CxtOrdRel (cxt_ord_to_source oL) oL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cxt_forall_ord (PR : rel Task -> Prop) (PL : (Task -> Task -> I.Bool) -> SProp) :
  (forall oR oL, CxtOrdRel oR oL -> PropSPropRel (PR oR) (PL oL)) -> PropSPropRel (forall o, PR o) (forall o, PL o).
Proof. exact (cxt_forall_cover _ _ CxtOrdRel cxt_ord_to_target cxt_ord_to_source cxt_ord_canonical cxt_ord_surjective PR PL). Qed.

Lemma cxt_neq x y : CtBoolRel (x != y) (I.Bool_not (I.Decidable_decide (Lean.eq x y) (dT x y))).
Proof. exact (ct_bool_not _ _ (ct_decide_eq Task x y)). Qed.

End TdmaRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section TdmaDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).

Lemma cxt_TD_TDMA_slot :
  And (forall sR : PolicyTDMA.TDMA_slot Task, CxtParRel Task sR (fun x => sub_nat_to_imported (sR x)))
      (forall sL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot Task dT, CxtParRel Task (fun x => sub_nat_to_rocq (sL x)) sL).
Proof.
  exact (And_intro _ _ (fun sR x => sub_nat_rel_canonical (sR x)) (fun sL x => sub_nat_rel_surjective (sL x))).
Qed.

Lemma cxt_TD_TDMA_slot_order :
  And (forall oR : PolicyTDMA.TDMA_slot_order Task, CxtOrdRel Task oR (cxt_ord_to_target Task oR))
      (forall oL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot_order Task dT, CxtOrdRel Task (cxt_ord_to_source Task oL) oL).
Proof. exact (And_intro _ _ (cxt_ord_canonical Task) (cxt_ord_surjective Task)). Qed.

Lemma cxt_TD_TDMA_cycle sR sL (Hs : CxtSetRel Task sR sL) slR slL (Hsl : CxtParRel Task slR slL) :
  SubNatRel (PolicyTDMA.TDMA_cycle sR slR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_cycle Task dT sL slL).
Proof. exact (cxt_sum_rel Task slR slL Hsl _ _ Hs). Qed.

Lemma cxt_TD_Task_slot_offset sR sL (Hs : CxtSetRel Task sR sL) oR oL (Ho : CxtOrdRel Task oR oL)
    task slR slL (Hsl : CxtParRel Task slR slL) :
  SubNatRel (PolicyTDMA.Task_slot_offset sR oR task slR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_Task_slot_offset Task dT sL oL task slL).
Proof.
  exact (cxt_sum_filtered_rel Task slR slL Hsl _
    (fun p => I.Bool_and (oL p task) (I.Bool_not (I.Decidable_decide (Lean.eq p task) (dT p task))))
    (fun p => ct_bool_and _ _ _ _ (Ho p task) (cxt_neq Task p task)) _ _ Hs).
Qed.

Lemma cxt_TD_Task_in_time_slot sR sL (Hs : CxtSetRel Task sR sL) oR oL (Ho : CxtOrdRel Task oR oL)
    task slR slL (Hsl : CxtParRel Task slR slL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (PolicyTDMA.Task_in_time_slot sR oR task slR tR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_Task_in_time_slot Task dT sL oL task slL tL).
Proof.
  have HC := cxt_TD_TDMA_cycle sR sL Hs slR slL Hsl.
  have HO := cxt_TD_Task_slot_offset sR sL Hs oR oL Ho task slR slL Hsl.
  apply: ct_decide_lt; last exact (Hsl task).
  apply: dm_mod_correspondence; last exact HC.
  apply: dm_sub_correspondence; last exact (dm_mod_correspondence _ _ _ _ HO HC).
  exact (sub_add_correspondence _ _ _ _ Ht HC).
Qed.

End TdmaDefs.

Lemma cxt_pred_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ct_sub nL (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Hn. apply: coq_eq_to_imported_eq. rewrite -subn1.
  exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1))).
Qed.

Lemma cxt_iff (P Q : Prop) (PL QL : SProp) :
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

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section TWTDPDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CxtSchedRel Job sR sL.
Variables (tsR : {set Task}) (tsL : I.Prosa_Util_Seqset_set Task dT).
Hypothesis Hts : CxtSetRel Task tsR tsL.
Variables (slR : PolicyTDMA.TDMA_slot Task) (slL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot Task dT).
Hypothesis Hsl : CxtParRel Task slR slL.
Variables (oR : PolicyTDMA.TDMA_slot_order Task) (oL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot_order Task dT).
Hypothesis Ho : CxtOrdRel Task oR oL.
Variable job_task : Job -> Task.

Lemma cxt_in_slot j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (PolicyTDMA.Task_in_time_slot tsR oR (job_task j) slR tR)
    (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_Task_in_time_slot Task dT tsL oL (job_task j) slL tL).
Proof. exact (cxt_TD_Task_in_time_slot Task tsR tsL Hts oR oL Ho (job_task j) slR slL Hsl tR tL Ht). Qed.

Lemma cxt_TDP_sched_implies_in_slot j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (Platform_TDMA.sched_implies_in_slot job_task sR tsR slR oR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Basic_PlatformTdma_Platform_TDMA_sched_implies_in_slot Task dT Job dJ job_task sL tsL slL oL j tL).
Proof.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cxt_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (cxt_in_slot j tR tL Ht)).
Qed.

Lemma cxt_TDP_backlogged_implies_not_in_slot_or_other_job_sched aR aL (Ha : CxtParRel Job aR aL)
    cR cL (Hc : CxtParRel Job cR cL) arrR arrL (Harr : CxtArrRel Job arrR arrL) j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (Platform_TDMA.backlogged_implies_not_in_slot_or_other_job_sched aR cR job_task arrR sR tsR slR oR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Basic_PlatformTdma_Platform_TDMA_backlogged_implies_not_in_slot_or_other_job_sched Task dT Job dJ aL cL job_task arrL sL tsL slL oL j tL).
Proof.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cxt_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_or.
  - apply: ct_imp; first exact (ct_bool_truth _ _ (cxt_in_slot j tR tL Ht)).
    exact cxt_false_rel.
  - apply: ct_exists_identity => j_other.
    apply: ct_and; first exact (cxt_arrives_in Job arrR arrL Harr j_other).
    apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha j_other) (Ha j)).
    apply: ct_and; first exact (ct_eq_rel Task (job_task j) (job_task j_other)).
    exact (ct_bool_truth _ _ (cxt_US_scheduled_at Job sR sL Hs j_other tR tL Ht)).
Qed.

Lemma cxt_TDP_Respects_TDMA_policy aR aL (Ha : CxtParRel Job aR aL)
    cR cL (Hc : CxtParRel Job cR cL) arrR arrL (Harr : CxtArrRel Job arrR arrL) :
  PropSPropRel (Platform_TDMA.Respects_TDMA_policy aR cR job_task arrR sR tsR slR oR)
    (I.Prosa_Classic_Model_Schedule_Uni_Basic_PlatformTdma_Platform_TDMA_Respects_TDMA_policy Task dT Job dJ aL cL job_task arrL sL tsL slL oL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cxt_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (cxt_TDP_sched_implies_in_slot j tR tL Ht).
  exact (cxt_TDP_backlogged_implies_not_in_slot_or_other_job_sched aR aL Ha cR cL Hc arrR arrL Harr j tR tL Ht).
Qed.

End TWTDPDefs.

(* ------------------------------------------------------------------ *)
(** * [diagnosis_option] (constructor-wise, related instants) *)

Notation nc := sub_nat_to_imported.
Notation EQ H := (imported_eq_to_coq_eq _ _ H).

Definition cxt_dg_to_target (d : end_time.diagnosis_option) : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option :=
  match d with
  | end_time.OK t => I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK (nc t)
  | end_time.Failure t => I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_Failure (nc t)
  end.
Definition cxt_dg_to_source (d : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option) : end_time.diagnosis_option :=
  match d with
  | I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK t => end_time.OK (sub_nat_to_rocq t)
  | I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_Failure t => end_time.Failure (sub_nat_to_rocq t)
  end.
Definition CxtDgRel (dR : end_time.diagnosis_option) (dL : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option) : SProp :=
  Lean.eq (cxt_dg_to_target dR) dL.

Lemma cxt_dg_ts d : Logic.eq (cxt_dg_to_source (cxt_dg_to_target d)) d.
Proof. case: d => t /=; by rewrite sub_nat_rocq_roundtrip. Qed.

Lemma cxt_dg_eq dR1 dL1 dR2 dL2 (H1 : CxtDgRel dR1 dL1) (H2 : CxtDgRel dR2 dL2) :
  PropSPropRel (Logic.eq dR1 dR2) (Lean.eq dL1 dL2).
Proof.
  rewrite -(EQ H1) -(EQ H2). clear H1 H2. apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. have E' := f_equal cxt_dg_to_source (EQ E). by rewrite !cxt_dg_ts in E'.
Qed.

Lemma cxt_OK tR tL (Ht : SubNatRel tR tL) : CxtDgRel (end_time.OK tR) (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK tL).
Proof. exact (sub_imported_eq_congr (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK) _ _ Ht). Qed.

Lemma cxt_not_rel (P : Prop) (PL : SProp) : PropSPropRel P PL -> PropSPropRel (~ P) (I.Not PL).
Proof. intro H. exact (ct_imp _ _ _ _ H cxt_false_rel). Qed.

(* ------------------------------------------------------------------ *)
(** * [end_time_option] and [end_time_predicate] *)

Section TWETEndTime.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CxtSchedRel Job sR sL.
Variable job : Job.
Notation SA := (cxt_US_scheduled_at Job sR sL Hs job).

Lemma cxt_back_rel tL : SubNatRel (sub_nat_to_rocq tL) tL.
Proof. exact (sub_nat_imported_roundtrip tL). Qed.

End TWETEndTime.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cxt_dg_st d : Logic.eq (cxt_dg_to_target (cxt_dg_to_source d)) d.
Proof.
  case: d => t /=; by rewrite (EQ (sub_nat_imported_roundtrip t)).
Qed.

(** The inductive [diagnosis_option]: the constructor-wise relation is total in both directions. *)
Lemma cxt_ET_diagnosis_option :
  And (forall dR : end_time.diagnosis_option, CxtDgRel dR (cxt_dg_to_target dR))
      (forall dL : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option, CxtDgRel (cxt_dg_to_source dL) dL).
Proof.
  exact (And_intro _ _ (fun dR => @Lean.eq_refl _ _) (fun dL => coq_eq_to_imported_eq _ _ (cxt_dg_st dL))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Conditionals *)

(** A Lean [ite] on a decidable proposition against a Rocq Boolean [if], given the relation of the
    Boolean test to the proposition (any decision procedure). *)
Lemma cxt_ite_nat (bR : bool) (P : SProp) (d : I.Decidable P) (H : PropSPropRel (is_true bR) P)
    xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) :
  SubNatRel (if bR then xR else yR) (I.ite Lean.Nat P d xL yL).
Proof.
  destruct d as [Hf | Ht]; destruct bR; cbn.
  - exact (ct_false_elim _ (Hf (prop_to_sprop _ _ H (Logic.eq_refl true)))).
  - exact Hy.
  - exact Hx.
  - exact (ct_false_elim _ (ct_coq_false_to_target (match sprop_to_prop _ _ H Ht with end))).
Qed.

Lemma cxt_eqn0 nR nL (Hn : SubNatRel nR nL) :
  PropSPropRel (is_true (nR == 0)) (Lean.eq nL (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))).
Proof.
  have E := sub_nat_eq_correspondence _ _ _ _ Hn (sub_nat_rel_canonical 0).
  apply prop_sprop_rel_intro.
  - move=> /eqP H. exact (prop_to_sprop _ _ E H).
  - intro H. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ E H).
Qed.

(* ------------------------------------------------------------------ *)
(** * The section-local arithmetic [Let]s (Lean [LEAN_HELPER] definitions) *)

Section TWArith.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tsR : {set Task}) (tsL : I.Prosa_Util_Seqset_set Task dT).
Hypothesis Hts : CxtSetRel Task tsR tsL.
Variables (slR : PolicyTDMA.TDMA_slot Task) (slL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot Task dT).
Hypothesis Hsl : CxtParRel Task slR slL.
Variables (oR : PolicyTDMA.TDMA_slot_order Task) (oL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot_order Task dT).
Hypothesis Ho : CxtOrdRel Task oR oL.
Variable tsk : Task.
Notation HC := (cxt_TD_TDMA_cycle Task tsR tsL Hts slR slL Hsl).
Notation HO := (cxt_TD_Task_slot_offset Task tsR tsL Hts oR oL Ho tsk slR slL Hsl).
Notation cyc := (PolicyTDMA.TDMA_cycle tsR slR).
Notation FS t := ((t + cyc - PolicyTDMA.Task_slot_offset tsR oR tsk slR %% cyc) %% cyc).

End TWArith.

Lemma cxt_TW_WCRT_formula cyR cyL (Hcy : SubNatRel cyR cyL) sR sL (Hs : SubNatRel sR sL) wR wL (Hw : SubNatRel wR wL) :
  SubNatRel (WCRT_OneJobTDMA.WCRT_formula cyR sR wR) (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_WCRT_formula cyL sL wL).
Proof.
  exact (dm_add_correspondence _ _ _ _
    (dm_mul_correspondence _ _ _ _ (dm_div_ceil_correspondence _ _ _ _ Hw Hs) (dm_sub_correspondence _ _ _ _ Hcy Hs)) Hw).
Qed.

(* ------------------------------------------------------------------ *)
(** * Section hypotheses shared by the lemmas *)

Lemma cxt_allprev (Task Job : eqType) aR aL (Ha : CxtParRel Job aR aL) cR cL (Hc : CxtParRel Job cR cL) (job_task : Job -> Task)
    arrR arrL (Harr : CxtArrRel Job arrR arrL) sR sL (Hs : CxtSchedRel Job sR sL) j :
  PropSPropRel
    (forall j_other, ArrivalSequence.arrives_in arrR j_other -> job_task j = job_task j_other ->
       aR j_other < aR j -> UniprocessorSchedule.completed_by cR sR j_other (aR j))
    (forall j_other, I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job (ct_decidable_eq Job) arrL j_other ->
       Lean.eq (job_task j) (job_task j_other) -> I.LT_lt_inst1 Lean.Nat I.instLTNat (aL j_other) (aL j) ->
       Lean.eq (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job (ct_decidable_eq Job) cL sL j_other (aL j)) I.Bool_true).
Proof.
  apply: ct_forall_identity => jo.
  apply: ct_imp; first exact (cxt_arrives_in Job arrR arrL Harr jo).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task jo)).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha jo) (Ha j)).
  exact (ct_bool_truth _ _ (cxt_US_completed_by Job sR sL Hs cR cL Hc jo _ _ (Ha j))).
Qed.

(* ------------------------------------------------------------------ *)
(** * The informative reflection [TDMA_policy_case_RT_le_Period] *)

(* ------------------------------------------------------------------ *)
(** * [Task_T] (constructor-wise, field-wise [SubNatRel]) *)

Notation nr := sub_nat_to_rocq.

Definition cxt_to_target (t : extraction_tdma.Task_T) : I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_Task_T :=
  match t with extraction_tdma.build_task a b c d => I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_Task_T_build_task (nc a) (nc b) (nc c) (nc d) end.
Definition cxt_to_source (t : I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_Task_T) : extraction_tdma.Task_T :=
  match t with I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_Task_T_build_task a b c d => extraction_tdma.build_task (nr a) (nr b) (nr c) (nr d) end.
Definition CxtTRel (tR : extraction_tdma.Task_T) (tL : I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_Task_T) : SProp := Lean.eq (cxt_to_target tR) tL.
Definition CxtLRel := ClListRel1 cxt_to_target.

Lemma cxt_ts t : Logic.eq (cxt_to_source (cxt_to_target t)) t.
Proof.
  case: t => a b c d.
  change (Logic.eq (extraction_tdma.build_task (nr (nc a)) (nr (nc b)) (nr (nc c)) (nr (nc d))) (extraction_tdma.build_task a b c d)).
  by rewrite !sub_nat_rocq_roundtrip.
Qed.
Lemma cxt_st t : Logic.eq (cxt_to_target (cxt_to_source t)) t.
Proof.
  case: t => a b c d.
  change (Logic.eq (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_Task_T_build_task (nc (nr a)) (nc (nr b)) (nc (nr c)) (nc (nr d))) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_Task_T_build_task a b c d)).
  by rewrite (EQ (sub_nat_imported_roundtrip a)) (EQ (sub_nat_imported_roundtrip b))
             (EQ (sub_nat_imported_roundtrip c)) (EQ (sub_nat_imported_roundtrip d)).
Qed.

Lemma cxt_eq tR1 tL1 tR2 tL2 (H1 : CxtTRel tR1 tL1) (H2 : CxtTRel tR2 tL2) :
  PropSPropRel (Logic.eq tR1 tR2) (Lean.eq tL1 tL2).
Proof.
  rewrite -(EQ H1) -(EQ H2). clear H1 H2. apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. have E' := f_equal cxt_to_source (EQ E). by rewrite !cxt_ts in E'.
Qed.

Lemma cxt_forall_task (PR : extraction_tdma.Task_T -> Prop) (PL : I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_Task_T -> SProp) :
  (forall tR tL, CxtTRel tR tL -> PropSPropRel (PR tR) (PL tL)) -> PropSPropRel (forall t, PR t) (forall t, PL t).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR tL. exact (prop_to_sprop _ _ (H _ _ (coq_eq_to_imported_eq _ _ (cxt_st tL))) (HR _)).
  - intro HL. apply strictly_inhabits. intro tR. exact (sprop_to_prop _ _ (H tR _ (@Lean.eq_refl _ _)) (HL _)).
Qed.

Lemma cxt_forall_tlist (PR : seq extraction_tdma.Task_T -> Prop) (PL : I.List_inst1 I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_Task_T -> SProp) :
  (forall sR sL, CxtLRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl1_forall_list cxt_to_target cxt_to_source cxt_st PR PL). Qed.

Lemma cxt_get_slot_eq t : Logic.eq (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_get_slot (cxt_to_target t)) (nc (extraction_tdma.get_slot t)).
Proof. case: t => a b c d. exact (EQ (I.Prosa_Validation_ClassicExtractionTdmaInterface_xt_get_slot_eq (nc a) (nc b) (nc c) (nc d))). Qed.
Lemma cxt_get_cost_eq t : Logic.eq (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_get_cost (cxt_to_target t)) (nc (extraction_tdma.get_cost t)).
Proof. case: t => a b c d. exact (EQ (I.Prosa_Validation_ClassicExtractionTdmaInterface_xt_get_cost_eq (nc a) (nc b) (nc c) (nc d))). Qed.
Lemma cxt_get_D_eq t : Logic.eq (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_get_D (cxt_to_target t)) (nc (extraction_tdma.get_D t)).
Proof. case: t => a b c d. exact (EQ (I.Prosa_Validation_ClassicExtractionTdmaInterface_xt_get_D_eq (nc a) (nc b) (nc c) (nc d))). Qed.
Lemma cxt_get_P_eq t : Logic.eq (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_get_P (cxt_to_target t)) (nc (extraction_tdma.get_P t)).
Proof. case: t => a b c d. exact (EQ (I.Prosa_Validation_ClassicExtractionTdmaInterface_xt_get_P_eq (nc a) (nc b) (nc c) (nc d))). Qed.

Lemma cxt_get_slot tR tL (H : CxtTRel tR tL) : SubNatRel (extraction_tdma.get_slot tR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_get_slot tL).
Proof. rewrite -(EQ H) cxt_get_slot_eq. exact (sub_nat_rel_canonical _). Qed.
Lemma cxt_get_cost tR tL (H : CxtTRel tR tL) : SubNatRel (extraction_tdma.get_cost tR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_get_cost tL).
Proof. rewrite -(EQ H) cxt_get_cost_eq. exact (sub_nat_rel_canonical _). Qed.
Lemma cxt_get_D tR tL (H : CxtTRel tR tL) : SubNatRel (extraction_tdma.get_D tR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_get_D tL).
Proof. rewrite -(EQ H) cxt_get_D_eq. exact (sub_nat_rel_canonical _). Qed.
Lemma cxt_get_P tR tL (H : CxtTRel tR tL) : SubNatRel (extraction_tdma.get_P tR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_get_P tL).
Proof. rewrite -(EQ H) cxt_get_P_eq. exact (sub_nat_rel_canonical _). Qed.

Lemma cxt_task_eq tR1 tL1 (H1 : CxtTRel tR1 tL1) tR2 tL2 (H2 : CxtTRel tR2 tL2) :
  CtBoolRel (extraction_tdma.task_eq tR1 tR2) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_task_eq tL1 tL2).
Proof.
  exact (ct_bool_and _ _ _ _ (ct_bool_and _ _ _ _ (ct_bool_and _ _ _ _
    (ct_decide_eq_nat _ _ _ _ (cxt_get_slot _ _ H1) (cxt_get_slot _ _ H2))
    (ct_decide_eq_nat _ _ _ _ (cxt_get_cost _ _ H1) (cxt_get_cost _ _ H2)))
    (ct_decide_eq_nat _ _ _ _ (cxt_get_D _ _ H1) (cxt_get_D _ _ H2)))
    (ct_decide_eq_nat _ _ _ _ (cxt_get_P _ _ H1) (cxt_get_P _ _ H2))).
Qed.

(* ------------------------------------------------------------------ *)
(** * The list fixpoints *)

Lemma cxt_In_list a : forall sR,
  PropSPropRel (extraction_tdma.In a sR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_In (cxt_to_target a) (cl1_map cxt_to_target sR)).
Proof.
  elim => [|b s IH].
  - rewrite (EQ (I.Prosa_Validation_ClassicExtractionTdmaInterface_xt_In_nil (cxt_to_target a))). exact cxt_false_rel.
  - rewrite (EQ (I.Prosa_Validation_ClassicExtractionTdmaInterface_xt_In_cons (cxt_to_target a) (cxt_to_target b) (cl1_map cxt_to_target s))).
    exact (ct_or _ _ _ _ (cxt_eq _ _ _ _ (@Lean.eq_refl _ _) (@Lean.eq_refl _ _)) IH).
Qed.

Lemma cxt_In aR aL (Ha : CxtTRel aR aL) sR sL (Hs : CxtLRel sR sL) :
  PropSPropRel (extraction_tdma.In aR sR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_In aL sL).
Proof. rewrite -(EQ Ha) -(EQ Hs). exact (cxt_In_list aR sR). Qed.

Lemma cxt_schedulable_tsk_eq T tsk : Logic.eq (extraction_tdma.schedulable_tsk T tsk)
  ((WCRT_OneJobTDMA.WCRT_formula T (extraction_tdma.get_slot tsk) (extraction_tdma.get_cost tsk) <= extraction_tdma.get_D tsk) &&
   (WCRT_OneJobTDMA.WCRT_formula T (extraction_tdma.get_slot tsk) (extraction_tdma.get_cost tsk) <= extraction_tdma.get_P tsk)).
Proof. rewrite /extraction_tdma.schedulable_tsk. by case: (_ && _). Qed.

Lemma cxt_schedulable_tsk TR TL (HT : SubNatRel TR TL) tR tL (Ht : CxtTRel tR tL) :
  CtBoolRel (extraction_tdma.schedulable_tsk TR tR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_schedulable_tsk TL tL).
Proof.
  rewrite cxt_schedulable_tsk_eq (EQ (I.Prosa_Validation_ClassicExtractionTdmaInterface_xt_schedulable_tsk_eq TL tL)).
  have W := cxt_TW_WCRT_formula _ _ HT _ _ (cxt_get_slot _ _ Ht) _ _ (cxt_get_cost _ _ Ht).
  exact (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ W (cxt_get_D _ _ Ht)) (ct_decide_le _ _ _ _ W (cxt_get_P _ _ Ht))).
Qed.

Lemma cxt_test_list TR TL (HT : SubNatRel TR TL) : forall sR,
  CtBoolRel (extraction_tdma.schedulability_test TR sR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_schedulability_test TL (cl1_map cxt_to_target sR)).
Proof.
  intro sR; induction sR as [|x s IH].
  - rewrite (EQ (I.Prosa_Validation_ClassicExtractionTdmaInterface_xt_test_nil TL)). exact (ct_bool_canonical true).
  - rewrite (EQ (I.Prosa_Validation_ClassicExtractionTdmaInterface_xt_test_cons TL (cxt_to_target x) (cl1_map cxt_to_target s))).
    exact (ct_bool_and _ _ _ _ (cxt_schedulable_tsk _ _ HT _ _ (@Lean.eq_refl _ _)) IH).
Qed.

Lemma cxt_schedulability_test TR TL (HT : SubNatRel TR TL) sR sL (Hs : CxtLRel sR sL) :
  CtBoolRel (extraction_tdma.schedulability_test TR sR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_schedulability_test TL sL).
Proof. rewrite -(EQ Hs). exact (cxt_test_list _ _ HT sR). Qed.

Lemma cxt_cycle_list : forall sR, SubNatRel (extraction_tdma.cycle sR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_cycle (cl1_map cxt_to_target sR)).
Proof.
  intro sR; induction sR as [|x s IH].
  - rewrite (EQ (I.Prosa_Validation_ClassicExtractionTdmaInterface_xt_cycle_nil)). exact (sub_nat_rel_canonical 0).
  - rewrite (EQ (I.Prosa_Validation_ClassicExtractionTdmaInterface_xt_cycle_cons (cxt_to_target x) (cl1_map cxt_to_target s))).
    exact (sub_add_correspondence _ _ _ _ (cxt_get_slot _ _ (@Lean.eq_refl _ _)) IH).
Qed.

Lemma cxt_cycle sR sL (Hs : CxtLRel sR sL) : SubNatRel (extraction_tdma.cycle sR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_cycle sL).
Proof. rewrite -(EQ Hs). exact (cxt_cycle_list sR). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(** The coinductive [Task_T] (one non-recursive constructor): the constructor-wise relation is total in both
    directions. *)
Theorem Task_T_correspondence :
  And (forall tR : extraction_tdma.Task_T, CxtTRel tR (cxt_to_target tR))
      (forall tL : I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_Task_T, CxtTRel (cxt_to_source tL) tL).
Proof.
  exact (And_intro _ _ (fun tR => @Lean.eq_refl _ _) (fun tL => coq_eq_to_imported_eq _ _ (cxt_st tL))).
Qed.

Theorem get_slot_correspondence tR tL (H : CxtTRel tR tL) : SubNatRel (extraction_tdma.get_slot tR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_get_slot tL).
Proof. exact (cxt_get_slot _ _ H). Qed.
Theorem get_cost_correspondence tR tL (H : CxtTRel tR tL) : SubNatRel (extraction_tdma.get_cost tR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_get_cost tL).
Proof. exact (cxt_get_cost _ _ H). Qed.
Theorem get_D_correspondence tR tL (H : CxtTRel tR tL) : SubNatRel (extraction_tdma.get_D tR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_get_D tL).
Proof. exact (cxt_get_D _ _ H). Qed.
Theorem get_P_correspondence tR tL (H : CxtTRel tR tL) : SubNatRel (extraction_tdma.get_P tR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_get_P tL).
Proof. exact (cxt_get_P _ _ H). Qed.
Theorem task_eq_correspondence tR1 tL1 (H1 : CxtTRel tR1 tL1) tR2 tL2 (H2 : CxtTRel tR2 tL2) :
  CtBoolRel (extraction_tdma.task_eq tR1 tR2) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_task_eq tL1 tL2).
Proof. exact (cxt_task_eq _ _ H1 _ _ H2). Qed.
Theorem In_correspondence aR aL (Ha : CxtTRel aR aL) sR sL (Hs : CxtLRel sR sL) :
  PropSPropRel (extraction_tdma.In aR sR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_In aL sL).
Proof. exact (cxt_In _ _ Ha _ _ Hs). Qed.
Theorem schedulable_tsk_correspondence TR TL (HT : SubNatRel TR TL) tR tL (Ht : CxtTRel tR tL) :
  CtBoolRel (extraction_tdma.schedulable_tsk TR tR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_schedulable_tsk TL tL).
Proof. exact (cxt_schedulable_tsk _ _ HT _ _ Ht). Qed.
Theorem schedulability_test_correspondence TR TL (HT : SubNatRel TR TL) sR sL (Hs : CxtLRel sR sL) :
  CtBoolRel (extraction_tdma.schedulability_test TR sR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_schedulability_test TL sL).
Proof. exact (cxt_schedulability_test _ _ HT _ _ Hs). Qed.
Theorem cycle_correspondence sR sL (Hs : CxtLRel sR sL) : SubNatRel (extraction_tdma.cycle sR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_cycle sL).
Proof. exact (cxt_cycle _ _ Hs). Qed.
Theorem schedulability_tdma_correspondence sR sL (Hs : CxtLRel sR sL) :
  CtBoolRel (extraction_tdma.schedulability_tdma sR) (I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_schedulability_tdma sL).
Proof. exact (cxt_schedulability_test _ _ (cxt_cycle _ _ Hs) _ _ Hs). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_schedulability_test_valid : Prop := ltac:(type_of_term extraction_tdma.schedulability_test_valid).
Definition tgt_schedulability_test_valid : SProp := ltac:(type_of_term I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_schedulability_test_valid).
Theorem schedulability_test_valid_correspondence :
  PropSPropRel src_schedulability_test_valid tgt_schedulability_test_valid.
Proof.
  unfold src_schedulability_test_valid, tgt_schedulability_test_valid.
  apply: ct_forall_nat => TR TL HT. apply: cxt_forall_tlist => sR sL Hs.
  apply: cxt_iff; first exact (ct_bool_truth _ _ (cxt_schedulability_test _ _ HT _ _ Hs)).
  apply: cxt_forall_task => tR tL Ht. apply: ct_imp; first exact (cxt_In _ _ Ht _ _ Hs).
  exact (ct_bool_truth _ _ (cxt_schedulable_tsk _ _ HT _ _ Ht)).
Qed.

Definition src_schedulability_tdma_valid : Prop := ltac:(type_of_term extraction_tdma.schedulability_tdma_valid).
Definition tgt_schedulability_tdma_valid : SProp := ltac:(type_of_term I.Prosa_Classic_Implementation_Uni_Basic_ExtractionTdma_schedulability_tdma_valid).
Theorem schedulability_tdma_valid_correspondence :
  PropSPropRel src_schedulability_tdma_valid tgt_schedulability_tdma_valid.
Proof.
  unfold src_schedulability_tdma_valid, tgt_schedulability_tdma_valid.
  apply: cxt_forall_tlist => sR sL Hs.
  apply: cxt_iff; first exact (ct_bool_truth _ _ (schedulability_tdma_correspondence _ _ Hs)).
  apply: cxt_forall_task => tR tL Ht. apply: ct_imp; first exact (cxt_In _ _ Ht _ _ Hs).
  exact (ct_bool_truth _ _ (cxt_schedulable_tsk _ _ (cxt_cycle _ _ Hs) _ _ Ht)).
Qed.
