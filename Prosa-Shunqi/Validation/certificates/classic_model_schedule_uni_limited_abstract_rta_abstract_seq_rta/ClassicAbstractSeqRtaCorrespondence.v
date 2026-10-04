From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.arrival.curves.bounds classic.analysis.uni.arrival_curves.workload_bound classic.model.schedule.uni.schedule classic.model.schedule.uni.service classic.model.schedule.uni.workload classic.model.schedule.uni.schedule_of_task classic.model.schedule.uni.response_time classic.model.schedule.uni.limited.schedule classic.model.schedule.uni.limited.abstract_RTA.definitions classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicAbstractSeqRta.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicAbstractSeqRtaBase ClassicAbstractSeqRtaList.



Module I := ImportedClassicAbstractSeqRta.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/abstract_RTA/abstract_seq_rta.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the eqTypes'
    decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job and task parameters
    pointwise through [SubNatRel]; task sequences elementwise; arrival curves pointwise on related arguments; arrival
    sequences pointwise on related times; interference predicates, interfering workloads and interference bound
    functions pointwise on related arguments; uniprocessor schedules pointwise through the option map; all with two-way
    totals.  The abstract-RTA, reduction-of-search-space, lock-in-service, service, workload, task-arrival,
    arrival-curve and request-bound notions as in the accepted classic certificates (re-bound below);
    [cumul_task_interference] and [cumul_interference] through kernel-guarded [rfl] body projections; [has] against
    [List.any].

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof is not
    used).  Where the task cost precedes the job type in both binder lists, the job type is fixed as an [eqType] with
    its canonical Lean instance and the task cost stays universally quantified on both sides. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cqs_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cqs_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cqs_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cqs_false_rel). Qed.

Lemma cqs_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cqs_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cqs_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cqs_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cqs_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cqs_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cqs_unmap_rel T l) PR PL).
Qed.

Definition CqsParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cqs_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CqsParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cqs_forall_cover _ _ (CqsParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cqs_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cqs_natl s') end.

Definition cqs_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cqs_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cqs_one) (cqs_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cqs_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cqs_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cqs_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cqs_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cqs_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cqs_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cqs_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cqs_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cqs_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cqs_cl_append. reflexivity.
Qed.

Lemma cqs_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CqsFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cqs_bigcat_rel (A : Type) fR fL (Hf : CqsFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicAbstractSeqRtaInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cqs_iota_range (nR - mR) 0) cqs_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cqs_cl_map_ext _ _ Hpt) (cqs_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cqs_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cqs_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CqsArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cqs_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cqs_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cqs_arr_canonical aR : CqsArrRel aR (cqs_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cqs_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cqs_arr_surjective aL : CqsArrRel (cqs_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cqs_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CqsArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cqs_forall_cover _ _ CqsArrRel cqs_arr_to_target cqs_arr_to_source cqs_arr_canonical cqs_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cqs_jobs_arrived_between aR aL (Ha : CqsArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cqs_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cqs_arrives_in aR aL (Ha : CqsArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cqs_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cqs_consistent pR pL (Hp : CqsParRel Job pR pL) aR aL (Ha : CqsArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cqs_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cqs_arrives_at aR aL (Ha : CqsArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cqs_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma cqs_has_arrived pR pL (Hp : CqsParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

Lemma cqs_arrived_before pR pL (Hp : CqsParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrived_before pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_before Job dJ pL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (Hp j) Ht). Qed.

Lemma cqs_arrived_between pR pL (Hp : CqsParRel Job pR pL) j t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  CtBoolRel (ArrivalSequence.arrived_between pR j t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_between Job dJ pL j t1L t2L).
Proof. exact (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Hp j)) (ct_decide_lt _ _ _ _ (Hp j) H2)). Qed.

End ArrivalDefs2.

Fixpoint cqs_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cqs_snatl s') end.

Lemma cqs_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cqs_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cqs_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cqs_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cqs_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cqs_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cqs_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CqsFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cqs_fun_canonical FR FL (HF : CqsFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cqs_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cqs_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CqsFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cqs_nat_sub_canonical nR mR.
  rewrite cqs_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cqs_foldr_add FL FR (cqs_fun_canonical FR FL HF)).
  by rewrite cqs_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cqs_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cqs_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cqs_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cqs_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cqs_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CqsSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cqs_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cqs_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cqs_sched_canonical sR : CqsSchedRel sR (cqs_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cqs_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cqs_sched_surjective sL : CqsSchedRel (cqs_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cqs_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cqs_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CqsSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cqs_forall_cover _ _ CqsSchedRel cqs_sched_to_target cqs_sched_to_source cqs_sched_canonical cqs_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cqs_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CqsSchedRel Job sR (cqs_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CqsSchedRel Job (cqs_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cqs_sched_canonical Job) (cqs_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CqsSchedRel Job sR sL.

Lemma cqs_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cqs_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cqs_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cqs_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cqs_US_scheduled_at j tR tL Ht)). Qed.

Lemma cqs_service_at_fun j : CqsFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cqs_US_service_at j kR kL Hk). Qed.

Lemma cqs_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cqs_ico _ _ _ _ _ _ H1 H2 (cqs_service_at_fun j)). Qed.

Lemma cqs_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cqs_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cqs_US_completed_by cR cL (Hc : CqsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cqs_US_service j tR tL Ht)). Qed.

Lemma cqs_US_pending aR aL (Ha : CqsParRel Job aR aL) cR cL (Hc : CqsParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cqs_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cqs_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cqs_US_pending_earlier_and_at aR aL (Ha : CqsParRel Job aR aL) cR cL (Hc : CqsParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending_earlier_and_at aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending_earlier_and_at Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cqs_arrived_before Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cqs_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cqs_US_sequential_jobs (Task : eqType) aR aL (Ha : CqsParRel Job aR aL) cR cL (Hc : CqsParRel Job cR cL)
    (job_task : Job -> Task) :
  PropSPropRel (UniprocessorSchedule.sequential_jobs aR cR sR job_task)
    (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_sequential_jobs Job dJ aL cL sL Task (ct_decidable_eq Task) job_task).
Proof.
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_eq Task (job_task j1) (job_task j2))).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha j1) (Ha j2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqs_US_scheduled_at j2 tR tL Ht)).
  exact (ct_bool_truth _ _ (cqs_US_completed_by cR cL Hc j1 tR tL Ht)).
Qed.

Lemma cqs_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CqsArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqs_US_scheduled_at j tR tL Ht)).
  exact (cqs_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cqs_US_jobs_must_arrive_to_execute aR aL (Ha : CqsParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqs_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cqs_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma cqs_US_completed_jobs_dont_execute cR cL (Hc : CqsParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cqs_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cqs_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicAbstractSeqRtaInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicAbstractSeqRtaInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cqs_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cqs_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cqs_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicAbstractSeqRtaInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicAbstractSeqRtaInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicAbstractSeqRtaInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cqs_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cqs_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CqsPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma cqs_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CqsPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cqs_forall_cover _ _ (CqsPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CqsRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cqs_rel_canonical (T : Type) (rR : T -> T -> bool) : CqsRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cqs_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CqsRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cqs_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CqsRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cqs_forall_cover _ _ (CqsRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cqs_rel_canonical T) (cqs_rel_surjective T) PR PL).
Qed.

Definition CqsJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CqsRelRel T (rR tR) (rL tL).

Lemma cqs_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CqsJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cqs_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CqsJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cqs_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CqsJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cqs_forall_cover _ _ (CqsJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cqs_jldp_canonical T) (cqs_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

End PriodefsDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cqs_J_job_cost_positive cR cL (Hc : CqsParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

Lemma cqs_J_job_cost_le_task_cost tcR tcL (Htc : CqsParRel Task tcR tcL) cR cL (Hc : CqsParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

Lemma cqs_J_cost_of_jobs_from_arrival_sequence_le_task_cost tcR tcL (Htc : CqsParRel Task tcR tcL)
    cR cL (Hc : CqsParRel Job cR cL) (job_task : Job -> Task) aR aL (Ha : CqsArrRel Job aR aL) :
  PropSPropRel (Job.cost_of_jobs_from_arrival_sequence_le_task_cost tcR cR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_cost_of_jobs_from_arrival_sequence_le_task_cost Task dT tcL Job dJ cL job_task aL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp.
  - apply: ct_exists_nat => tR tL Ht. exact (cqs_mem Job j _ _ (Ha tR tL Ht)).
  - exact (ct_bool_truth _ _ (cqs_J_job_cost_le_task_cost tcR tcL Htc cR cL Hc job_task j)).
Qed.

End JobDefs.

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cqs_TA_is_job_of_task (job_task : Job -> Task) tsk j :
  CtBoolRel (TaskArrival.is_job_of_task job_task tsk j)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk j).
Proof. exact (ct_decide_eq Task (job_task j) tsk). Qed.

Lemma cqs_TA_arrivals_of_task_between (job_task : Job -> Task) aR aL (Ha : CqsArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_between Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans (cl_filter cid _ (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk)
                            (cqs_TA_is_job_of_task job_task tsk) _) _).
  exact (f_equal (I.List_filter Job (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk))
           (Logic.eq_sym (cl_list_logic _ _ _ (cqs_jobs_arrived_between Job aR aL Ha _ _ _ _ H1 H2)))).
Qed.

Lemma cqs_TA_arrivals_of_task_before (job_task : Job -> Task) aR aL (Ha : CqsArrRel Job aR aL) tsk
    tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (TaskArrival.arrivals_of_task_before job_task aR tsk tR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_before Task Job dT dJ job_task aL tsk tL).
Proof. exact (cqs_TA_arrivals_of_task_between job_task aR aL Ha tsk 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma cqs_TA_num_arrivals_of_task (job_task : Job -> Task) aR aL (Ha : CqsArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (TaskArrival.num_arrivals_of_task job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_num_arrivals_of_task Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  have H := cqs_TA_arrivals_of_task_between job_task aR aL Ha tsk _ _ _ _ H1 H2.
  change (SubNatRel (size (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R))
    (I.List_length Job (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_between Task Job dT dJ job_task aL tsk t1L t2L))).
  exact (match H in Lean.eq _ z
               return SubNatRel (size (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R)) (I.List_length Job z) with
         | Lean.eq_refl => cl_size cid _
         end).
Qed.

End TaskArrivalDefs.

Section AcboundsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

(** Curves [Task -> nat -> nat] pointwise on related arguments. *)
Definition CqsCurveRel (fR : Task -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk nR nL, SubNatRel nR nL -> SubNatRel (fR tsk nR) (fL tsk nL).

Notation NA := (cqs_TA_num_arrivals_of_task Task Job).

Lemma cqs_AC_is_arrival_bound (job_task : Job -> Task) aR aL (Ha : CqsArrRel Job aR aL)
    mR mL (Hm : CqsCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.is_arrival_bound job_task aR mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_is_arrival_bound Task dT Job dJ job_task aL mL tsk).
Proof.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 H2).
  exact (sub_nat_le_correspondence _ _ _ _ (NA job_task aR aL Ha tsk _ _ _ _ H1 H2) (Hm tsk _ _ (ct_sub_rel _ _ _ _ H2 H1))).
Qed.

Lemma cqs_AC_zero_arrival_curve mR mL (Hm : CqsCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.zero_arrival_curve mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_zero_arrival_curve Task dT mL tsk).
Proof. exact (sub_nat_eq_correspondence _ _ _ _ (Hm tsk _ _ (sub_nat_rel_canonical 0)) (sub_nat_rel_canonical 0)). Qed.

Lemma cqs_AC_monotonic_arrival_curve mR mL (Hm : CqsCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.monotonic_arrival_curve mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_monotonic_arrival_curve Task dT mL tsk).
Proof.
  apply: ct_forall_nat => xR xL Hx. apply: ct_forall_nat => yR yL Hy.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ Hx Hy)).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hm tsk _ _ Hx) (Hm tsk _ _ Hy))).
Qed.

Lemma cqs_AC_proper_arrival_curve (job_task : Job -> Task) aR aL (Ha : CqsArrRel Job aR aL)
    mR mL (Hm : CqsCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.proper_arrival_curve job_task aR mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_proper_arrival_curve Task dT Job dJ job_task aL mL tsk).
Proof.
  apply: ct_and; first exact (cqs_AC_is_arrival_bound job_task aR aL Ha mR mL Hm tsk).
  apply: ct_and; first exact (cqs_AC_zero_arrival_curve mR mL Hm tsk).
  exact (cqs_AC_monotonic_arrival_curve mR mL Hm tsk).
Qed.

Lemma cqs_AC_family_of_proper_arrival_curves (job_task : Job -> Task) aR aL (Ha : CqsArrRel Job aR aL)
    mR mL (Hm : CqsCurveRel mR mL) tsR tsL (Hts : ClListRel cid tsR tsL) :
  PropSPropRel (ArrivalCurves.family_of_proper_arrival_curves job_task aR mR tsR)
    (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_family_of_proper_arrival_curves Task dT Job dJ job_task aL mL tsL).
Proof.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cqs_mem Task tsk _ _ Hts).
  exact (cqs_AC_proper_arrival_curve job_task aR aL Ha mR mL Hm tsk).
Qed.

End AcboundsDefs.

(** * Arrival curves [Task -> time -> nat], with two-way totals *)

Lemma cqs_curve_canonical (Task : eqType) mR : CqsCurveRel Task mR (fun tsk nL => sub_nat_to_imported (mR tsk (sub_nat_to_rocq nL))).
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma cqs_curve_surjective (Task : eqType) mL : CqsCurveRel Task (fun tsk nR => sub_nat_to_rocq (mL tsk (sub_nat_to_imported nR))) mL.
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. exact (sub_nat_rel_surjective _). Qed.

Lemma cqs_forall_curve (Task : eqType) (PR : (Task -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall mR mL, CqsCurveRel Task mR mL -> PropSPropRel (PR mR) (PL mL)) -> PropSPropRel (forall m, PR m) (forall m, PL m).
Proof. exact (cqs_forall_cover _ _ (CqsCurveRel Task) _ _ (cqs_curve_canonical Task) (cqs_curve_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section AcwbDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat).
Hypothesis Htc : CqsParRel Task tcR tcL.
Variables (mR : Task -> nat -> nat) (mL : Task -> Lean.Nat -> Lean.Nat).
Hypothesis Hm : CqsCurveRel Task mR mL.

Lemma cqs_WB_task_request_bound_function tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.task_request_bound_function tcR mR tsk dR) (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_task_request_bound_function Task dT tcL mL tsk dL).
Proof. exact (sub_mul_correspondence _ _ _ _ (Htc tsk) (Hm tsk _ _ Hd)). Qed.

Notation TRBF := cqs_WB_task_request_bound_function.

End AcwbDefs.

Section UwlDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cqs_WL_workload_of_jobs cR cL (Hc : CqsParRel Job cR cL) jobsR jobsL (Hj : ClListRel cid jobsR jobsL)
    pR pL (Hp : CqsPredRel Job pR pL) :
  SubNatRel (Workload.workload_of_jobs cR jobsR pR) (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_workload_of_jobs Job dJ cL jobsL pL).
Proof. exact (cqs_sum_filtered_rel Job cR cL Hc pR pL Hp _ _ Hj). Qed.

Lemma cqs_WL_task_workload cR cL (Hc : CqsParRel Job cR cL) (job_task : Job -> Task) tsk
    jobsR jobsL (Hj : ClListRel cid jobsR jobsL) :
  SubNatRel (Workload.task_workload cR job_task tsk jobsR) (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_task_workload Task dT Job dJ cL job_task tsk jobsL).
Proof. exact (cqs_WL_workload_of_jobs cR cL Hc jobsR jobsL Hj _ _ (fun j => ct_decide_eq Task (job_task j) tsk)). Qed.

Lemma cqs_WL_task_workload_between cR cL (Hc : CqsParRel Job cR cL) (job_task : Job -> Task)
    arrR arrL (Harr : CqsArrRel Job arrR arrL) tsk t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Workload.task_workload_between cR job_task arrR tsk t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_task_workload_between Task dT Job dJ cL job_task arrL tsk t1L t2L).
Proof. exact (cqs_WL_task_workload cR cL Hc job_task tsk _ _ (cqs_jobs_arrived_between Job arrR arrL Harr _ _ _ _ H1 H2)). Qed.

End UwlDefs.

Section UrtDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CqsSchedRel Job sR sL.

Lemma cqs_RT_is_response_time_bound_of_job aR aL (Ha : CqsParRel Job aR aL) cR cL (Hc : CqsParRel Job cR cL)
    j rR rL (Hr : SubNatRel rR rL) :
  CtBoolRel (ResponseTime.is_response_time_bound_of_job aR cR sR j rR) (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_job Job dJ aL cL sL j rL).
Proof. exact (cqs_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr)). Qed.

Lemma cqs_RT_is_response_time_bound_of_task aR aL (Ha : CqsParRel Job aR aL) cR cL (Hc : CqsParRel Job cR cL)
    (job_task : Job -> Task) arrR arrL (Harr : CqsArrRel Job arrR arrL) tsk rR rL (Hr : SubNatRel rR rL) :
  PropSPropRel (ResponseTime.is_response_time_bound_of_task aR cR job_task arrR sR tsk rR)
    (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_task Task dT Job dJ aL cL job_task arrL sL tsk rL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (cqs_RT_is_response_time_bound_of_job aR aL Ha cR cL Hc j rR rL Hr)).
Qed.

End UrtDefs.

Lemma cqs_iff (P Q : Prop) (PL QL : SProp) :
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
(** * Relations *)

Lemma cqs_eq_transport (T : Type) (a b : T) aL bL : Lean.eq a aL -> Lean.eq b bL ->
  PropSPropRel (Logic.eq a b) (Lean.eq aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (ct_eq_rel T a b). Qed.

(** Functions [nat -> T] (identical values) and [nat -> nat] (values by [SubNatRel]), pointwise on related arguments. *)
Definition CqsRsFunRel (T : Type) (fR : nat -> T) (fL : Lean.Nat -> T) : SProp :=
  forall nR nL, SubNatRel nR nL -> Lean.eq (fR nR) (fL nL).
Definition CqsNatFunRel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) : SProp :=
  forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

(** Interference bound functions [Task -> time -> time -> time], pointwise on related arguments and values. *)
Definition CqsIbfRel (Task : Type) (fR : Task -> nat -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk, forall aR aL, SubNatRel aR aL -> CqsNatFunRel (fR tsk aR) (fL tsk aL).

Definition cqs_ibf_to_target (Task : Type) (fR : Task -> nat -> nat -> nat) : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat :=
  fun tsk aL xL => sub_nat_to_imported (fR tsk (sub_nat_to_rocq aL) (sub_nat_to_rocq xL)).
Definition cqs_ibf_to_source (Task : Type) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : Task -> nat -> nat -> nat :=
  fun tsk aR xR => sub_nat_to_rocq (fL tsk (sub_nat_to_imported aR) (sub_nat_to_imported xR)).

Lemma cqs_ibf_canonical (Task : Type) fR : CqsIbfRel Task fR (cqs_ibf_to_target Task fR).
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  unfold cqs_ibf_to_target. rewrite !sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma cqs_ibf_surjective (Task : Type) fL : CqsIbfRel Task (cqs_ibf_to_source Task fL) fL.
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma cqs_forall_ibf (Task : Type) (PR : (Task -> nat -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, CqsIbfRel Task fR fL -> PropSPropRel (PR fR) (PL fL)) -> PropSPropRel (forall f, PR f) (forall f, PL f).
Proof. exact (cqs_forall_cover _ _ (CqsIbfRel Task) (cqs_ibf_to_target Task) (cqs_ibf_to_source Task) (cqs_ibf_canonical Task) (cqs_ibf_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cqs_RS_are_not_equivalent_at_values_less_than (T : eqType) f1R f1L (H1 : CqsRsFunRel T f1R f1L)
    f2R f2L (H2 : CqsRsFunRel T f2R f2L) BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (AbstractRTAReduction.are_not_equivalent_at_values_less_than f1R f2R BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_are_not_equivalent_at_values_less_than T (ct_decidable_eq T) f1L f2L BL).
Proof.
  apply: ct_exists_nat => xR xL Hx.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Hx HB).
  exact (ct_imp _ _ _ _ (cqs_eq_transport T _ _ _ _ (H1 xR xL Hx) (H2 xR xL Hx)) cqs_false_rel).
Qed.

Lemma cqs_not_equiv_nat f1R f1L (H1 : CqsNatFunRel f1R f1L) f2R f2L (H2 : CqsNatFunRel f2R f2L) BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (AbstractRTAReduction.are_not_equivalent_at_values_less_than f1R f2R BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_are_not_equivalent_at_values_less_than_inst1 Lean.Nat I.instDecidableEqNat f1L f2L BL).
Proof.
  apply: ct_exists_nat => xR xL Hx.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Hx HB).
  exact (ct_imp _ _ _ _ (sub_nat_eq_correspondence _ _ _ _ (H1 xR xL Hx) (H2 xR xL Hx)) cqs_false_rel).
Qed.

Lemma cqs_RS_is_in_search_space (Task : eqType) tsk BR BL (HB : SubNatRel BR BL)
    fR fL (Hf : CqsIbfRel Task fR fL) AR AL (HA : SubNatRel AR AL) :
  PropSPropRel (AbstractRTAReduction.is_in_search_space tsk BR fR AR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_is_in_search_space Task (ct_decidable_eq Task) tsk BL fL AL).
Proof.
  apply: ct_or; first exact (sub_nat_eq_correspondence _ _ _ _ HA (sub_nat_rel_canonical 0)).
  apply: ct_and.
  - exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) HA) (ct_decide_lt _ _ _ _ HA HB))).
  - exact (cqs_not_equiv_nat _ _ (Hf tsk _ _ (ct_sub_rel _ _ _ _ HA (sub_nat_rel_canonical 1))) _ _ (Hf tsk _ _ HA) _ _ HB).
Qed.

(* ------------------------------------------------------------------ *)
(** * Interference predicates and interfering workloads *)

Section ARDIRel.
Variable Job : eqType.

Definition CqsIntRel (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (iR j tR) (iL j tL).

Lemma cqs_int_canonical iR : CqsIntRel iR (fun j tL => ct_b2l (iR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cqs_int_surjective iL : CqsIntRel (fun j tR => ct_l2b (iL j (sub_nat_to_imported tR))) iL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cqs_forall_int (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall iR iL, CqsIntRel iR iL -> PropSPropRel (PR iR) (PL iL)) -> PropSPropRel (forall i, PR i) (forall i, PL i).
Proof. exact (cqs_forall_cover _ _ CqsIntRel _ _ cqs_int_canonical cqs_int_surjective PR PL). Qed.

Definition CqsWlRel (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (wR j tR) (wL j tL).

Lemma cqs_wl_canonical wR : CqsWlRel wR (fun j tL => sub_nat_to_imported (wR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma cqs_wl_surjective wL : CqsWlRel (fun j tR => sub_nat_to_rocq (wL j (sub_nat_to_imported tR))) wL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (sub_nat_rel_surjective _). Qed.

Lemma cqs_forall_wl (PR : (Job -> nat -> nat) -> Prop) (PL : (Job -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall wR wL, CqsWlRel wR wL -> PropSPropRel (PR wR) (PL wL)) -> PropSPropRel (forall w, PR w) (forall w, PL w).
Proof. exact (cqs_forall_cover _ _ CqsWlRel _ _ cqs_wl_canonical cqs_wl_surjective PR PL). Qed.

End ARDIRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section ARDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cqs_ARD_cumul_interference iR iL (Hi : CqsIntRel Job iR iL) j t1R t1L (H1 : SubNatRel t1R t1L)
    t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (AbstractRTADefinitions.cumul_interference iR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_cumul_interference Job dJ iL j t1L t2L).
Proof. exact (cqs_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (Hi j kR kL Hk))). Qed.

Lemma cqs_ARD_cumul_interfering_workload wR wL (Hw : CqsWlRel Job wR wL) j t1R t1L (H1 : SubNatRel t1R t1L)
    t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (AbstractRTADefinitions.cumul_interfering_workload wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_cumul_interfering_workload Job dJ wL j t1L t2L).
Proof. exact (cqs_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => Hw j kR kL Hk)). Qed.

Notation CI := cqs_ARD_cumul_interference.
Notation CW := cqs_ARD_cumul_interfering_workload.

Section ARDSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CqsSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CqsParRel Job aR aL) (Hc : CqsParRel Job cR cL).
Variables (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat).
Hypotheses (Hi : CqsIntRel Job iR iL) (Hw : CqsWlRel Job wR wL).

Lemma cqs_ARD_quiet_time j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (AbstractRTADefinitions.quiet_time aR cR sR iR wR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_quiet_time Job dJ aL cL sL iL wL j tL).
Proof.
  apply: ct_and.
  - exact (sub_nat_eq_correspondence _ _ _ _ (CI iR iL Hi j 0 _ (sub_nat_rel_canonical 0) tR tL Ht)
             (CW wR wL Hw j 0 _ (sub_nat_rel_canonical 0) tR tL Ht)).
  - exact (ct_bool_truth _ _ (ct_bool_not _ _ (cqs_US_pending_earlier_and_at Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht))).
Qed.

Lemma cqs_ARD_busy_interval_prefix j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (AbstractRTADefinitions.busy_interval_prefix aR cR sR iR wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_interval_prefix Job dJ aL cL sL iL wL j t1L t2L).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Ha j)) (ct_decide_lt _ _ _ _ (Ha j) H2))).
  apply: ct_and; first exact (cqs_ARD_quiet_time j t1R t1L H1).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  exact (ct_imp _ _ _ _ (cqs_ARD_quiet_time j tR tL Ht) cqs_false_rel).
Qed.

Lemma cqs_ARD_busy_interval j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (AbstractRTADefinitions.busy_interval aR cR sR iR wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_interval Job dJ aL cL sL iL wL j t1L t2L).
Proof.
  apply: ct_and; first exact (cqs_ARD_busy_interval_prefix j t1R t1L H1 t2R t2L H2).
  exact (cqs_ARD_quiet_time j t2R t2L H2).
Qed.

Notation BI := cqs_ARD_busy_interval.

Lemma cqs_ARD_work_conserving (job_task : Job -> Task) arrR arrL (Harr : CqsArrRel Job arrR arrL) tsk :
  PropSPropRel (AbstractRTADefinitions.work_conserving aR cR job_task arrR sR tsk iR wR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_work_conserving Task dT Job dJ aL cL job_task arrL sL tsk iL wL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  apply: ct_imp; first exact (BI j t1R t1L H1 t2R t2L H2).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: cqs_iff.
  - exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (Hi j tR tL Ht)) cqs_false_rel).
  - exact (ct_bool_truth _ _ (cqs_US_scheduled_at Job sR sL Hs j tR tL Ht)).
Qed.

Lemma cqs_ARD_busy_intervals_are_bounded_by (job_task : Job -> Task) arrR arrL (Harr : CqsArrRel Job arrR arrL)
    tsk LR LL (HL : SubNatRel LR LL) :
  PropSPropRel (AbstractRTADefinitions.busy_intervals_are_bounded_by aR cR job_task arrR sR tsk iR wR LR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_intervals_are_bounded_by Task dT Job dJ aL cL job_task arrL sL tsk iL wL LL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  apply: ct_exists_nat => t1R t1L H1. apply: ct_exists_nat => t2R t2L H2.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Ha j)) (ct_decide_lt _ _ _ _ (Ha j) H2))).
  apply: ct_and; first exact (sub_nat_le_correspondence _ _ _ _ H2 (sub_add_correspondence _ _ _ _ H1 HL)).
  exact (BI j t1R t1L H1 t2R t2L H2).
Qed.

End ARDSched.

End ARDDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Module LS := prosa.classic.model.schedule.uni.limited.schedule.

Section LSDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CqsParRel Job cR cL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CqsArrRel Job arrR arrL.
Variables (lR : Job -> nat) (lL : Job -> Lean.Nat).
Hypothesis Hl : CqsParRel Job lR lL.

Lemma cqs_LS_job_lock_in_service_positive :
  PropSPropRel (LS.job_lock_in_service_positive cR arrR lR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_lock_in_service_positive Job dJ cL arrL lL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqs_J_job_cost_positive Job cR cL Hc j)).
  exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hl j)).
Qed.

Lemma cqs_LS_job_lock_in_service_le_job_cost :
  PropSPropRel (LS.job_lock_in_service_le_job_cost cR arrR lR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_lock_in_service_le_job_cost Job dJ cL arrL lL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqs_J_job_cost_positive Job cR cL Hc j)).
  exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (Hc j)).
Qed.

Section LSSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CqsSchedRel Job sR sL.

Lemma cqs_LS_job_nonpreemptive_after_lock_in_service :
  PropSPropRel (LS.job_nonpreemptive_after_lock_in_service cR arrR sR lR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_nonpreemptive_after_lock_in_service Job dJ cL arrL sL lL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht Ht').
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (cqs_US_service Job sR sL Hs j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (cqs_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht'))).
  exact (ct_bool_truth _ _ (cqs_US_scheduled_at Job sR sL Hs j _ _ Ht')).
Qed.

Lemma cqs_LS_proper_job_lock_in_service :
  PropSPropRel (LS.proper_job_lock_in_service cR arrR sR lR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_proper_job_lock_in_service Job dJ cL arrL sL lL).
Proof.
  apply: ct_and; first exact cqs_LS_job_lock_in_service_positive.
  apply: ct_and; first exact cqs_LS_job_lock_in_service_le_job_cost.
  exact cqs_LS_job_nonpreemptive_after_lock_in_service.
Qed.

End LSSched.

Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat) (tlR : Task -> nat) (tlL : Task -> Lean.Nat).
Hypotheses (Htc : CqsParRel Task tcR tcL) (Htl : CqsParRel Task tlR tlL).

Lemma cqs_LS_task_lock_in_service_le_task_cost tsk :
  PropSPropRel (LS.task_lock_in_service_le_task_cost tcR tlR tsk) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_task_lock_in_service_le_task_cost Task dT tcL tlL tsk).
Proof. exact (sub_nat_le_correspondence _ _ _ _ (Htl tsk) (Htc tsk)). Qed.

Lemma cqs_LS_task_lock_in_service_bounds_job_lock_in_service (job_task : Job -> Task) tsk :
  PropSPropRel (LS.task_lock_in_service_bounds_job_lock_in_service job_task arrR lR tlR tsk)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_task_lock_in_service_bounds_job_lock_in_service Task dT Job dJ job_task arrL lL tlL tsk).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (Htl tsk)).
Qed.

Lemma cqs_LS_proper_task_lock_in_service (job_task : Job -> Task) tsk :
  PropSPropRel (LS.proper_task_lock_in_service tcR job_task arrR lR tlR tsk)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_proper_task_lock_in_service Task dT tcL Job dJ job_task arrL lL tlL tsk).
Proof.
  apply: ct_and; first exact (cqs_LS_task_lock_in_service_le_task_cost tsk).
  exact (cqs_LS_task_lock_in_service_bounds_job_lock_in_service job_task tsk).
Qed.

End LSDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section SVDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CqsSchedRel Job sR sL.

Lemma cqs_SV_service_of_jobs jobsR jobsL (Hj : ClListRel cid jobsR jobsL) pR pL (Hp : CqsPredRel Job pR pL)
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.service_of_jobs sR jobsR pR t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs Job dJ sL jobsL pL t1L t2L).
Proof.
  exact (cqs_sum_filtered_rel Job (fun j => UniprocessorSchedule.service_during sR j t1R t2R)
           (fun j => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L)
           (fun j => cqs_US_service_during Job sR sL Hs j _ _ H1 _ _ H2) pR pL Hp _ _ Hj).
Qed.

Lemma cqs_SV_task_service_of_jobs_received_in (Task : eqType) (job_task : Job -> Task)
    arrR arrL (Harr : CqsArrRel Job arrR arrL) tsk a1R a1L (Ha1 : SubNatRel a1R a1L) a2R a2L (Ha2 : SubNatRel a2R a2L)
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.task_service_of_jobs_received_in job_task arrR sR tsk a1R a2R t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_task_service_of_jobs_received_in Task (ct_decidable_eq Task) Job dJ job_task arrL sL tsk a1L a2L t1L t2L).
Proof.
  exact (cqs_SV_service_of_jobs _ _ (cqs_jobs_arrived_between Job arrR arrL Harr _ _ _ _ Ha1 Ha2)
           _ _ (fun j => ct_decide_eq Task (job_task j) tsk) _ _ H1 _ _ H2).
Qed.

Lemma cqs_SV_task_service_between (Task : eqType) (job_task : Job -> Task)
    arrR arrL (Harr : CqsArrRel Job arrR arrL) tsk t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.task_service_between job_task arrR sR tsk t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_task_service_between Task (ct_decidable_eq Task) Job dJ job_task arrL sL tsk t1L t2L).
Proof. exact (cqs_SV_task_service_of_jobs_received_in Task job_task arrR arrL Harr tsk _ _ H1 _ _ H2 _ _ H1 _ _ H2). Qed.

End SVDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section STDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CqsSchedRel Job sR sL.
Variable job_task : Job -> Task.

Lemma cqs_ST_task_scheduled_at tsk tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleOfTask.task_scheduled_at job_task sR tsk tR) (I.Prosa_Classic_Model_Schedule_Uni_ScheduleOfTask_ScheduleOfTask_task_scheduled_at Task dT Job dJ job_task sL tsk tL).
Proof.
  refine (cqs_trs (Hs tR tL Ht)
            (fun z => CtBoolRel (ScheduleOfTask.task_scheduled_at job_task sR tsk tR)
                        (match z with
                         | I.Option_some j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk)
                         | I.Option_none => I.Bool_false end)) _).
  rewrite /ScheduleOfTask.task_scheduled_at. destruct (sR tR) as [x|].
  - exact (ct_decide_eq Task (job_task x) tsk).
  - exact (ct_bool_canonical false).
Qed.

End STDefs.

(* ------------------------------------------------------------------ *)
(** * [has] against [List.any] *)

Lemma cqs_has_eq (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL x)) :
  forall s, Logic.eq (I.List_any T (cl_map cid s) pL) (ct_b2l (has pR s)).
Proof.
  elim => [|x s IH]; first reflexivity.
  have -> : Logic.eq (I.List_any T (cl_map cid (x :: s)) pL) (I.Bool_or (pL x) (I.List_any T (cl_map cid s) pL)).
  { cbn. destruct (pL x); reflexivity. }
  rewrite (ct_bool_rel_logic _ _ (Hp x)) IH /=. by case: (pR x); case: (has pR s).
Qed.

Lemma cqs_has (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL x)) :
  forall s, CtBoolRel (has pR s) (I.List_any T (cl_map cid s) pL).
Proof. intro s. exact (coq_eq_to_imported_eq _ _ (Logic.eq_sym (cqs_has_eq T pR pL Hp s))). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CqsSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CqsParRel Job aR aL) (Hc : CqsParRel Job cR cL).
Variable job_task : Job -> Task.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CqsArrRel Job arrR arrL.
Variables (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat).
Hypotheses (Hi : CqsIntRel Job iR iL) (Hw : CqsWlRel Job wR wL).
Notation BI := (cqs_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw).

Theorem AbstractSeqRTA_interference_and_workload_consistent_with_sequential_jobs_correspondence tsk :
  PropSPropRel (@AbstractSeqRTA.interference_and_workload_consistent_with_sequential_jobs Task Job aR cR job_task arrR sR tsk iR wR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_interference_and_workload_consistent_with_sequential_jobs Task dT Job dJ aL cL job_task arrL sL tsk iL wL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  apply: ct_imp; first exact (BI j t1R t1L H1 t2R t2L H2).
  exact (sub_nat_eq_correspondence _ _ _ _ (cqs_WL_task_workload_between Task Job cR cL Hc job_task arrR arrL Harr tsk _ _ (sub_nat_rel_canonical 0) _ _ H1)
           (cqs_SV_task_service_between Job sR sL Hs Task job_task arrR arrL Harr tsk _ _ (sub_nat_rel_canonical 0) _ _ H1)).
Qed.

Theorem AbstractSeqRTA_task_interference_received_before_correspondence tsk uR uL (Hu : SubNatRel uR uL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@AbstractSeqRTA.task_interference_received_before Task Job job_task arrR sR iR tsk uR tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_task_interference_received_before Task dT Job dJ job_task arrL sL iL tsk uL tL).
Proof.
  apply: ct_bool_and; first exact (ct_bool_not _ _ (cqs_ST_task_scheduled_at Task Job sR sL Hs job_task tsk tR tL Ht)).
  refine (cqs_trs (cqs_TA_arrivals_of_task_before Task Job job_task arrR arrL Harr tsk uR uL Hu)
            (fun z => CtBoolRel _ (I.List_any Job z (fun j => iL j tL))) _).
  exact (cqs_has Job _ _ (fun j => Hi j tR tL Ht) _).
Qed.

Theorem AbstractSeqRTA_cumul_task_interference_correspondence tsk uR uL (Hu : SubNatRel uR uL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (@AbstractSeqRTA.cumul_task_interference Task Job job_task arrR sR iR tsk uR t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_cumul_task_interference Task dT Job dJ job_task arrL sL iL tsk uL t1L t2L).
Proof.
  exact (cqs_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (AbstractSeqRTA_task_interference_received_before_correspondence tsk uR uL Hu kR kL Hk))).
Qed.

Theorem AbstractSeqRTA_task_interference_is_bounded_by_correspondence tsk fR fL (Hf : CqsIbfRel Task fR fL) :
  PropSPropRel (@AbstractSeqRTA.task_interference_is_bounded_by Task Job aR cR job_task arrR sR tsk iR wR fR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_task_interference_is_bounded_by Task dT Job dJ aL cL job_task arrL sL tsk iL wL fL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => RR RL HR.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  have H1R := sub_add_correspondence _ _ _ _ H1 HR.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ H1R H2).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (cqs_US_completed_by Job sR sL Hs cR cL Hc j _ _ H1R))).
  apply: ct_imp; first exact (BI j t1R t1L H1 t2R t2L H2).
  cbv zeta.
  exact (sub_nat_le_correspondence _ _ _ _ (AbstractSeqRTA_cumul_task_interference_correspondence tsk _ _ H2 _ _ H1 _ _ H1R)
           (Hf tsk _ _ (ct_sub_rel _ _ _ _ (Ha j) H1) _ _ HR)).
Qed.

End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_completed_before_beginning_of_busy_interval (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@AbstractSeqRTA.completed_before_beginning_of_busy_interval Task Job)).
Definition tgt_completed_before_beginning_of_busy_interval (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_completed_before_beginning_of_busy_interval Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem AbstractSeqRTA_completed_before_beginning_of_busy_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_completed_before_beginning_of_busy_interval Task Job) (tgt_completed_before_beginning_of_busy_interval Task Job).
Proof.
  unfold src_completed_before_beginning_of_busy_interval, tgt_completed_before_beginning_of_busy_interval.
  apply: cqs_forall_par => aR aL Ha. apply: cqs_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (cqs_forall_arr Job) => arrR arrL Harr.
  apply: ct_imp; first exact (cqs_consistent Job aR aL Ha arrR arrL Harr).
  apply: (cqs_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqs_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cqs_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk.
  apply: (cqs_forall_int Job) => iR iL Hi. apply: (cqs_forall_wl Job) => wR wL Hw.
  apply: ct_imp; first exact (AbstractSeqRTA_interference_and_workload_consistent_with_sequential_jobs_correspondence Task Job sR sL Hs aR aL cR cL Ha Hc job_task arrR arrL Harr iR iL wR wL Hi Hw tsk).
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j1).
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j2).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j1) tsk).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j2) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqs_J_job_cost_positive Job cR cL Hc j1)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cqs_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j1 _ _ H1 _ _ H2).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha j2) H1).
  exact (ct_bool_truth _ _ (cqs_US_completed_by Job sR sL Hs cR cL Hc j2 _ _ H1)).
Qed.

Definition src_arrives_after_beginning_of_busy_interval (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@AbstractSeqRTA.arrives_after_beginning_of_busy_interval Task Job)).
Definition tgt_arrives_after_beginning_of_busy_interval (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_arrives_after_beginning_of_busy_interval Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem AbstractSeqRTA_arrives_after_beginning_of_busy_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_arrives_after_beginning_of_busy_interval Task Job) (tgt_arrives_after_beginning_of_busy_interval Task Job).
Proof.
  unfold src_arrives_after_beginning_of_busy_interval, tgt_arrives_after_beginning_of_busy_interval.
  apply: cqs_forall_par => aR aL Ha. apply: cqs_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (cqs_forall_arr Job) => arrR arrL Harr.
  apply: ct_imp; first exact (cqs_consistent Job aR aL Ha arrR arrL Harr).
  apply: (cqs_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqs_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cqs_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk.
  apply: (cqs_forall_int Job) => iR iL Hi. apply: (cqs_forall_wl Job) => wR wL Hw.
  apply: ct_imp; first exact (AbstractSeqRTA_interference_and_workload_consistent_with_sequential_jobs_correspondence Task Job sR sL Hs aR aL cR cL Ha Hc job_task arrR arrL Harr iR iL wR wL Hi Hw tsk).
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j1).
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j2).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j1) tsk).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j2) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqs_J_job_cost_positive Job cR cL Hc j1)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cqs_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j1 _ _ H1 _ _ H2).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 Ht).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqs_US_pending Job sR sL Hs aR aL Ha cR cL Hc j2 tR tL Ht)).
  exact (ct_bool_truth _ _ (cqs_arrived_between Job aR aL Ha j2 _ _ _ _ H1 (cqs_succ_rel _ _ Ht))).
Qed.

Definition src_bound_for_cumulative_job_interference_actual (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@AbstractSeqRTA.bound_for_cumulative_job_interference_actual Task Job)).
Definition tgt_bound_for_cumulative_job_interference_actual (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_bound_for_cumulative_job_interference_actual Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem AbstractSeqRTA_bound_for_cumulative_job_interference_actual_correspondence (Task Job : eqType) :
  PropSPropRel (src_bound_for_cumulative_job_interference_actual Task Job) (tgt_bound_for_cumulative_job_interference_actual Task Job).
Proof.
  unfold src_bound_for_cumulative_job_interference_actual, tgt_bound_for_cumulative_job_interference_actual.
  apply: cqs_forall_par => aR aL Ha. apply: cqs_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (cqs_forall_arr Job) => arrR arrL Harr.
  apply: ct_imp; first exact (cqs_consistent Job aR aL Ha arrR arrL Harr).
  apply: (cqs_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqs_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_imp; first exact (cqs_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cqs_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => tsk.
  apply: (cqs_forall_int Job) => iR iL Hi. apply: (cqs_forall_wl Job) => wR wL Hw.
  apply: ct_imp; first exact (cqs_ARD_work_conserving Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk).
  apply: ct_imp; first exact (cqs_US_sequential_jobs Job sR sL Hs Task aR aL Ha cR cL Hc job_task).
  apply: ct_imp; first exact (AbstractSeqRTA_interference_and_workload_consistent_with_sequential_jobs_correspondence Task Job sR sL Hs aR aL cR cL Ha Hc job_task arrR arrL Harr iR iL wR wL Hi Hw tsk).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqs_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cqs_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2).
  apply: ct_forall_nat => xR xL Hx.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ H1 Hx) H2).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (cqs_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ H1 Hx)))).
  exact (sub_nat_le_correspondence _ _ _ _ (cqs_ARD_cumul_interference Job iR iL Hi j _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hx)) (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (cqs_WL_task_workload_between Task Job cR cL Hc job_task arrR arrL Harr tsk _ _ H1 _ _ (sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ H1 (ct_sub_rel _ _ _ _ (Ha j) H1)) (sub_nat_rel_canonical 1))) (Hc j)) (AbstractSeqRTA_cumul_task_interference_correspondence Task Job sR sL Hs job_task arrR arrL Harr iR iL Hi tsk _ _ H2 _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hx)))).
Qed.

Definition src_task_rbf_excl_tsk_bounds_task_workload_excl_j (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time,
    ltac:(type_of_term (@AbstractSeqRTA.task_rbf_excl_tsk_bounds_task_workload_excl_j Task task_cost Job)).
Definition tgt_task_rbf_excl_tsk_bounds_task_workload_excl_j (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_task_rbf_excl_tsk_bounds_task_workload_excl_j Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).
Theorem AbstractSeqRTA_task_rbf_excl_tsk_bounds_task_workload_excl_j_correspondence (Task Job : eqType) :
  PropSPropRel (src_task_rbf_excl_tsk_bounds_task_workload_excl_j Task Job) (tgt_task_rbf_excl_tsk_bounds_task_workload_excl_j Task Job).
Proof.
  unfold src_task_rbf_excl_tsk_bounds_task_workload_excl_j, tgt_task_rbf_excl_tsk_bounds_task_workload_excl_j.
  apply: cqs_forall_par => tcR tcL Htc.
  apply: cqs_forall_par => aR aL Ha. apply: cqs_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (cqs_forall_arr Job) => arrR arrL Harr.
  apply: ct_imp; first exact (cqs_consistent Job aR aL Ha arrR arrL Harr).
  apply: (cqs_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqs_J_cost_of_jobs_from_arrival_sequence_le_task_cost Task Job tcR tcL Htc cR cL Hc job_task arrR arrL Harr).
  apply: (cqs_forall_list Task) => tsR tsL Hts.
  apply: (cqs_forall_curve Task) => mR mL Hm.
  apply: ct_imp; first exact (cqs_AC_family_of_proper_arrival_curves Task Job job_task arrR arrL Harr mR mL Hm tsR tsL Hts).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cqs_mem Task tsk _ _ Hts).
  apply: (cqs_forall_int Job) => iR iL Hi. apply: (cqs_forall_wl Job) => wR wL Hw.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqs_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cqs_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2).
  exact (sub_nat_le_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (cqs_WL_task_workload_between Task Job cR cL Hc job_task arrR arrL Harr tsk _ _ H1 _ _ (sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ H1 (ct_sub_rel _ _ _ _ (Ha j) H1)) (sub_nat_rel_canonical 1))) (Hc j)) (ct_sub_rel _ _ _ _ (cqs_WB_task_request_bound_function Task tcR tcL Htc mR mL Hm tsk _ _ (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (Ha j) H1) (sub_nat_rel_canonical 1))) (Htc tsk))).
Qed.

Definition src_bound_for_cumulative_job_interference (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time,
    ltac:(type_of_term (@AbstractSeqRTA.bound_for_cumulative_job_interference Task task_cost Job)).
Definition tgt_bound_for_cumulative_job_interference (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_bound_for_cumulative_job_interference Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).
Theorem AbstractSeqRTA_bound_for_cumulative_job_interference_correspondence (Task Job : eqType) :
  PropSPropRel (src_bound_for_cumulative_job_interference Task Job) (tgt_bound_for_cumulative_job_interference Task Job).
Proof.
  unfold src_bound_for_cumulative_job_interference, tgt_bound_for_cumulative_job_interference.
  apply: cqs_forall_par => tcR tcL Htc.
  apply: cqs_forall_par => aR aL Ha. apply: cqs_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (cqs_forall_arr Job) => arrR arrL Harr.
  apply: ct_imp; first exact (cqs_consistent Job aR aL Ha arrR arrL Harr).
  apply: (cqs_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqs_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_imp; first exact (cqs_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cqs_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cqs_J_cost_of_jobs_from_arrival_sequence_le_task_cost Task Job tcR tcL Htc cR cL Hc job_task arrR arrL Harr).
  apply: (cqs_forall_list Task) => tsR tsL Hts.
  apply: (cqs_forall_curve Task) => mR mL Hm.
  apply: ct_imp; first exact (cqs_AC_family_of_proper_arrival_curves Task Job job_task arrR arrL Harr mR mL Hm tsR tsL Hts).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cqs_mem Task tsk _ _ Hts).
  apply: (cqs_forall_int Job) => iR iL Hi. apply: (cqs_forall_wl Job) => wR wL Hw.
  apply: ct_imp; first exact (cqs_ARD_work_conserving Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk).
  apply: ct_imp; first exact (cqs_US_sequential_jobs Job sR sL Hs Task aR aL Ha cR cL Hc job_task).
  apply: ct_imp; first exact (AbstractSeqRTA_interference_and_workload_consistent_with_sequential_jobs_correspondence Task Job sR sL Hs aR aL cR cL Ha Hc job_task arrR arrL Harr iR iL wR wL Hi Hw tsk).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cqs_J_job_cost_positive Job cR cL Hc j)).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cqs_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw j _ _ H1 _ _ H2).
  apply: ct_forall_nat => xR xL Hx.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ H1 Hx) H2).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (cqs_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ H1 Hx)))).
  exact (sub_nat_le_correspondence _ _ _ _ (cqs_ARD_cumul_interference Job iR iL Hi j _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hx)) (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (cqs_WB_task_request_bound_function Task tcR tcL Htc mR mL Hm tsk _ _ (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (Ha j) H1) (sub_nat_rel_canonical 1))) (Htc tsk)) (AbstractSeqRTA_cumul_task_interference_correspondence Task Job sR sL Hs job_task arrR arrL Harr iR iL Hi tsk _ _ H2 _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hx)))).
Qed.

Definition src_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time,
    ltac:(type_of_term (@AbstractSeqRTA.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis Task task_cost Job)).
Definition tgt_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).
Theorem AbstractSeqRTA_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis_correspondence (Task Job : eqType) :
  PropSPropRel (src_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis Task Job) (tgt_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis Task Job).
Proof.
  unfold src_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis, tgt_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis.
  apply: cqs_forall_par => tcR tcL Htc.
  apply: cqs_forall_par => aR aL Ha. apply: cqs_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (cqs_forall_arr Job) => arrR arrL Harr.
  apply: ct_imp; first exact (cqs_consistent Job aR aL Ha arrR arrL Harr).
  apply: (cqs_forall_sched Job) => sR sL Hs.
  apply: (cqs_forall_list Task) => tsR tsL Hts.
  apply: (cqs_forall_curve Task) => mR mL Hm.
  apply: ct_imp; first exact (cqs_AC_family_of_proper_arrival_curves Task Job job_task arrR arrL Harr mR mL Hm tsR tsL Hts).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cqs_mem Task tsk _ _ Hts).
  apply: cqs_forall_par => lR lL Hl. apply: cqs_forall_par => tlR tlL Htl.
  apply: ct_imp; first exact (cqs_LS_proper_job_lock_in_service Job cR cL Hc arrR arrL Harr lR lL Hl sR sL Hs).
  apply: ct_imp; first exact (cqs_LS_proper_task_lock_in_service Task Job arrR arrL Harr lR lL Hl tcR tcL tlR tlL Htc Htl job_task tsk).
  apply: ct_forall_nat => LR LL HL.
  apply: (cqs_forall_ibf Task) => fR fL Hf.
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp.
  { apply: ct_forall_nat => AR AL HA.
    apply: ct_imp; first exact (cqs_RS_is_in_search_space Task tsk _ _ HL _ _ (fun tsk0 aR' aL' Ha' xR xL Hx => sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (cqs_WB_task_request_bound_function Task tcR tcL Htc mR mL Hm tsk _ _ (sub_add_correspondence _ _ _ _ Ha' (sub_nat_rel_canonical 1))) (Htc tsk0)) (Hf tsk0 aR' aL' Ha' xR xL Hx)) _ _ HA).
    apply: ct_exists_nat => FR FL HF.
    apply: ct_and; first exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HA HF) (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (cqs_WB_task_request_bound_function Task tcR tcL Htc mR mL Hm tsk _ _ (sub_add_correspondence _ _ _ _ HA (sub_nat_rel_canonical 1))) (ct_sub_rel _ _ _ _ (Htc tsk) (Htl tsk))) (Hf tsk _ _ HA _ _ (sub_add_correspondence _ _ _ _ HA HF)))).
    exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HF (ct_sub_rel _ _ _ _ (Htc tsk) (Htl tsk))) HR). }
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cqs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_forall_nat => AR AL HA.
  apply: ct_imp; first exact (cqs_RS_is_in_search_space Task tsk _ _ HL _ _ (fun tsk0 aR' aL' Ha' xR xL Hx => sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (cqs_WB_task_request_bound_function Task tcR tcL Htc mR mL Hm tsk _ _ (sub_add_correspondence _ _ _ _ Ha' (sub_nat_rel_canonical 1))) (Htc tsk0)) (Hf tsk0 aR' aL' Ha' xR xL Hx)) _ _ HA).
  apply: ct_exists_nat => FR FL HF.
  apply: ct_and; first exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HA HF) (sub_add_correspondence _ _ _ _ (Htl tsk) (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (cqs_WB_task_request_bound_function Task tcR tcL Htc mR mL Hm tsk _ _ (sub_add_correspondence _ _ _ _ HA (sub_nat_rel_canonical 1))) (Htc tsk)) (Hf tsk _ _ HA _ _ (sub_add_correspondence _ _ _ _ HA HF))))).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HF (ct_sub_rel _ _ _ _ (Htc tsk) (Htl tsk))) HR).
Qed.

Definition src_uniprocessor_response_time_bound_seq (Task Job : eqType) : Prop :=
  forall task_cost : Task -> Time.time,
    ltac:(type_of_term (@AbstractSeqRTA.uniprocessor_response_time_bound_seq Task task_cost Job)).
Definition tgt_uniprocessor_response_time_bound_seq (Task Job : eqType) : SProp :=
  forall task_cost : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_uniprocessor_response_time_bound_seq Task (ct_decidable_eq Task) task_cost Job (ct_decidable_eq Job))).
Theorem AbstractSeqRTA_uniprocessor_response_time_bound_seq_correspondence (Task Job : eqType) :
  PropSPropRel (src_uniprocessor_response_time_bound_seq Task Job) (tgt_uniprocessor_response_time_bound_seq Task Job).
Proof.
  unfold src_uniprocessor_response_time_bound_seq, tgt_uniprocessor_response_time_bound_seq.
  apply: cqs_forall_par => tcR tcL Htc.
  apply: cqs_forall_par => aR aL Ha. apply: cqs_forall_par => cR cL Hc. apply: ct_forall_identity => job_task.
  apply: (cqs_forall_arr Job) => arrR arrL Harr.
  apply: ct_imp; first exact (cqs_consistent Job aR aL Ha arrR arrL Harr).
  apply: (cqs_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cqs_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_imp; first exact (cqs_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cqs_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cqs_J_cost_of_jobs_from_arrival_sequence_le_task_cost Task Job tcR tcL Htc cR cL Hc job_task arrR arrL Harr).
  apply: (cqs_forall_list Task) => tsR tsL Hts.
  apply: (cqs_forall_curve Task) => mR mL Hm.
  apply: ct_imp; first exact (cqs_AC_family_of_proper_arrival_curves Task Job job_task arrR arrL Harr mR mL Hm tsR tsL Hts).
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cqs_mem Task tsk _ _ Hts).
  apply: cqs_forall_par => lR lL Hl. apply: cqs_forall_par => tlR tlL Htl.
  apply: ct_imp; first exact (cqs_LS_proper_job_lock_in_service Job cR cL Hc arrR arrL Harr lR lL Hl sR sL Hs).
  apply: ct_imp; first exact (cqs_LS_proper_task_lock_in_service Task Job arrR arrL Harr lR lL Hl tcR tcL tlR tlL Htc Htl job_task tsk).
  apply: (cqs_forall_int Job) => iR iL Hi. apply: (cqs_forall_wl Job) => wR wL Hw.
  apply: ct_imp; first exact (cqs_ARD_work_conserving Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk).
  apply: ct_imp; first exact (cqs_US_sequential_jobs Job sR sL Hs Task aR aL Ha cR cL Hc job_task).
  apply: ct_imp; first exact (AbstractSeqRTA_interference_and_workload_consistent_with_sequential_jobs_correspondence Task Job sR sL Hs aR aL cR cL Ha Hc job_task arrR arrL Harr iR iL wR wL Hi Hw tsk).
  apply: ct_forall_nat => LR LL HL.
  apply: ct_imp; first exact (cqs_ARD_busy_intervals_are_bounded_by Task Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw job_task arrR arrL Harr tsk LR LL HL).
  apply: (cqs_forall_ibf Task) => fR fL Hf.
  apply: ct_imp; first exact (AbstractSeqRTA_task_interference_is_bounded_by_correspondence Task Job sR sL Hs aR aL cR cL Ha Hc job_task arrR arrL Harr iR iL wR wL Hi Hw tsk fR fL Hf).
  apply: ct_forall_nat => RR RL HR.
  apply: ct_imp.
  { apply: ct_forall_nat => AR AL HA.
    apply: ct_imp; first exact (cqs_RS_is_in_search_space Task tsk _ _ HL _ _ (fun tsk0 aR' aL' Ha' xR xL Hx => sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (cqs_WB_task_request_bound_function Task tcR tcL Htc mR mL Hm tsk _ _ (sub_add_correspondence _ _ _ _ Ha' (sub_nat_rel_canonical 1))) (Htc tsk0)) (Hf tsk0 aR' aL' Ha' xR xL Hx)) _ _ HA).
    apply: ct_exists_nat => FR FL HF.
    apply: ct_and; first exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HA HF) (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (cqs_WB_task_request_bound_function Task tcR tcL Htc mR mL Hm tsk _ _ (sub_add_correspondence _ _ _ _ HA (sub_nat_rel_canonical 1))) (ct_sub_rel _ _ _ _ (Htc tsk) (Htl tsk))) (Hf tsk _ _ HA _ _ (sub_add_correspondence _ _ _ _ HA HF)))).
    exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HF (ct_sub_rel _ _ _ _ (Htc tsk) (Htl tsk))) HR). }
  exact (cqs_RT_is_response_time_bound_of_task Task Job sR sL Hs aR aL Ha cR cL Hc job_task arrR arrL Harr tsk RR RL HR).
Qed.
