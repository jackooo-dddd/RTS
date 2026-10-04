From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.service classic.model.schedule.uni.workload classic.model.schedule.uni.schedule_of_task classic.model.schedule.uni.limited.busy_interval classic.model.schedule.uni.limited.abstract_RTA.definitions classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta classic.model.schedule.uni.limited.jlfp_instantiation classic.model.schedule.uni.basic.platform classic.model.priority classic.model.schedule.uni.response_time classic.model.schedule.uni.limited.platform.definitions classic.model.schedule.uni.limited.schedule classic.model.schedule.uni.limited.rbf classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space classic.model.arrival.curves.bounds classic.analysis.uni.arrival_curves.workload_bound classic.model.schedule.uni.limited.edf.nonpr_reg.response_time_bound classic.model.schedule.uni.limited.platform.priority_inversion_is_bounded classic.model.schedule.uni.limited.edf.response_time_bound classic.model.schedule.uni.nonpreemptive.schedule classic.model.schedule.uni.limited.platform.limited classic.model.schedule.uni.limited.platform.preemptive classic.model.schedule.uni.limited.platform.nonpreemptive classic.model.schedule.uni.limited.edf.nonpr_reg.concrete_models.response_time_bound.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicConcreteEdfRta.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicConcreteEdfRtaBase ClassicConcreteEdfRtaList ClassicConcreteEdfRtaList1.



Module I := ImportedClassicConcreteEdfRta.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/edf/nonpr_reg/concrete_models/response_time_bound.v] (ProsaBuddy classic, commit f692cb7).

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

Lemma cce_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cce_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cce_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cce_false_rel). Qed.

Lemma cce_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cce_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cce_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cce_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cce_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cce_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cce_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cce_unmap_rel T l) PR PL).
Qed.

Definition CceParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cce_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CceParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cce_forall_cover _ _ (CceParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cce_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cce_natl s') end.

Definition cce_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cce_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cce_one) (cce_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cce_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cce_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cce_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cce_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cce_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cce_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cce_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cce_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cce_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cce_cl_append. reflexivity.
Qed.

Lemma cce_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CceFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cce_bigcat_rel (A : Type) fR fL (Hf : CceFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cce_iota_range (nR - mR) 0) cce_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cce_cl_map_ext _ _ Hpt) (cce_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cce_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cce_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CceArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cce_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cce_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cce_arr_canonical aR : CceArrRel aR (cce_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cce_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cce_arr_surjective aL : CceArrRel (cce_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cce_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CceArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cce_forall_cover _ _ CceArrRel cce_arr_to_target cce_arr_to_source cce_arr_canonical cce_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cce_jobs_arrived_between aR aL (Ha : CceArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cce_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cce_arrives_in aR aL (Ha : CceArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cce_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cce_consistent pR pL (Hp : CceParRel Job pR pL) aR aL (Ha : CceArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cce_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cce_is_a_set aR aL (Ha : CceArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cce_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cce_arrives_at aR aL (Ha : CceArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cce_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma cce_has_arrived pR pL (Hp : CceParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cce_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cce_snatl s') end.

Lemma cce_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cce_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cce_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cce_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cce_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cce_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cce_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CceFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cce_fun_canonical FR FL (HF : CceFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cce_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cce_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CceFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cce_nat_sub_canonical nR mR.
  rewrite cce_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cce_foldr_add FL FR (cce_fun_canonical FR FL HF)).
  by rewrite cce_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cce_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cce_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cce_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cce_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cce_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CceSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cce_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cce_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cce_sched_canonical sR : CceSchedRel sR (cce_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cce_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cce_sched_surjective sL : CceSchedRel (cce_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cce_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cce_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CceSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cce_forall_cover _ _ CceSchedRel cce_sched_to_target cce_sched_to_source cce_sched_canonical cce_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cce_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CceSchedRel Job sR (cce_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CceSchedRel Job (cce_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cce_sched_canonical Job) (cce_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.

Lemma cce_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cce_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cce_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cce_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cce_US_scheduled_at j tR tL Ht)). Qed.

Lemma cce_service_at_fun j : CceFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cce_US_service_at j kR kL Hk). Qed.

Lemma cce_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cce_ico _ _ _ _ _ _ H1 H2 (cce_service_at_fun j)). Qed.

Lemma cce_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cce_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cce_US_completed_by cR cL (Hc : CceParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cce_US_service j tR tL Ht)). Qed.

Lemma cce_US_pending aR aL (Ha : CceParRel Job aR aL) cR cL (Hc : CceParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cce_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cce_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cce_US_backlogged aR aL (Ha : CceParRel Job aR aL) cR cL (Hc : CceParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.backlogged aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_backlogged Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cce_US_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (cce_US_scheduled_at j tR tL Ht))).
Qed.

Lemma cce_US_sequential_jobs (Task : eqType) aR aL (Ha : CceParRel Job aR aL) cR cL (Hc : CceParRel Job cR cL)
    (job_task : Job -> Task) :
  PropSPropRel (UniprocessorSchedule.sequential_jobs aR cR sR job_task)
    (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_sequential_jobs Job dJ aL cL sL Task (ct_decidable_eq Task) job_task).
Proof.
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_eq Task (job_task j1) (job_task j2))).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha j1) (Ha j2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cce_US_scheduled_at j2 tR tL Ht)).
  exact (ct_bool_truth _ _ (cce_US_completed_by cR cL Hc j1 tR tL Ht)).
Qed.

Lemma cce_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CceArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cce_US_scheduled_at j tR tL Ht)).
  exact (cce_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cce_US_jobs_must_arrive_to_execute aR aL (Ha : CceParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cce_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cce_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma cce_US_completed_jobs_dont_execute cR cL (Hc : CceParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cce_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cce_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cce_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cce_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cce_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cce_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cce_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CcePredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma cce_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CcePredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cce_forall_cover _ _ (CcePredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CceRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cce_rel_canonical (T : Type) (rR : T -> T -> bool) : CceRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cce_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CceRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cce_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CceRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cce_forall_cover _ _ (CceRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cce_rel_canonical T) (cce_rel_surjective T) PR PL).
Qed.

Definition CceJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CceRelRel T (rR tR) (rL tL).

Lemma cce_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CceJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cce_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CceJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cce_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CceJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cce_forall_cover _ _ (CceJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cce_jldp_canonical T) (cce_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cce_PR_JLFP_policy :
  And (forall rR : Priority.JLFP_policy Job, CceRelRel Job rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLFP_policy Job dJ, CceRelRel Job (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cce_rel_canonical Job) (cce_rel_surjective Job)). Qed.

Lemma cce_PR_EDF jaR jaL (Hja : CceParRel Job jaR jaL) jdR jdL (Hjd : CceParRel Job jdR jdL) :
  CceRelRel Job (Priority.EDF jaR jdR) (I.Prosa_Classic_Model_Priority_Priority_EDF Job dJ jaL jdL).
Proof.
  intros a b. exact (ct_decide_le _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja a) (Hjd a))
                                          (sub_add_correspondence _ _ _ _ (Hja b) (Hjd b))).
Qed.

Lemma cce_PR_job_relative_dealine tdR tdL (Htd : CceParRel Task tdR tdL) (job_task : Job -> Task) :
  CceParRel Job (Priority.job_relative_dealine tdR job_task)
    (I.Prosa_Classic_Model_Priority_Priority_job_relative_dealine Task dT tdL Job dJ job_task).
Proof. intro j. exact (Htd (job_task j)). Qed.

End PriodefsDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cce_J_job_cost_le_task_cost tcR tcL (Htc : CceParRel Task tcR tcL) cR cL (Hc : CceParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

Lemma cce_J_cost_of_jobs_from_arrival_sequence_le_task_cost tcR tcL (Htc : CceParRel Task tcR tcL)
    cR cL (Hc : CceParRel Job cR cL) (job_task : Job -> Task) aR aL (Ha : CceArrRel Job aR aL) :
  PropSPropRel (Job.cost_of_jobs_from_arrival_sequence_le_task_cost tcR cR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_cost_of_jobs_from_arrival_sequence_le_task_cost Task dT tcL Job dJ cL job_task aL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp.
  - apply: ct_exists_nat => tR tL Ht. exact (cce_mem Job j _ _ (Ha tR tL Ht)).
  - exact (ct_bool_truth _ _ (cce_J_job_cost_le_task_cost tcR tcL Htc cR cL Hc job_task j)).
Qed.

End JobDefs.

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cce_TA_is_job_of_task (job_task : Job -> Task) tsk j :
  CtBoolRel (TaskArrival.is_job_of_task job_task tsk j)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk j).
Proof. exact (ct_decide_eq Task (job_task j) tsk). Qed.

Lemma cce_TA_arrivals_of_task_between (job_task : Job -> Task) aR aL (Ha : CceArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_between Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans (cl_filter cid _ (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk)
                            (cce_TA_is_job_of_task job_task tsk) _) _).
  exact (f_equal (I.List_filter Job (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk))
           (Logic.eq_sym (cl_list_logic _ _ _ (cce_jobs_arrived_between Job aR aL Ha _ _ _ _ H1 H2)))).
Qed.

Lemma cce_TA_num_arrivals_of_task (job_task : Job -> Task) aR aL (Ha : CceArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (TaskArrival.num_arrivals_of_task job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_num_arrivals_of_task Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  have H := cce_TA_arrivals_of_task_between job_task aR aL Ha tsk _ _ _ _ H1 H2.
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
Definition CceCurveRel (fR : Task -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk nR nL, SubNatRel nR nL -> SubNatRel (fR tsk nR) (fL tsk nL).

Notation NA := (cce_TA_num_arrivals_of_task Task Job).

Lemma cce_AC_is_arrival_bound (job_task : Job -> Task) aR aL (Ha : CceArrRel Job aR aL)
    mR mL (Hm : CceCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.is_arrival_bound job_task aR mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_is_arrival_bound Task dT Job dJ job_task aL mL tsk).
Proof.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 H2).
  exact (sub_nat_le_correspondence _ _ _ _ (NA job_task aR aL Ha tsk _ _ _ _ H1 H2) (Hm tsk _ _ (ct_sub_rel _ _ _ _ H2 H1))).
Qed.

Lemma cce_AC_zero_arrival_curve mR mL (Hm : CceCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.zero_arrival_curve mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_zero_arrival_curve Task dT mL tsk).
Proof. exact (sub_nat_eq_correspondence _ _ _ _ (Hm tsk _ _ (sub_nat_rel_canonical 0)) (sub_nat_rel_canonical 0)). Qed.

Lemma cce_AC_monotonic_arrival_curve mR mL (Hm : CceCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.monotonic_arrival_curve mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_monotonic_arrival_curve Task dT mL tsk).
Proof.
  apply: ct_forall_nat => xR xL Hx. apply: ct_forall_nat => yR yL Hy.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ Hx Hy)).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hm tsk _ _ Hx) (Hm tsk _ _ Hy))).
Qed.

Lemma cce_AC_proper_arrival_curve (job_task : Job -> Task) aR aL (Ha : CceArrRel Job aR aL)
    mR mL (Hm : CceCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.proper_arrival_curve job_task aR mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_proper_arrival_curve Task dT Job dJ job_task aL mL tsk).
Proof.
  apply: ct_and; first exact (cce_AC_is_arrival_bound job_task aR aL Ha mR mL Hm tsk).
  apply: ct_and; first exact (cce_AC_zero_arrival_curve mR mL Hm tsk).
  exact (cce_AC_monotonic_arrival_curve mR mL Hm tsk).
Qed.

Lemma cce_AC_family_of_proper_arrival_curves (job_task : Job -> Task) aR aL (Ha : CceArrRel Job aR aL)
    mR mL (Hm : CceCurveRel mR mL) tsR tsL (Hts : ClListRel cid tsR tsL) :
  PropSPropRel (ArrivalCurves.family_of_proper_arrival_curves job_task aR mR tsR)
    (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_family_of_proper_arrival_curves Task dT Job dJ job_task aL mL tsL).
Proof.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cce_mem Task tsk _ _ Hts).
  exact (cce_AC_proper_arrival_curve job_task aR aL Ha mR mL Hm tsk).
Qed.

End AcboundsDefs.

(** * Arrival curves [Task -> time -> nat], with two-way totals *)

Lemma cce_curve_canonical (Task : eqType) mR : CceCurveRel Task mR (fun tsk nL => sub_nat_to_imported (mR tsk (sub_nat_to_rocq nL))).
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma cce_curve_surjective (Task : eqType) mL : CceCurveRel Task (fun tsk nR => sub_nat_to_rocq (mL tsk (sub_nat_to_imported nR))) mL.
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. exact (sub_nat_rel_surjective _). Qed.

Lemma cce_forall_curve (Task : eqType) (PR : (Task -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall mR mL, CceCurveRel Task mR mL -> PropSPropRel (PR mR) (PL mL)) -> PropSPropRel (forall m, PR m) (forall m, PL m).
Proof. exact (cce_forall_cover _ _ (CceCurveRel Task) _ _ (cce_curve_canonical Task) (cce_curve_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section AcwbDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat).
Hypothesis Htc : CceParRel Task tcR tcL.
Variables (mR : Task -> nat -> nat) (mL : Task -> Lean.Nat -> Lean.Nat).
Hypothesis Hm : CceCurveRel Task mR mL.

Lemma cce_WB_task_request_bound_function tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.task_request_bound_function tcR mR tsk dR) (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_task_request_bound_function Task dT tcL mL tsk dL).
Proof. exact (sub_mul_correspondence _ _ _ _ (Htc tsk) (Hm tsk _ _ Hd)). Qed.

Notation TRBF := cce_WB_task_request_bound_function.

Lemma cce_WB_total_request_bound_function tsR tsL (Hts : ClListRel cid tsR tsL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.total_request_bound_function tcR mR tsR dR) (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_total_request_bound_function Task dT tcL mL tsL dL).
Proof. exact (cce_sum_rel Task _ _ (fun x => TRBF x dR dL Hd) _ _ Hts). Qed.

End AcwbDefs.

Section UwlDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

End UwlDefs.

Section UrtDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.

Lemma cce_RT_is_response_time_bound_of_job aR aL (Ha : CceParRel Job aR aL) cR cL (Hc : CceParRel Job cR cL)
    j rR rL (Hr : SubNatRel rR rL) :
  CtBoolRel (ResponseTime.is_response_time_bound_of_job aR cR sR j rR) (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_job Job dJ aL cL sL j rL).
Proof. exact (cce_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr)). Qed.

Lemma cce_RT_is_response_time_bound_of_task aR aL (Ha : CceParRel Job aR aL) cR cL (Hc : CceParRel Job cR cL)
    (job_task : Job -> Task) arrR arrL (Harr : CceArrRel Job arrR arrL) tsk rR rL (Hr : SubNatRel rR rL) :
  PropSPropRel (ResponseTime.is_response_time_bound_of_task aR cR job_task arrR sR tsk rR)
    (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_task Task dT Job dJ aL cL job_task arrL sL tsk rL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cce_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (cce_RT_is_response_time_bound_of_job aR aL Ha cR cL Hc j rR rL Hr)).
Qed.

End UrtDefs.

Lemma cce_NP_is_nonpreemptive_schedule (Job : eqType) sR sL (Hs : CceSchedRel Job sR sL)
    cR cL (Hc : CceParRel Job cR cL) :
  PropSPropRel (NonpreemptiveSchedule.is_nonpreemptive_schedule cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Schedule_NonpreemptiveSchedule_is_nonpreemptive_schedule Job (ct_decidable_eq Job) cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht Ht').
  apply: ct_imp; first exact (ct_bool_truth _ _ (cce_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (cce_US_completed_by Job sR sL Hs cR cL Hc j t'R t'L Ht'))).
  exact (ct_bool_truth _ _ (cce_US_scheduled_at Job sR sL Hs j t'R t'L Ht')).
Qed.

Section UplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.

Lemma cce_UP_work_conserving aR aL (Ha : CceParRel Job aR aL) cR cL (Hc : CceParRel Job cR cL)
    arrR arrL (Harr : CceArrRel Job arrR arrL) :
  PropSPropRel (Platform.work_conserving aR cR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Basic_Platform_Platform_work_conserving Job dJ aL cL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cce_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cce_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (cce_US_scheduled_at Job sR sL Hs j_other tR tL Ht)).
Qed.

End UplatDefs.

Lemma cce_iff (P Q : Prop) (PL QL : SProp) :
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

(** * Preemption models *)

Section LpdefsPmRel.
Variable Job : eqType.
Definition CcePmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma cce_pm_canonical pR : CcePmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cce_pm_surjective pL : CcePmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cce_forall_pm (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CcePmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (cce_forall_cover _ _ CcePmRel _ _ cce_pm_canonical cce_pm_surjective PR PL). Qed.

End LpdefsPmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LpdefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CcePmRel Job pR pL.

Notation SA := (cce_US_scheduled_at Job sR sL Hs).
Notation SV := (cce_US_service Job sR sL Hs).

Lemma cce_LP_preemption_time tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_preemption_time Job dJ sL pL tL).
Proof.
  refine (cce_trs (Hs tR tL Ht)
            (fun z => CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR)
                        (match z with
                         | I.Option_some j => pL j (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL)
                         | I.Option_none => I.Bool_true end)) _).
  rewrite /LimitedPreemptionPlatform.preemption_time. destruct (sR tR) as [x|].
  - exact (Hp x _ _ (SV x tR tL Ht)).
  - exact (ct_bool_canonical true).
Qed.

End LpdefsDefs.

Section LpdefsDefs2.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CcePmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : CceParRel Job cR cL) (Hm : CceParRel Job mR mL) (Htm : CceParRel Task tmR tmL).

End LpdefsDefs2.

Lemma cce_getD (T : Type) (s : seq T) sL (Hs : ClListRel cid s sL) (x0 : T) nR nL (Hn : SubNatRel nR nL) :
  Logic.eq (I.List_getD T sL nL x0) (nth x0 s nR).
Proof.
  rewrite (cl_list_logic _ _ _ Hs) (cl_nat_logic _ _ Hn). exact (Logic.eq_sym (cl_nth cid x0 s nR)).
Qed.

Lemma cce_pred_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ct_sub nL (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Hn. apply: coq_eq_to_imported_eq. rewrite -subn1.
  exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Relations *)

Lemma cce_eq_transport (T : Type) (a b : T) aL bL : Lean.eq a aL -> Lean.eq b bL ->
  PropSPropRel (Logic.eq a b) (Lean.eq aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (ct_eq_rel T a b). Qed.

(** Functions [nat -> T] (identical values) and [nat -> nat] (values by [SubNatRel]), pointwise on related arguments. *)
Definition CceRsFunRel (T : Type) (fR : nat -> T) (fL : Lean.Nat -> T) : SProp :=
  forall nR nL, SubNatRel nR nL -> Lean.eq (fR nR) (fL nL).
Definition CceNatFunRel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) : SProp :=
  forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

(** Interference bound functions [Task -> time -> time -> time], pointwise on related arguments and values. *)
Definition CceIbfRel (Task : Type) (fR : Task -> nat -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk, forall aR aL, SubNatRel aR aL -> CceNatFunRel (fR tsk aR) (fL tsk aL).

Definition cce_ibf_to_target (Task : Type) (fR : Task -> nat -> nat -> nat) : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat :=
  fun tsk aL xL => sub_nat_to_imported (fR tsk (sub_nat_to_rocq aL) (sub_nat_to_rocq xL)).
Definition cce_ibf_to_source (Task : Type) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : Task -> nat -> nat -> nat :=
  fun tsk aR xR => sub_nat_to_rocq (fL tsk (sub_nat_to_imported aR) (sub_nat_to_imported xR)).

Lemma cce_ibf_canonical (Task : Type) fR : CceIbfRel Task fR (cce_ibf_to_target Task fR).
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  unfold cce_ibf_to_target. rewrite !sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma cce_ibf_surjective (Task : Type) fL : CceIbfRel Task (cce_ibf_to_source Task fL) fL.
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma cce_forall_ibf (Task : Type) (PR : (Task -> nat -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, CceIbfRel Task fR fL -> PropSPropRel (PR fR) (PL fL)) -> PropSPropRel (forall f, PR f) (forall f, PL f).
Proof. exact (cce_forall_cover _ _ (CceIbfRel Task) (cce_ibf_to_target Task) (cce_ibf_to_source Task) (cce_ibf_canonical Task) (cce_ibf_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(* ------------------------------------------------------------------ *)
(** * Interference predicates and interfering workloads *)

Section NPRJISEQARDIRel.
Variable Job : eqType.

Definition CceIntRel (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (iR j tR) (iL j tL).

Lemma cce_int_canonical iR : CceIntRel iR (fun j tL => ct_b2l (iR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cce_int_surjective iL : CceIntRel (fun j tR => ct_l2b (iL j (sub_nat_to_imported tR))) iL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cce_forall_int (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall iR iL, CceIntRel iR iL -> PropSPropRel (PR iR) (PL iL)) -> PropSPropRel (forall i, PR i) (forall i, PL i).
Proof. exact (cce_forall_cover _ _ CceIntRel _ _ cce_int_canonical cce_int_surjective PR PL). Qed.

Definition CceWlRel (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (wR j tR) (wL j tL).

Lemma cce_wl_canonical wR : CceWlRel wR (fun j tL => sub_nat_to_imported (wR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma cce_wl_surjective wL : CceWlRel (fun j tR => sub_nat_to_rocq (wL j (sub_nat_to_imported tR))) wL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (sub_nat_rel_surjective _). Qed.

Lemma cce_forall_wl (PR : (Job -> nat -> nat) -> Prop) (PL : (Job -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall wR wL, CceWlRel wR wL -> PropSPropRel (PR wR) (PL wL)) -> PropSPropRel (forall w, PR w) (forall w, PL w).
Proof. exact (cce_forall_cover _ _ CceWlRel _ _ cce_wl_canonical cce_wl_surjective PR PL). Qed.

End NPRJISEQARDIRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section NPRJISEQARDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Section NPRJISEQARDSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CceParRel Job aR aL) (Hc : CceParRel Job cR cL).
Variables (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat).
Hypotheses (Hi : CceIntRel Job iR iL) (Hw : CceWlRel Job wR wL).

End NPRJISEQARDSched.

End NPRJISEQARDDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Module LS := prosa.classic.model.schedule.uni.limited.schedule.

Section NPRJISEQLSDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CceParRel Job cR cL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CceArrRel Job arrR arrL.
Variables (lR : Job -> nat) (lL : Job -> Lean.Nat).
Hypothesis Hl : CceParRel Job lR lL.

Section NPRJISEQLSSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.

End NPRJISEQLSSched.

Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat) (tlR : Task -> nat) (tlL : Task -> Lean.Nat).
Hypotheses (Htc : CceParRel Task tcR tcL) (Htl : CceParRel Task tlR tlL).

End NPRJISEQLSDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section NPRJISEQSVDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.

End NPRJISEQSVDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section NPRJISEQSTDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.
Variable job_task : Job -> Task.

End NPRJISEQSTDefs.

(* ------------------------------------------------------------------ *)
(** * [has] against [List.any] *)

Lemma cce_has_eq (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL x)) :
  forall s, Logic.eq (I.List_any T (cl_map cid s) pL) (ct_b2l (has pR s)).
Proof.
  elim => [|x s IH]; first reflexivity.
  have -> : Logic.eq (I.List_any T (cl_map cid (x :: s)) pL) (I.Bool_or (pL x) (I.List_any T (cl_map cid s) pL)).
  { cbn. destruct (pL x); reflexivity. }
  rewrite (ct_bool_rel_logic _ _ (Hp x)) IH /=. by case: (pR x); case: (has pR s).
Qed.

Lemma cce_has (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL x)) :
  forall s, CtBoolRel (has pR s) (I.List_any T (cl_map cid s) pL).
Proof. intro s. exact (coq_eq_to_imported_eq _ _ (Logic.eq_sym (cce_has_eq T pR pL Hp s))). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(* ------------------------------------------------------------------ *)
(** * Service of jobs (as in the accepted classic uniprocessor service certificate) *)

Section NPRJILBISvc.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.

End NPRJILBISvc.

(* ------------------------------------------------------------------ *)
(** * Auxiliary relations *)

Lemma cce_implb aR aL (Ha : CtBoolRel aR aL) bR bL (Hb : CtBoolRel bR bL) :
  CtBoolRel (aR ==> bR) (I.Bool_or (I.Bool_not aL) bL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite (ct_bool_rel_logic _ _ Ha) (ct_bool_rel_logic _ _ Hb). clear Ha Hb.
  by case: aR; case: bR.
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section NPRJILBIDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CceParRel Job jaR jaL) (Hc : CceParRel Job cR cL).
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CceArrRel Job aR aL.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.
Variables (hR : Job -> Job -> bool) (hL : Job -> Job -> I.Bool).
Hypothesis Hh : CceRelRel Job hR hL.

Lemma cce_LP_work_conserving :
  PropSPropRel (LimitedPreemptionPlatform.work_conserving jaR cR aR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_work_conserving Job dJ jaL cL aL sL).
Proof. exact (cce_UP_work_conserving Job sR sL Hs jaR jaL Hja cR cL Hc aR aL Ha). Qed.

End NPRJILBIDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cce_arriving_at (Job : eqType) aR aL (Ha : CceArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arriving_at aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arriving_at Job (ct_decidable_eq Job) aL tL).
Proof. exact (Ha tR tL Ht). Qed.

Section NPRJIDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.
Variables (hR : Job -> Job -> bool) (hL : Job -> Job -> I.Bool).
Hypothesis Hh : CceRelRel Job hR hL.
Variable job_task : Job -> Task.

Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CceParRel Job cR cL.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CceArrRel Job aR aL.

End NPRJIDefs.

(* ------------------------------------------------------------------ *)
(** * Preemption models *)

Section NPRLPDPmRel.
Variable Job : eqType.
Definition CcePmRel__NPRLPDPmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma cce_pm_canonical__NPRLPDPmRel pR : CcePmRel__NPRLPDPmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cce_pm_surjective__NPRLPDPmRel pL : CcePmRel__NPRLPDPmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cce_forall_pm__NPRLPDPmRel (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CcePmRel__NPRLPDPmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (cce_forall_cover _ _ CcePmRel__NPRLPDPmRel _ _ cce_pm_canonical__NPRLPDPmRel cce_pm_surjective__NPRLPDPmRel PR PL). Qed.

End NPRLPDPmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section NPRLPDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CcePmRel Job pR pL.

Notation SA := (cce_US_scheduled_at Job sR sL Hs).
Notation SV := (cce_US_service Job sR sL Hs).

Lemma cce_LPD_preemption_time tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_preemption_time Job dJ sL pL tL).
Proof.
  refine (cce_trs (Hs tR tL Ht)
            (fun z => CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR)
                        (match z with
                         | I.Option_some j => pL j (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL)
                         | I.Option_none => I.Bool_true end)) _).
  rewrite /LimitedPreemptionPlatform.preemption_time. destruct (sR tR) as [x|].
  - exact (Hp x _ _ (SV x tR tL Ht)).
  - exact (ct_bool_canonical true).
Qed.

End NPRLPDDefs.

Section NPRLPDDefs2.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CcePmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : CceParRel Job cR cL) (Hm : CceParRel Job mR mL) (Htm : CceParRel Task tmR tmL).

End NPRLPDDefs2.

Lemma cce_LPD_work_conserving (Job : eqType) sR sL (Hs : CceSchedRel Job sR sL) cR cL (Hc : CceParRel Job cR cL)
    c0R c0L (Hc0 : CceParRel Job c0R c0L) arrR arrL (Harr : CceArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.work_conserving cR c0R arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_work_conserving Job (ct_decidable_eq Job) cL c0L arrL sL).
Proof. exact (cce_UP_work_conserving Job sR sL Hs cR cL Hc c0R c0L Hc0 arrR arrL Harr). Qed.

Section NPRLPDResp.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CceParRel Job aR aL) (Hc : CceParRel Job cR cL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CceArrRel Job arrR arrL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CcePmRel Job pR pL.

Lemma cce_LPD_respects_JLFP_policy_at_preemption_point hR hL (Hh : CceRelRel Job hR hL) :
  PropSPropRel (LimitedPreemptionPlatform.respects_JLFP_policy_at_preemption_point aR cR arrR sR pR hR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_respects_JLFP_policy_at_preemption_point Job dJ aL cL arrL sL pL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cce_LPD_preemption_time Job sR sL Hs pR pL Hp tR tL Ht)).
  apply: ct_imp; first exact (cce_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cce_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cce_US_scheduled_at Job sR sL Hs j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh j_hp j)).
Qed.

End NPRLPDResp.

(* ------------------------------------------------------------------ *)
(** * [\max] over a filtered sequence against the v0.6 [maxFiltered] (through the exported equation
    [maxFiltered_eq_foldr_cond]) *)

Section NPRPIBMaxSeq.
Variable X : Type.
Variables (PR : X -> bool) (PL : X -> I.Bool).
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).
Variables (FR : X -> nat) (FL : X -> Lean.Nat).
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cce_foldr_max_cond : forall s : seq X,
  Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat I.Nat_max (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))
              (I.List_map_inst2 X Lean.Nat (fun x => I.cond Lean.Nat (PL x) (FL x) (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)))
                 (cl_map cid s)))
           (sub_nat_to_imported (\max_(x <- s | PR x) FR x)).
Proof.
  elim => [|x s IH]; first by rewrite big_nil.
  rewrite big_cons.
  change (Logic.eq (I.Nat_max (I.cond Lean.Nat (PL x) (FL x) (sub_nat_to_imported 0))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat I.Nat_max (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))
              (I.List_map_inst2 X Lean.Nat (fun x => I.cond Lean.Nat (PL x) (FL x) (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)))
                 (cl_map cid s))))
         (sub_nat_to_imported (if PR x then maxn (FR x) (\max_(j <- s | PR j) FR j) else \max_(j <- s | PR j) FR j))).
  rewrite IH (ct_bool_rel_logic _ _ (HP x)).
  have HFx := imported_eq_to_coq_eq _ _ (HF x).
  destruct (PR x).
  - change (Logic.eq (I.Nat_max (FL x) (sub_nat_to_imported (\max_(j <- s | PR j) FR j)))
                     (sub_nat_to_imported (maxn (FR x) (\max_(j <- s | PR j) FR j)))).
    rewrite -HFx. exact (ct_max_canonical _ _).
  - change (Logic.eq (I.Nat_max (sub_nat_to_imported 0) (sub_nat_to_imported (\max_(j <- s | PR j) FR j)))
                     (sub_nat_to_imported (\max_(j <- s | PR j) FR j))).
    rewrite (ct_max_canonical 0 _) max0n. reflexivity.
Qed.

Lemma cce_max_filtered_rel s sL (Hs : ClListRel cid s sL) :
  SubNatRel (\max_(x <- s | PR x) FR x) (I.Prosa_Util_Sum_maxFiltered X sL PL FL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite -(imported_eq_to_coq_eq _ _ Hs).
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_maxFiltered_eq_foldr_cond X PL FL (cl_map cid s))).
  exact (Logic.eq_sym (cce_foldr_max_cond s)).
Qed.

End NPRPIBMaxSeq.

(** [min] on [Nat] through [instMinNat] (this export elaborates [min] via the [Min] instance). *)
Lemma cib_min_canonical (a b : nat) :
  Logic.eq ((I.Min_min_inst1 Lean.Nat I.instMinNat) (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (minn a b)).
Proof.
  have Hle := sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical a) (sub_nat_rel_canonical b).
  have -> : Logic.eq ((I.Min_min_inst1 Lean.Nat I.instMinNat) (sub_nat_to_imported a) (sub_nat_to_imported b))
      (I.ite Lean.Nat (I.LE_le_inst1 Lean.Nat I.instLENat (sub_nat_to_imported a) (sub_nat_to_imported b))
         (I.Nat_decLe (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported a) (sub_nat_to_imported b))
    by reflexivity.
  destruct (I.Nat_decLe (sub_nat_to_imported a) (sub_nat_to_imported b)) as [h|h].
  - have Hab : ~~ (a <= b)%nat.
    { apply/negP => Hs. exact (interpret_strict _ (ct_target_false_to_strict (h (prop_to_sprop _ _ Hle Hs)))). }
    rewrite -ltnNge in Hab. rewrite (minn_idPr (ltnW Hab)). reflexivity.
  - have Hab : (a <= b)%nat := sprop_to_prop _ _ Hle h. rewrite (minn_idPl Hab). reflexivity.
Qed.

Lemma cib_min_rel aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel (minn aR bR) ((I.Min_min_inst1 Lean.Nat I.instMinNat) aL bL).
Proof.
  intros Ha Hb. rewrite -(imported_eq_to_coq_eq _ _ Ha) -(imported_eq_to_coq_eq _ _ Hb).
  apply: coq_eq_to_imported_eq. exact (Logic.eq_sym (cib_min_canonical aR bR)).
Qed.

Lemma cce_jrd (Task Job : eqType) pR pL (Hp : CceParRel Task pR pL) (job_task : Job -> Task) j :
  SubNatRel (pR (job_task j))
    (I.Prosa_Classic_Model_Priority_Priority_job_relative_dealine Task (ct_decidable_eq Task) pL Job (ct_decidable_eq Job) job_task j).
Proof. exact (Hp (job_task j)). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cce_EDF_task_rbf_changes_at (Task : eqType) tcR tcL (Htc : CceParRel Task tcR tcL)
    mR mL (Hm : CceCurveRel Task mR mL) tsk AR AL (HA : SubNatRel AR AL) :
  CtBoolRel (@AbstractRTAforEDFwithArrivalCurves.task_rbf_changes_at Task tcR mR tsk AR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_ResponseTimeBound_AbstractRTAforEDFwithArrivalCurves_task_rbf_changes_at Task (ct_decidable_eq Task) tcL mL tsk AL).
Proof.
  have W := cce_WB_task_request_bound_function Task tcR tcL Htc mR mL Hm.
  exact (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _ (W tsk _ _ HA)
    (W tsk _ _ (sub_add_correspondence _ _ _ _ HA (sub_nat_rel_canonical 1))))).
Qed.

Lemma cce_EDF_bound_on_total_hep_workload_changes_at (Task : eqType) tcR tcL (Htc : CceParRel Task tcR tcL)
    tdR tdL (Htd : CceParRel Task tdR tdL) tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL)
    mR mL (Hm : CceCurveRel Task mR mL) tsk AR AL (HA : SubNatRel AR AL) :
  CtBoolRel (@AbstractRTAforEDFwithArrivalCurves.bound_on_total_hep_workload_changes_at Task tcR tdR tsR mR tsk AR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_ResponseTimeBound_AbstractRTAforEDFwithArrivalCurves_bound_on_total_hep_workload_changes_at Task (ct_decidable_eq Task) tcL tdL tsL mL tsk AL).
Proof.
  have W := cce_WB_task_request_bound_function Task tcR tcL Htc mR mL Hm.
  rewrite -(imported_eq_to_coq_eq _ _ Hts).
  refine (cce_has Task _ _ (fun tsko => _) tsR).
  exact (ct_bool_and _ _ _ _ (ct_bool_not _ _ (ct_decide_eq Task tsk tsko))
    (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _
      (W tsko _ _ (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ HA (Htd tsk)) (Htd tsko)))
      (W tsko _ _ (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _
          (sub_add_correspondence _ _ _ _ HA (sub_nat_rel_canonical 1)) (Htd tsk)) (Htd tsko)))))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(* ------------------------------------------------------------------ *)
(** * Preemption models *)

Section LMLPDPmRel.
Variable Job : eqType.
Definition CcePmRel__LMLPDPmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma cce_pm_canonical__LMLPDPmRel pR : CcePmRel__LMLPDPmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cce_pm_surjective__LMLPDPmRel pL : CcePmRel__LMLPDPmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cce_forall_pm__LMLPDPmRel (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CcePmRel__LMLPDPmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (cce_forall_cover _ _ CcePmRel__LMLPDPmRel _ _ cce_pm_canonical__LMLPDPmRel cce_pm_surjective__LMLPDPmRel PR PL). Qed.

End LMLPDPmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LMLPDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CcePmRel Job pR pL.

Notation SA := (cce_US_scheduled_at Job sR sL Hs).
Notation SV := (cce_US_service Job sR sL Hs).

Lemma cce_LPD_preemption_time__LMLPDDefs tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_preemption_time Job dJ sL pL tL).
Proof.
  refine (cce_trs (Hs tR tL Ht)
            (fun z => CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR)
                        (match z with
                         | I.Option_some j => pL j (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL)
                         | I.Option_none => I.Bool_true end)) _).
  rewrite /LimitedPreemptionPlatform.preemption_time. destruct (sR tR) as [x|].
  - exact (Hp x _ _ (SV x tR tL Ht)).
  - exact (ct_bool_canonical true).
Qed.

End LMLPDDefs.

Section LMLPDDefs2.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CcePmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : CceParRel Job cR cL) (Hm : CceParRel Job mR mL) (Htm : CceParRel Task tmR tmL).

End LMLPDDefs2.

Section LMLPDResp.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CceSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CceParRel Job aR aL) (Hc : CceParRel Job cR cL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CceArrRel Job arrR arrL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CcePmRel Job pR pL.

Lemma cce_LPD_respects_JLFP_policy_at_preemption_point__LMLPDResp hR hL (Hh : CceRelRel Job hR hL) :
  PropSPropRel (LimitedPreemptionPlatform.respects_JLFP_policy_at_preemption_point aR cR arrR sR pR hR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_respects_JLFP_policy_at_preemption_point Job dJ aL cL arrL sL pL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cce_LPD_preemption_time Job sR sL Hs pR pL Hp tR tL Ht)).
  apply: ct_imp; first exact (cce_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cce_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cce_US_scheduled_at Job sR sL Hs j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh j_hp j)).
Qed.

End LMLPDResp.

(* ------------------------------------------------------------------ *)
(** * Nat lists (universe instance [List_inst1]) through the Nat embedding *)

Notation NL := (I.List_inst1 Lean.Nat).
Notation nc := sub_nat_to_imported.
Definition CceNlRel (sR : seq nat) (sL : NL) : SProp := ClListRel1 sub_nat_to_imported sR sL.

Lemma cce_dc x : Logic.eq (sub_nat_to_rocq (sub_nat_to_imported x)) x.
Proof. exact (sub_nat_rocq_roundtrip x). Qed.
Lemma cce_cd y : Logic.eq (sub_nat_to_imported (sub_nat_to_rocq y)) y.
Proof. exact (imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip y)). Qed.

Notation EQ H := (imported_eq_to_coq_eq _ _ H).

Lemma cce_distances_eq : forall s,
  Logic.eq (cl1_map nc (prosa.util.nondecreasing.distances s)) (I.Prosa_Util_Nondecreasing_distances (cl1_map nc s)).
Proof.
  elim => [|x s IH]; first exact (Logic.eq_sym (EQ I.Prosa_Validation_ClassicConcreteEdfRtaInterface_distances_nil)).
  case: s IH => [|y ys] IH; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_distances_single (nc x)))).
  rewrite (EQ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_distances_cons2 (nc x) (nc y) (cl1_map nc ys))).
  have Hs : Logic.eq (prosa.util.nondecreasing.distances [:: x, y & ys]) ((y - x) :: prosa.util.nondecreasing.distances (y :: ys)) by rewrite /prosa.util.nondecreasing.distances /= drop0.
  rewrite Hs.
  change (Logic.eq (I.List_cons_inst1 Lean.Nat (nc (y - x)) (cl1_map nc (prosa.util.nondecreasing.distances (y :: ys))))
    (I.List_cons_inst1 Lean.Nat (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat) (nc y) (nc x))
       (I.Prosa_Util_Nondecreasing_distances (cl1_map nc (y :: ys))))).
  rewrite -IH. exact (f_equal (fun z => I.List_cons_inst1 Lean.Nat z (cl1_map nc (prosa.util.nondecreasing.distances (y :: ys))))
    (EQ (ct_sub_rel _ _ _ _ (sub_nat_rel_canonical y) (sub_nat_rel_canonical x)))).
Qed.

Lemma cce_distances sR sL : CceNlRel sR sL -> CceNlRel (prosa.util.nondecreasing.distances sR) (I.Prosa_Util_Nondecreasing_distances sL).
Proof.
  intro H. exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (cce_distances_eq sR))
    (sub_imported_eq_congr I.Prosa_Util_Nondecreasing_distances _ _ H)).
Qed.

Lemma cce_foldl_max_eq : forall s z,
  Logic.eq (nc (seq.foldl maxn z s)) (I.List_foldl_inst3 Lean.Nat Lean.Nat I.Nat_max (nc z) (cl1_map nc s)).
Proof.
  elim => [|x s IH] z; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_foldl_max_nil (nc z)))).
  rewrite (EQ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_foldl_max_cons (nc z) (nc x) (cl1_map nc s))).
  rewrite -(EQ (ct_max_rel _ _ _ _ (sub_nat_rel_canonical z) (sub_nat_rel_canonical x))).
  exact (IH (maxn z x)).
Qed.

Lemma cce_max0 sR sL : CceNlRel sR sL -> SubNatRel (prosa.util.list.max0 sR) (I.Prosa_Util_List_max0 sL).
Proof.
  intro H.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_max0_eq sL))).
  exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (cce_foldl_max_eq sR 0))
    (sub_imported_eq_congr (fun l => I.List_foldl_inst3 Lean.Nat Lean.Nat I.Nat_max (nc 0) l) _ _ H)).
Qed.

Lemma cce_first0_eq s : Logic.eq (nc (prosa.util.list.first0 s)) (I.Prosa_Util_List_first0 (cl1_map nc s)).
Proof.
  case: s => [|x s]; first exact (Logic.eq_sym (EQ I.Prosa_Validation_ClassicConcreteEdfRtaInterface_first0_nil)).
  exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_first0_cons (nc x) (cl1_map nc s)))).
Qed.

Lemma cce_first0 sR sL : CceNlRel sR sL -> SubNatRel (prosa.util.list.first0 sR) (I.Prosa_Util_List_first0 sL).
Proof.
  intro H. exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (cce_first0_eq sR))
    (sub_imported_eq_congr I.Prosa_Util_List_first0 _ _ H)).
Qed.

Lemma cce_last0_eq : forall s, Logic.eq (nc (prosa.util.list.last0 s)) (I.Prosa_Util_List_last0 (cl1_map nc s)).
Proof.
  elim => [|x s IH]; first exact (Logic.eq_sym (EQ I.Prosa_Validation_ClassicConcreteEdfRtaInterface_last0_nil)).
  case: s IH => [|y ys] IH; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_last0_single (nc x)))).
  rewrite (EQ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_last0_cons2 (nc x) (nc y) (cl1_map nc ys))).
  exact IH.
Qed.

Lemma cce_last0 sR sL : CceNlRel sR sL -> SubNatRel (prosa.util.list.last0 sR) (I.Prosa_Util_List_last0 sL).
Proof.
  intro H. exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (cce_last0_eq sR))
    (sub_imported_eq_congr I.Prosa_Util_List_last0 _ _ H)).
Qed.

Lemma cce_nth_eq : forall s n,
  Logic.eq (nc (seq.nth 0 s n)) (I.List_getD_inst1 Lean.Nat (cl1_map nc s) (nc n) (nc 0)).
Proof.
  elim => [|x s IH] n; first by case: n => [|n]; exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_getD_nil _ (nc 0)))).
  case: n => [|n]; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_getD_cons_zero (nc x) (cl1_map nc s) (nc 0)))).
  exact (Logic.eq_trans (IH n) (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_getD_cons_succ (nc x) (cl1_map nc s) (nc n) (nc 0))))).
Qed.

Lemma cce_nth sR sL (H : CceNlRel sR sL) nR nL (Hn : SubNatRel nR nL) :
  SubNatRel (seq.nth 0 sR nR) (I.List_getD_inst1 Lean.Nat sL nL (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))).
Proof.
  exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (cce_nth_eq sR nR))
    (sub_imported_eq_congr2 (fun l m => I.List_getD_inst1 Lean.Nat l m (nc 0)) _ _ _ _ H Hn)).
Qed.

Lemma cce_size_eq : forall s, Logic.eq (nc (seq.size s)) (I.List_length_inst1 Lean.Nat (cl1_map nc s)).
Proof.
  elim => [|x s IH]; first exact (Logic.eq_sym (EQ I.Prosa_Validation_ClassicConcreteEdfRtaInterface_length_nil)).
  rewrite (EQ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_length_cons (nc x) (cl1_map nc s))) -IH. reflexivity.
Qed.

Lemma cce_size sR sL : CceNlRel sR sL -> SubNatRel (seq.size sR) (I.List_length_inst1 Lean.Nat sL).
Proof.
  intro H. exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (cce_size_eq sR))
    (sub_imported_eq_congr (I.List_length_inst1 Lean.Nat) _ _ H)).
Qed.

Lemma cce_nmem xR xL (Hx : SubNatRel xR xL) sR sL (H : CceNlRel sR sL) :
  PropSPropRel (xR \in sR)
    (I.Membership_mem_inst3 Lean.Nat NL (I.List_instMembership_inst1 Lean.Nat) sL xL).
Proof.
  rewrite (cl_nat_logic _ _ Hx).
  exact (cl1_mem_rel_list _ Lean.Nat sub_nat_to_imported sub_nat_to_rocq cce_dc xR sR sL H).
Qed.

Lemma cce_nl_eq sR sL tR tL (Hs : CceNlRel sR sL) (Ht : CceNlRel tR tL) :
  PropSPropRel (Logic.eq sR tR) (Lean.eq sL tL).
Proof.
  rewrite (cl1_list_logic _ _ _ Hs) (cl1_list_logic _ _ _ Ht). clear Hs Ht.
  apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. have E' := imported_eq_to_coq_eq _ _ E.
    by rewrite -(cl1_unmap_map nc sub_nat_to_rocq cce_dc sR) -(cl1_unmap_map nc sub_nat_to_rocq cce_dc tR) E'.
Qed.

Lemma cce_andb_and a b (PA PB : SProp) :
  PropSPropRel (is_true a) PA -> PropSPropRel (is_true b) PB -> PropSPropRel (is_true (a && b)) (And PA PB).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - move=> E. exact (And_intro PA PB (prop_to_sprop _ _ Ha (proj1 (elimT andP E))) (prop_to_sprop _ _ Hb (proj2 (elimT andP E)))).
  - intros [x y]. apply strictly_inhabits. apply/andP. split; [exact (sprop_to_prop _ _ Ha x) | exact (sprop_to_prop _ _ Hb y)].
Qed.

Lemma cce_nondecreasing sR sL (H : CceNlRel sR sL) :
  PropSPropRel (prosa.util.nondecreasing.nondecreasing_sequence sR) (I.Prosa_Util_Nondecreasing_nondecreasing_sequence sL).
Proof.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicConcreteEdfRtaInterface_nondecreasing_sequence_eq sL)).
  apply: ct_forall_nat => n1R n1L H1. apply: ct_forall_nat => n2R n2L H2.
  apply: ct_imp.
  - exact (cce_andb_and _ _ _ _ (sub_nat_le_correspondence _ _ _ _ H1 H2) (sub_nat_lt_correspondence _ _ _ _ H2 (cce_size _ _ H))).
  - exact (sub_nat_le_correspondence _ _ _ _ (cce_nth _ _ H _ _ H1) (cce_nth _ _ H _ _ H2)).
Qed.

Definition CcePpRel (T : Type) (pR : T -> seq nat) (pL : T -> NL) : SProp := forall x, CceNlRel (pR x) (pL x).

Lemma cce_forall_pp (T : Type) (PR : (T -> seq nat) -> Prop) (PL : (T -> NL) -> SProp) :
  (forall pR pL, CcePpRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cce_forall_cover _ _ (CcePpRel T) (fun pR x => cl1_map nc (pR x)) (fun pL x => cl1_unmap sub_nat_to_rocq (pL x))
    (fun pR x => @Lean.eq_refl _ _)
    (fun pL x => coq_eq_to_imported_eq _ _ (cl1_map_unmap nc sub_nat_to_rocq cce_cd (pL x))) PR PL).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LMJobDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> seq nat) (pL : Job -> NL).
Hypothesis Hp : CcePpRel Job pR pL.

Lemma cce_LM_lengths_of_segments j :
  CceNlRel (@ModelWithLimitedPreemptions.lengths_of_segments Job pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_lengths_of_segments Job dJ pL j).
Proof. exact (cce_distances _ _ (Hp j)). Qed.

Lemma cce_LM_job_max_nps j :
  SubNatRel (@ModelWithLimitedPreemptions.job_max_nps Job pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_max_nps Job dJ pL j).
Proof. exact (cce_max0 _ _ (cce_LM_lengths_of_segments j)). Qed.

Lemma cce_LM_job_last_nps j :
  SubNatRel (@ModelWithLimitedPreemptions.job_last_nps Job pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_last_nps Job dJ pL j).
Proof. exact (cce_last0 _ _ (cce_LM_lengths_of_segments j)). Qed.

Lemma cce_LM_can_be_preempted_for_model_with_limited_preemptions j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions Job pR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_can_be_preempted_for_model_with_limited_preemptions Job dJ pL j tL).
Proof. exact (ct_decide_bool _ _ _ (cce_nmem _ _ Ht _ _ (Hp j))). Qed.

Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CceParRel Job cR cL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CceArrRel Job arrR arrL.
Notation ARR := (cce_arrives_in Job arrR arrL Harr).

Lemma cce_LM_job_with_zero_cost_consists_of_one_empty_segment :
  PropSPropRel (@ModelWithLimitedPreemptions.job_with_zero_cost_consists_of_one_empty_segment Job cR arrR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_with_zero_cost_consists_of_one_empty_segment Job dJ cL arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (Hc j) (sub_nat_rel_canonical 0)).
  exact (cce_nl_eq _ _ _ _ (Hp j) (@Lean.eq_refl _ (cl1_map nc [:: 0; 0]))).
Qed.

Lemma cce_LM_last_segment_is_positive :
  PropSPropRel (@ModelWithLimitedPreemptions.last_segment_is_positive Job cR arrR pR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_last_segment_is_positive Job dJ cL arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (cce_LM_job_last_nps j)).
Qed.

Lemma cce_LM_beginning_of_execution_in_preemption_points :
  PropSPropRel (@ModelWithLimitedPreemptions.beginning_of_execution_in_preemption_points Job arrR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_beginning_of_execution_in_preemption_points Job dJ arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (sub_nat_eq_correspondence _ _ _ _ (cce_first0 _ _ (Hp j)) (sub_nat_rel_canonical 0)).
Qed.

Lemma cce_LM_end_of_execution_in_preemption_points :
  PropSPropRel (@ModelWithLimitedPreemptions.end_of_execution_in_preemption_points Job cR arrR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_end_of_execution_in_preemption_points Job dJ cL arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (sub_nat_eq_correspondence _ _ _ _ (cce_last0 _ _ (Hp j)) (Hc j)).
Qed.

Lemma cce_LM_preemption_points_is_nondecreasing_sequence :
  PropSPropRel (@ModelWithLimitedPreemptions.preemption_points_is_nondecreasing_sequence Job arrR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_preemption_points_is_nondecreasing_sequence Job dJ arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (cce_nondecreasing _ _ (Hp j)).
Qed.

Lemma cce_LM_limited_preemptions_job_model :
  PropSPropRel (@ModelWithLimitedPreemptions.limited_preemptions_job_model Job cR arrR pR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_limited_preemptions_job_model Job dJ cL arrL pL).
Proof.
  apply: ct_and; first exact cce_LM_job_with_zero_cost_consists_of_one_empty_segment.
  apply: ct_and; first exact cce_LM_last_segment_is_positive.
  apply: ct_and; first exact cce_LM_beginning_of_execution_in_preemption_points.
  apply: ct_and; first exact cce_LM_end_of_execution_in_preemption_points.
  exact cce_LM_preemption_points_is_nondecreasing_sequence.
Qed.

Lemma cce_LM_is_schedule_with_limited_preemptions sR sL (Hs : CceSchedRel Job sR sL) :
  PropSPropRel (@ModelWithLimitedPreemptions.is_schedule_with_limited_preemptions Job arrR pR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_is_schedule_with_limited_preemptions Job dJ arrL pL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ARR j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _
    (cce_LM_can_be_preempted_for_model_with_limited_preemptions j _ _ (cce_US_service Job sR sL Hs j tR tL Ht)))).
  exact (ct_bool_truth _ _ (cce_US_scheduled_at Job sR sL Hs j tR tL Ht)).
Qed.

End LMJobDefs.

Section LMTaskDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tpR : Task -> seq nat) (tpL : Task -> NL).
Hypothesis Htp : CcePpRel Task tpR tpL.

Lemma cce_LM_task_last_nps tsk :
  SubNatRel (@ModelWithLimitedPreemptions.task_last_nps Task tpR tsk) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_last_nps Task dT tpL tsk).
Proof. exact (cce_last0 _ _ (cce_distances _ _ (Htp tsk))). Qed.

Lemma cce_LM_task_max_nps tsk :
  SubNatRel (@ModelWithLimitedPreemptions.task_max_nps Task tpR tsk) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_max_nps Task dT tpL tsk).
Proof. exact (cce_max0 _ _ (cce_distances _ _ (Htp tsk))). Qed.

Variables (tsR : seq Task) (tsL : I.List Task).
Hypothesis Hts : ClListRel cid tsR tsL.
Notation MEM := (fun tsk => cce_mem Task tsk tsR tsL Hts).

Lemma cce_LM_task_beginning_of_execution_in_preemption_points :
  PropSPropRel (@ModelWithLimitedPreemptions.task_beginning_of_execution_in_preemption_points Task tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_beginning_of_execution_in_preemption_points Task dT tpL tsL).
Proof.
  apply: ct_forall_identity => tsk. apply: ct_imp; first exact (MEM tsk).
  exact (sub_nat_eq_correspondence _ _ _ _ (cce_first0 _ _ (Htp tsk)) (sub_nat_rel_canonical 0)).
Qed.

Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat).
Hypothesis Htc : CceParRel Task tcR tcL.

Lemma cce_LM_task_end_of_execution_in_preemption_points :
  PropSPropRel (@ModelWithLimitedPreemptions.task_end_of_execution_in_preemption_points Task tcR tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_end_of_execution_in_preemption_points Task dT tcL tpL tsL).
Proof.
  apply: ct_forall_identity => tsk. apply: ct_imp; first exact (MEM tsk).
  exact (sub_nat_eq_correspondence _ _ _ _ (cce_last0 _ _ (Htp tsk)) (Htc tsk)).
Qed.

Lemma cce_LM_task_preemption_points_is_nondecreasing_sequence :
  PropSPropRel (@ModelWithLimitedPreemptions.task_preemption_points_is_nondecreasing_sequence Task tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_preemption_points_is_nondecreasing_sequence Task dT tpL tsL).
Proof.
  apply: ct_forall_identity => tsk. apply: ct_imp; first exact (MEM tsk).
  exact (cce_nondecreasing _ _ (Htp tsk)).
Qed.

Lemma cce_LM_task_segments_are_nonempty :
  PropSPropRel (@ModelWithLimitedPreemptions.task_segments_are_nonempty Task tpR tsR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_segments_are_nonempty Task dT tpL tsL).
Proof.
  apply: ct_forall_identity => tsk. apply: ct_forall_nat => nR nL Hn.
  apply: ct_imp; first exact (MEM tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hn (cce_size _ _ (cce_distances _ _ (Htp tsk)))).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical 1) (cce_nth _ _ (cce_distances _ _ (Htp tsk)) _ _ Hn)).
Qed.

End LMTaskDefs.

Section LMJobTaskDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variable job_task : Job -> Task.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CceArrRel Job arrR arrL.
Notation ARR := (cce_arrives_in Job arrR arrL Harr).
Variables (pR : Job -> seq nat) (pL : Job -> NL).
Hypothesis Hp : CcePpRel Job pR pL.
Variables (tpR : Task -> seq nat) (tpL : Task -> NL).
Hypothesis Htp : CcePpRel Task tpR tpL.

Lemma cce_LM_job_consists_of_the_same_number_of_segments_as_task :
  PropSPropRel (@ModelWithLimitedPreemptions.job_consists_of_the_same_number_of_segments_as_task Task Job job_task arrR pR tpR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_consists_of_the_same_number_of_segments_as_task Task dT Job dJ job_task arrL pL tpL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (sub_nat_eq_correspondence _ _ _ _ (cce_size _ _ (Hp j)) (cce_size _ _ (Htp (job_task j)))).
Qed.

Lemma cce_LM_lengths_of_task_segments_bound_length_of_job_segments :
  PropSPropRel (@ModelWithLimitedPreemptions.lengths_of_task_segments_bound_length_of_job_segments Task Job job_task arrR pR tpR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_lengths_of_task_segments_bound_length_of_job_segments Task dT Job dJ job_task arrL pL tpL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => nR nL Hn.
  apply: ct_imp; first exact (ARR j).
  exact (sub_nat_le_correspondence _ _ _ _ (cce_nth _ _ (cce_distances _ _ (Hp j)) _ _ Hn)
    (cce_nth _ _ (cce_distances _ _ (Htp (job_task j))) _ _ Hn)).
Qed.

Variables (tsR : seq Task) (tsL : I.List Task).
Hypothesis Hts : ClListRel cid tsR tsL.
Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat).
Hypothesis Htc : CceParRel Task tcR tcL.

Lemma cce_LM_fixed_preemption_points_task_model :
  PropSPropRel (@ModelWithLimitedPreemptions.fixed_preemption_points_task_model Task tcR Job job_task arrR pR tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_fixed_preemption_points_task_model Task dT tcL Job dJ job_task arrL pL tpL tsL).
Proof.
  apply: ct_and; first exact (cce_LM_task_beginning_of_execution_in_preemption_points Task tpR tpL Htp tsR tsL Hts).
  apply: ct_and; first exact (cce_LM_task_end_of_execution_in_preemption_points Task tpR tpL Htp tsR tsL Hts tcR tcL Htc).
  apply: ct_and; first exact (cce_LM_task_preemption_points_is_nondecreasing_sequence Task tpR tpL Htp tsR tsL Hts).
  apply: ct_and; first exact cce_LM_job_consists_of_the_same_number_of_segments_as_task.
  apply: ct_and; first exact cce_LM_lengths_of_task_segments_bound_length_of_job_segments.
  exact (cce_LM_task_segments_are_nonempty Task tpR tpL Htp tsR tsL Hts).
Qed.

Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CceParRel Job cR cL.

Lemma cce_LM_fixed_preemption_points_model :
  PropSPropRel (@ModelWithLimitedPreemptions.fixed_preemption_points_model Task tcR Job cR job_task arrR pR tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_fixed_preemption_points_model Task dT tcL Job dJ cL job_task arrL pL tpL tsL).
Proof.
  apply: ct_and; first exact (cce_LM_limited_preemptions_job_model Job pR pL Hp cR cL Hc arrR arrL Harr).
  exact cce_LM_fixed_preemption_points_task_model.
Qed.

Variables (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypothesis Htm : CceParRel Task tmR tmL.

Lemma cce_LM_job_max_np_segment_le_task_max_np_segment :
  PropSPropRel (@ModelWithLimitedPreemptions.job_max_np_segment_le_task_max_np_segment Task Job job_task arrR pR tmR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_max_np_segment_le_task_max_np_segment Task dT Job dJ job_task arrL pL tmL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (sub_nat_le_correspondence _ _ _ _ (cce_LM_job_max_nps Job pR pL Hp j) (Htm (job_task j))).
Qed.

Lemma cce_LM_model_with_floating_nonpreemptive_regions :
  PropSPropRel (@ModelWithLimitedPreemptions.model_with_floating_nonpreemptive_regions Task Job cR job_task arrR pR tmR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_model_with_floating_nonpreemptive_regions Task dT Job dJ cL job_task arrL pL tmL).
Proof.
  apply: ct_and; first exact (cce_LM_limited_preemptions_job_model Job pR pL Hp cR cL Hc arrR arrL Harr).
  exact cce_LM_job_max_np_segment_le_task_max_np_segment.
Qed.

End LMJobTaskDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cce_NPM_can_be_preempted_for_fully_nonpreemptive_model (Job : eqType) cR cL (Hc : CceParRel Job cR cL) :
  CcePmRel Job (FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model cR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Nonpreemptive_FullyNonPreemptivePlatform_can_be_preempted_for_fully_nonpreemptive_model Job (ct_decidable_eq Job) cL).
Proof.
  intros j tR tL Ht.
  exact (ct_bool_or _ _ _ _ (ct_decide_eq_nat _ _ _ _ Ht (sub_nat_rel_canonical 0)) (ct_decide_eq_nat _ _ _ _ Ht (Hc j))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cce_PM_can_be_preempted_for_fully_preemptive_model (Job : eqType) :
  CcePmRel Job (FullyPreemptivePlatform.can_be_preempted_for_fully_preemptive_model (Job := Job))
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Preemptive_FullyPreemptivePlatform_can_be_preempted_for_fully_preemptive_model Job (ct_decidable_eq Job)).
Proof. intros j tR tL Ht. exact (ct_bool_canonical true). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(** [min] on [Nat] through [instMinNat] (this export elaborates [min] via the [Min] instance). *)

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem RTAforConcreteModels_blocking_bound_correspondence (Task : eqType) dR dL (Hd : CceParRel Task dR dL)
    tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) tsk mR mL (Hm : CceParRel Task mR mL) :
  SubNatRel (@RTAforConcreteModels.blocking_bound Task dR tsR tsk mR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_NonprReg_ConcreteModels_ResponseTimeBound_RTAforConcreteModels_blocking_bound Task (ct_decidable_eq Task) dL tsL tsk mL).
Proof.
  exact (cce_max_filtered_rel Task _ _ (fun x => ct_bool_and _ _ _ _ (ct_bool_not _ _ (ct_decide_eq Task x tsk)) (ct_decide_lt _ _ _ _ (Hd tsk) (Hd x)))
           _ _ (fun x => ct_sub_rel _ _ _ _ (Hm x) (sub_nat_rel_canonical 1)) tsR tsL Hts).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statement relation search

    [crel] proves a [PropSPropRel P PL] (and the [SubNatRel], [CtBoolRel], [ClListRel] and relation goals it
    generates) by the structure of the source side [P], as in the accepted classic case-study certificates: each
    binder by the cover lemma of its type's relation, each connective by its [LogicalRelation]/base lemma, and
    each atom by the correspondence lemma of its head (above), whose remaining relation premises are hypotheses
    introduced by the binders.  It only chains lemmas proved in this file or its imports; a goal it cannot close
    makes the proof fail. *)

Ltac crel_hyp :=
  match goal with
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CceParRel _ f g |- _ => exact (H x) end
  | |- CtBoolRel (?f ?x ?y) (?g ?x ?y) => match goal with H : CceRelRel _ f g |- _ => exact (H x y) end
  | |- CtBoolRel (?f ?x ?t) (?g ?x ?u) => match goal with H : CcePmRel _ f g |- _ => eapply H end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | ArrivalSequence.arrival_sequence _ => apply: (cce_forall_arr _); intros ? ? ?
  | UniprocessorSchedule.schedule _ => apply: (cce_forall_sched _); intros ? ? ?
  | Priority.FP_policy _ => apply: (cce_forall_rel _); intros ? ? ?
  | Priority.JLFP_policy _ => apply: (cce_forall_rel _); intros ? ? ?
  | seq _ => apply: (cce_forall_list _); intros ? ? ?
  | _ -> seq nat => apply: (cce_forall_pp _); intros ? ? ?
  | _ -> seq Time.time => apply: (cce_forall_pp _); intros ? ? ?
  | _ -> nat -> nat => apply: (cce_forall_curve _); intros ? ? ?
  | _ -> Time.time -> nat => apply: (cce_forall_curve _); intros ? ? ?
  | _ -> nat -> bool => apply: (cce_forall_pm _); intros ? ? ?
  | _ -> Time.time -> bool => apply: (cce_forall_pm _); intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: cce_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp; crel
  | lazymatch goal with
    | |- forall _, _ => intro; crel
    | |- SubNatRel _ (I.Prosa_Classic_Model_Priority_Priority_job_relative_dealine _ _ _ _ _ _ _) => eapply cce_jrd; crel
    | |- CceIntRel _ (JLFPInstantiation.interference _ _) _ => fail; crel
    | |- CceWlRel _ (JLFPInstantiation.interfering_workload _ _ _ _) _ => fail; crel
    | |- CceRelRel _ (Priority.FP_to_JLFP _ _) _ => fail; crel
    | |- CceRelRel _ (Priority.EDF _ _) _ => eapply cce_PR_EDF; crel
    | |- CceIntRel _ (fun _ => _) _ => fail; crel
    | |- CceWlRel _ (fun _ => _) _ => fail; crel
    | |- CceRelRel _ (fun _ => _) _ => first [ fail; crel | eapply cce_PR_EDF; crel | intros ? ?; cbv beta; crel ]
    | |- CtBoolRel (orb _ _) _ => eapply ct_bool_or; crel
    | |- CcePmRel _ (fun _ => _) _ => intros ? ? ? ?; cbv beta; crel
    | |- CcePmRel _ _ _ => first [ assumption | intros ? ? ? ?; cbv beta; crel ]
    | |- CceFunRel _ _ => intros ? ? ?; cbv beta; crel
    | |- CceNatFunRel _ _ => intros ? ? ?; cbv beta; crel
    | |- CceIbfRel _ _ _ => intros ? ? ? ? ? ? ?; cbv beta; crel
    | |- CcePredRel _ _ _ => intro; cbv beta; crel
    | |- CceParRel _ (fun _ => _) _ => intro; cbv beta; crel
    | |- SubNatRel ?a _ => crel_n a
    | |- CtBoolRel ?b _ => crel_b b
    | |- ClListRel _ ?l _ => crel_l l
    | |- PropSPropRel ?P _ => crel_p P
    end ]
with crel_n a :=
  lazymatch a with
  | addn _ _ => eapply sub_add_correspondence; crel
  | subn _ _ => first [ eapply ct_sub_rel; crel | fail; crel ]
  | muln _ _ => first [ fail; crel | eapply sub_mul_correspondence; crel ]
  | S _ => eapply cce_succ_rel; crel
  | _ => first [ exact (sub_nat_rel_canonical _) | crel_n_defs ]
  end
with crel_b b :=
  lazymatch b with
  | andb _ _ => eapply ct_bool_and; crel
  | negb _ => eapply ct_bool_not; crel
  | leq _ _ => first [ eapply ct_decide_lt; crel | eapply ct_decide_le; crel ]
  | @eq_op ?T _ _ => first [ eapply ct_decide_eq_nat; crel | eapply ct_decide_eq; crel ]
  | _ => crel_b_defs
  end
with crel_l l := crel_l_defs
with crel_p P :=
  lazymatch P with
  | forall x : ?T, _ => lazymatch type of T with Prop => eapply ct_imp; crel | _ => crel_intro T; crel end
  | exists x : ?T, _ =>
      tryif crel_isnat T then (apply: ct_exists_nat; intros ? ? ?; crel)
      else (apply: ct_exists_identity; intro; crel)
  | _ /\ _ => eapply ct_and; crel
  | _ <-> _ => eapply cce_iff; crel
  | _ <> _ => eapply cce_ne
  | ~ _ => eapply ct_imp; [crel | exact cce_false_rel]
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else crel_eq_defs
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_eq_defs := first [ eapply ct_eq_rel | fail; crel ]
with crel_n_defs := first [ (match goal with |- context [@RTAforConcreteModels.blocking_bound] => idtac end; eapply RTAforConcreteModels_blocking_bound_correspondence; crel)
    | (match goal with |- context [@MaxArrivalsWorkloadBound.task_request_bound_function] => idtac end; eapply cce_WB_task_request_bound_function; crel)
    | (match goal with |- context [@MaxArrivalsWorkloadBound.total_request_bound_function] => idtac end; eapply cce_WB_total_request_bound_function; crel)
    | eapply cce_ico; crel
    | eapply ct_bool_to_nat; crel
    | eapply cce_sum_filtered_rel; crel
    | eapply cce_sum_rel; crel
    | eapply cce_max_filtered_rel; crel
    | (match goal with |- context [@ModelWithLimitedPreemptions.task_max_nps] => idtac end; eapply cce_LM_task_max_nps; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.task_last_nps] => idtac end; eapply cce_LM_task_last_nps; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.job_max_nps] => idtac end; eapply cce_LM_job_max_nps; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.job_last_nps] => idtac end; eapply cce_LM_job_last_nps; crel)
    | (match goal with |- context [@prosa.util.list.max0] => idtac end; eapply cce_max0; crel)
    | (match goal with |- context [@prosa.util.list.first0] => idtac end; eapply cce_first0; crel)
    | (match goal with |- context [@prosa.util.list.last0] => idtac end; eapply cce_last0; crel)
    | (match goal with |- context [@seq.size] => idtac end; eapply cce_size; crel)
    | (match goal with |- context [@seq.nth] => idtac end; eapply cce_nth; crel)
    | eapply cib_min_rel; crel
    | (match goal with |- context [@UniprocessorSchedule.service] => idtac end; eapply cce_US_service; crel)
    | (match goal with |- context [@UniprocessorSchedule.service_during] => idtac end; eapply cce_US_service_during; crel)
    | (match goal with |- context [@UniprocessorSchedule.service_at] => idtac end; eapply cce_US_service_at; crel) ]
with crel_b_defs := first [ eapply cce_PM_can_be_preempted_for_fully_preemptive_model; crel
    | eapply cce_NPM_can_be_preempted_for_fully_nonpreemptive_model; crel
    | (match goal with |- context [@ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions] => idtac end; eapply cce_LM_can_be_preempted_for_model_with_limited_preemptions; crel)
    | (match goal with |- context [@AbstractRTAforEDFwithArrivalCurves.task_rbf_changes_at] => idtac end; eapply cce_EDF_task_rbf_changes_at; crel)
    | (match goal with |- context [@AbstractRTAforEDFwithArrivalCurves.bound_on_total_hep_workload_changes_at] => idtac end; eapply cce_EDF_bound_on_total_hep_workload_changes_at; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.preemption_time] => idtac end; eapply cce_LPD_preemption_time; crel)
    | (match goal with |- context [@UniprocessorSchedule.scheduled_at] => idtac end; eapply cce_US_scheduled_at; crel)
    | (match goal with |- context [@UniprocessorSchedule.completed_by] => idtac end; eapply cce_US_completed_by; crel)
    | (match goal with |- context [@UniprocessorSchedule.pending] => idtac end; eapply cce_US_pending; crel)
    | (match goal with |- context [@UniprocessorSchedule.backlogged] => idtac end; eapply cce_US_backlogged; crel)
    | (match goal with |- context [@ArrivalSequence.has_arrived] => idtac end; eapply cce_has_arrived; crel)
    | (match goal with |- context [@ArrivalSequence.arrives_at] => idtac end; eapply cce_arrives_at; crel)
    | (match goal with |- context [@Job.job_cost_le_task_cost] => idtac end; eapply cce_J_job_cost_le_task_cost; crel)
    | (match goal with |- context [@TaskArrival.is_job_of_task] => idtac end; eapply cce_TA_is_job_of_task; crel) ]
with crel_l_defs := first [ (match goal with |- context [@ArrivalSequence.jobs_arrived_between] => idtac end; eapply cce_jobs_arrived_between; crel)
    | (match goal with |- context [@ArrivalSequence.jobs_arriving_at] => idtac end; eapply cce_arriving_at; crel)
    | eapply cce_distances; crel
    | eapply cce_LM_lengths_of_segments; crel ]
with crel_p_defs := first [ (match goal with |- context [@LimitedPreemptionPlatform.work_conserving] => idtac end; eapply cce_LP_work_conserving; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.respects_JLFP_policy_at_preemption_point] => idtac end; eapply cce_LPD_respects_JLFP_policy_at_preemption_point; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.work_conserving] => idtac end; eapply cce_LPD_work_conserving; crel)
    | (match goal with |- context [@ArrivalCurves.family_of_proper_arrival_curves] => idtac end; eapply cce_AC_family_of_proper_arrival_curves; crel)
    | (match goal with |- context [@ArrivalCurves.is_arrival_bound] => idtac end; eapply cce_AC_is_arrival_bound; crel)
    | (match goal with |- context [@ArrivalCurves.proper_arrival_curve] => idtac end; eapply cce_AC_proper_arrival_curve; crel)
    | (match goal with |- context [@iff] => idtac end; eapply cce_iff; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.fixed_preemption_points_model] => idtac end; eapply cce_LM_fixed_preemption_points_model; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.is_schedule_with_limited_preemptions] => idtac end; eapply cce_LM_is_schedule_with_limited_preemptions; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.model_with_floating_nonpreemptive_regions] => idtac end; eapply cce_LM_model_with_floating_nonpreemptive_regions; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.limited_preemptions_job_model] => idtac end; eapply cce_LM_limited_preemptions_job_model; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.fixed_preemption_points_task_model] => idtac end; eapply cce_LM_fixed_preemption_points_task_model; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.job_max_np_segment_le_task_max_np_segment] => idtac end; eapply cce_LM_job_max_np_segment_le_task_max_np_segment; crel)
    | (match goal with |- context [@NonpreemptiveSchedule.is_nonpreemptive_schedule] => idtac end; eapply cce_NP_is_nonpreemptive_schedule; crel)
    | (match goal with |- context [@Job.cost_of_jobs_from_arrival_sequence_le_task_cost] => idtac end; eapply cce_J_cost_of_jobs_from_arrival_sequence_le_task_cost; crel)
    | (match goal with |- context [@prosa.util.nondecreasing.nondecreasing_sequence] => idtac end; eapply cce_nondecreasing; crel)
    | eapply cce_nmem; crel
    | (match goal with |- context [@ArrivalSequence.arrives_in] => idtac end; eapply cce_arrives_in; crel)
    | (match goal with |- context [@ArrivalSequence.arrival_times_are_consistent] => idtac end; eapply cce_consistent; crel)
    | (match goal with |- context [@ArrivalSequence.arrival_sequence_is_a_set] => idtac end; eapply cce_is_a_set; crel)
    | eapply cce_mem; crel
    | eapply cce_uniq; crel
    | (match goal with |- context [@UniprocessorSchedule.jobs_come_from_arrival_sequence] => idtac end; eapply cce_US_jobs_come_from_arrival_sequence; crel)
    | (match goal with |- context [@UniprocessorSchedule.jobs_must_arrive_to_execute] => idtac end; eapply cce_US_jobs_must_arrive_to_execute; crel)
    | (match goal with |- context [@UniprocessorSchedule.completed_jobs_dont_execute] => idtac end; eapply cce_US_completed_jobs_dont_execute; crel)
    | (match goal with |- context [@UniprocessorSchedule.sequential_jobs] => idtac end; eapply cce_US_sequential_jobs; crel)
    | (match goal with |- context [@ResponseTime.is_response_time_bound_of_job] => idtac end; eapply cce_RT_is_response_time_bound_of_job; crel)
    | (match goal with |- context [@ResponseTime.is_response_time_bound_of_task] => idtac end; eapply cce_RT_is_response_time_bound_of_task; crel) ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_uniprocessor_response_time_bound_fully_preemptive_edf (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@RTAforConcreteModels.uniprocessor_response_time_bound_fully_preemptive_edf Task p0 p1 Job)).
Definition tgt_uniprocessor_response_time_bound_fully_preemptive_edf (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_NonprReg_ConcreteModels_ResponseTimeBound_RTAforConcreteModels_uniprocessor_response_time_bound_fully_preemptive_edf Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem RTAforConcreteModels_uniprocessor_response_time_bound_fully_preemptive_edf_correspondence (Task Job : eqType) :
  PropSPropRel (src_uniprocessor_response_time_bound_fully_preemptive_edf Task Job) (tgt_uniprocessor_response_time_bound_fully_preemptive_edf Task Job).
Proof. unfold src_uniprocessor_response_time_bound_fully_preemptive_edf, tgt_uniprocessor_response_time_bound_fully_preemptive_edf. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_uniprocessor_response_time_bound_fully_nonpreemptive_edf (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@RTAforConcreteModels.uniprocessor_response_time_bound_fully_nonpreemptive_edf Task p0 p1 Job)).
Definition tgt_uniprocessor_response_time_bound_fully_nonpreemptive_edf (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_NonprReg_ConcreteModels_ResponseTimeBound_RTAforConcreteModels_uniprocessor_response_time_bound_fully_nonpreemptive_edf Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem RTAforConcreteModels_uniprocessor_response_time_bound_fully_nonpreemptive_edf_correspondence (Task Job : eqType) :
  PropSPropRel (src_uniprocessor_response_time_bound_fully_nonpreemptive_edf Task Job) (tgt_uniprocessor_response_time_bound_fully_nonpreemptive_edf Task Job).
Proof. unfold src_uniprocessor_response_time_bound_fully_nonpreemptive_edf, tgt_uniprocessor_response_time_bound_fully_nonpreemptive_edf. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_uniprocessor_response_time_bound_edf_with_fixed_preemption_points (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@RTAforConcreteModels.uniprocessor_response_time_bound_edf_with_fixed_preemption_points Task p0 p1 Job)).
Definition tgt_uniprocessor_response_time_bound_edf_with_fixed_preemption_points (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_NonprReg_ConcreteModels_ResponseTimeBound_RTAforConcreteModels_uniprocessor_response_time_bound_edf_with_fixed_preemption_points Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem RTAforConcreteModels_uniprocessor_response_time_bound_edf_with_fixed_preemption_points_correspondence (Task Job : eqType) :
  PropSPropRel (src_uniprocessor_response_time_bound_edf_with_fixed_preemption_points Task Job) (tgt_uniprocessor_response_time_bound_edf_with_fixed_preemption_points Task Job).
Proof. unfold src_uniprocessor_response_time_bound_edf_with_fixed_preemption_points, tgt_uniprocessor_response_time_bound_edf_with_fixed_preemption_points. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@RTAforConcreteModels.uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions Task p0 p1 Job)).
Definition tgt_uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_NonprReg_ConcreteModels_ResponseTimeBound_RTAforConcreteModels_uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem RTAforConcreteModels_uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions_correspondence (Task Job : eqType) :
  PropSPropRel (src_uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions Task Job) (tgt_uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions Task Job).
Proof. unfold src_uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions, tgt_uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions. crel_spine. crel. Unshelve. all: crel. Qed.
