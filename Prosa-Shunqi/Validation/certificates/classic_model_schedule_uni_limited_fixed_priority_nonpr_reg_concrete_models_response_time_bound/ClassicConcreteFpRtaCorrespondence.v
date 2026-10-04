From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.service classic.model.schedule.uni.workload classic.model.schedule.uni.schedule_of_task classic.model.schedule.uni.limited.busy_interval classic.model.schedule.uni.limited.abstract_RTA.definitions classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta classic.model.schedule.uni.limited.jlfp_instantiation classic.model.schedule.uni.basic.platform classic.model.priority classic.model.schedule.uni.response_time classic.model.schedule.uni.limited.platform.definitions classic.model.schedule.uni.limited.schedule classic.model.schedule.uni.limited.rbf classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space classic.model.arrival.curves.bounds classic.analysis.uni.arrival_curves.workload_bound classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.response_time_bound classic.model.schedule.uni.limited.platform.priority_inversion_is_bounded classic.model.schedule.uni.limited.fixed_priority.response_time_bound classic.model.schedule.uni.nonpreemptive.schedule classic.model.schedule.uni.limited.platform.limited classic.model.schedule.uni.limited.platform.preemptive classic.model.schedule.uni.limited.platform.nonpreemptive classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.concrete_models.response_time_bound.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicConcreteFpRta.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicConcreteFpRtaBase ClassicConcreteFpRtaList ClassicConcreteFpRtaList1.



Module I := ImportedClassicConcreteFpRta.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/fixed_priority/nonpr_reg/concrete_models/response_time_bound.v] (ProsaBuddy classic, commit f692cb7).

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

Lemma ccf_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma ccf_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma ccf_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) ccf_false_rel). Qed.

Lemma ccf_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma ccf_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma ccf_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma ccf_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma ccf_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma ccf_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (ccf_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => ccf_unmap_rel T l) PR PL).
Qed.

Definition CcfParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma ccf_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CcfParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (ccf_forall_cover _ _ (CcfParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint ccf_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (ccf_natl s') end.

Definition ccf_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma ccf_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) ccf_one) (ccf_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) ccf_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (ccf_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma ccf_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (ccf_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (ccf_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma ccf_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma ccf_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma ccf_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma ccf_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH ccf_cl_append. reflexivity.
Qed.

Lemma ccf_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CcfFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma ccf_bigcat_rel (A : Type) fR fL (Hf : CcfFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (ccf_iota_range (nR - mR) 0) ccf_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (ccf_cl_map_ext _ _ Hpt) (ccf_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) ccf_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite ccf_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CcfArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition ccf_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition ccf_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma ccf_arr_canonical aR : CcfArrRel aR (ccf_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /ccf_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma ccf_arr_surjective aL : CcfArrRel (ccf_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma ccf_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CcfArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (ccf_forall_cover _ _ CcfArrRel ccf_arr_to_target ccf_arr_to_source ccf_arr_canonical ccf_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma ccf_jobs_arrived_between aR aL (Ha : CcfArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (ccf_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma ccf_arrives_in aR aL (Ha : CcfArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (ccf_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma ccf_consistent pR pL (Hp : CcfParRel Job pR pL) aR aL (Ha : CcfArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (ccf_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma ccf_is_a_set aR aL (Ha : CcfArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (ccf_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma ccf_arrives_at aR aL (Ha : CcfArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (ccf_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma ccf_has_arrived pR pL (Hp : CcfParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint ccf_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (ccf_snatl s') end.

Lemma ccf_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (ccf_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (ccf_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma ccf_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (ccf_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (ccf_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma ccf_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CcfFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma ccf_fun_canonical FR FL (HF : CcfFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma ccf_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma ccf_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CcfFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ccf_nat_sub_canonical nR mR.
  rewrite ccf_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (ccf_foldr_add FL FR (ccf_fun_canonical FR FL HF)).
  by rewrite ccf_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition ccf_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition ccf_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma ccf_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma ccf_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (ccf_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CcfSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition ccf_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition ccf_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma ccf_sched_canonical sR : CcfSchedRel sR (ccf_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /ccf_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma ccf_sched_surjective sL : CcfSchedRel (ccf_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /ccf_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma ccf_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CcfSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (ccf_forall_cover _ _ CcfSchedRel ccf_sched_to_target ccf_sched_to_source ccf_sched_canonical ccf_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma ccf_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CcfSchedRel Job sR (ccf_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CcfSchedRel Job (ccf_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (ccf_sched_canonical Job) (ccf_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.

Lemma ccf_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (ccf_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (ccf_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma ccf_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (ccf_US_scheduled_at j tR tL Ht)). Qed.

Lemma ccf_service_at_fun j : CcfFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (ccf_US_service_at j kR kL Hk). Qed.

Lemma ccf_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (ccf_ico _ _ _ _ _ _ H1 H2 (ccf_service_at_fun j)). Qed.

Lemma ccf_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (ccf_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma ccf_US_completed_by cR cL (Hc : CcfParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (ccf_US_service j tR tL Ht)). Qed.

Lemma ccf_US_pending aR aL (Ha : CcfParRel Job aR aL) cR cL (Hc : CcfParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ccf_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (ccf_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma ccf_US_backlogged aR aL (Ha : CcfParRel Job aR aL) cR cL (Hc : CcfParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.backlogged aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_backlogged Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ccf_US_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (ccf_US_scheduled_at j tR tL Ht))).
Qed.

Lemma ccf_US_sequential_jobs (Task : eqType) aR aL (Ha : CcfParRel Job aR aL) cR cL (Hc : CcfParRel Job cR cL)
    (job_task : Job -> Task) :
  PropSPropRel (UniprocessorSchedule.sequential_jobs aR cR sR job_task)
    (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_sequential_jobs Job dJ aL cL sL Task (ct_decidable_eq Task) job_task).
Proof.
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_eq Task (job_task j1) (job_task j2))).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha j1) (Ha j2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccf_US_scheduled_at j2 tR tL Ht)).
  exact (ct_bool_truth _ _ (ccf_US_completed_by cR cL Hc j1 tR tL Ht)).
Qed.

Lemma ccf_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CcfArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccf_US_scheduled_at j tR tL Ht)).
  exact (ccf_arrives_in Job arrR arrL Harr j).
Qed.

Lemma ccf_US_jobs_must_arrive_to_execute aR aL (Ha : CcfParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccf_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (ccf_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma ccf_US_completed_jobs_dont_execute cR cL (Hc : CcfParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (ccf_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma ccf_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicConcreteFpRtaInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma ccf_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (ccf_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma ccf_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicConcreteFpRtaInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicConcreteFpRtaInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma ccf_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (ccf_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CcfPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma ccf_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CcfPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (ccf_forall_cover _ _ (CcfPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CcfRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma ccf_rel_canonical (T : Type) (rR : T -> T -> bool) : CcfRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma ccf_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CcfRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma ccf_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CcfRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (ccf_forall_cover _ _ (CcfRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (ccf_rel_canonical T) (ccf_rel_surjective T) PR PL).
Qed.

Definition CcfJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CcfRelRel T (rR tR) (rL tL).

Lemma ccf_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CcfJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma ccf_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CcfJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma ccf_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CcfJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (ccf_forall_cover _ _ (CcfJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (ccf_jldp_canonical T) (ccf_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma ccf_PR_FP_policy :
  And (forall rR : Priority.FP_policy Task, CcfRelRel Task rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_FP_policy Task dT, CcfRelRel Task (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (ccf_rel_canonical Task) (ccf_rel_surjective Task)). Qed.

Lemma ccf_reflexive (T : Type) rR rL (Hr : CcfRelRel T rR rL) :
  PropSPropRel (reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_reflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (Hr x x)). Qed.

Lemma ccf_transitive (T : Type) rR rL (Hr : CcfRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma ccf_PR_FP_is_reflexive rR rL (Hr : CcfRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_reflexive Task dT rL).
Proof. exact (ccf_reflexive Task rR rL Hr). Qed.

Lemma ccf_PR_FP_is_transitive rR rL (Hr : CcfRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_transitive Task dT rL).
Proof. exact (ccf_transitive Task rR rL Hr). Qed.

End PriodefsDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma ccf_J_job_cost_le_task_cost tcR tcL (Htc : CcfParRel Task tcR tcL) cR cL (Hc : CcfParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

Lemma ccf_J_cost_of_jobs_from_arrival_sequence_le_task_cost tcR tcL (Htc : CcfParRel Task tcR tcL)
    cR cL (Hc : CcfParRel Job cR cL) (job_task : Job -> Task) aR aL (Ha : CcfArrRel Job aR aL) :
  PropSPropRel (Job.cost_of_jobs_from_arrival_sequence_le_task_cost tcR cR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_cost_of_jobs_from_arrival_sequence_le_task_cost Task dT tcL Job dJ cL job_task aL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp.
  - apply: ct_exists_nat => tR tL Ht. exact (ccf_mem Job j _ _ (Ha tR tL Ht)).
  - exact (ct_bool_truth _ _ (ccf_J_job_cost_le_task_cost tcR tcL Htc cR cL Hc job_task j)).
Qed.

End JobDefs.

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma ccf_TA_is_job_of_task (job_task : Job -> Task) tsk j :
  CtBoolRel (TaskArrival.is_job_of_task job_task tsk j)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk j).
Proof. exact (ct_decide_eq Task (job_task j) tsk). Qed.

Lemma ccf_TA_arrivals_of_task_between (job_task : Job -> Task) aR aL (Ha : CcfArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_between Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans (cl_filter cid _ (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk)
                            (ccf_TA_is_job_of_task job_task tsk) _) _).
  exact (f_equal (I.List_filter Job (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk))
           (Logic.eq_sym (cl_list_logic _ _ _ (ccf_jobs_arrived_between Job aR aL Ha _ _ _ _ H1 H2)))).
Qed.

Lemma ccf_TA_num_arrivals_of_task (job_task : Job -> Task) aR aL (Ha : CcfArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (TaskArrival.num_arrivals_of_task job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_num_arrivals_of_task Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  have H := ccf_TA_arrivals_of_task_between job_task aR aL Ha tsk _ _ _ _ H1 H2.
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
Definition CcfCurveRel (fR : Task -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk nR nL, SubNatRel nR nL -> SubNatRel (fR tsk nR) (fL tsk nL).

Notation NA := (ccf_TA_num_arrivals_of_task Task Job).

Lemma ccf_AC_is_arrival_bound (job_task : Job -> Task) aR aL (Ha : CcfArrRel Job aR aL)
    mR mL (Hm : CcfCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.is_arrival_bound job_task aR mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_is_arrival_bound Task dT Job dJ job_task aL mL tsk).
Proof.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 H2).
  exact (sub_nat_le_correspondence _ _ _ _ (NA job_task aR aL Ha tsk _ _ _ _ H1 H2) (Hm tsk _ _ (ct_sub_rel _ _ _ _ H2 H1))).
Qed.

Lemma ccf_AC_zero_arrival_curve mR mL (Hm : CcfCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.zero_arrival_curve mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_zero_arrival_curve Task dT mL tsk).
Proof. exact (sub_nat_eq_correspondence _ _ _ _ (Hm tsk _ _ (sub_nat_rel_canonical 0)) (sub_nat_rel_canonical 0)). Qed.

Lemma ccf_AC_monotonic_arrival_curve mR mL (Hm : CcfCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.monotonic_arrival_curve mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_monotonic_arrival_curve Task dT mL tsk).
Proof.
  apply: ct_forall_nat => xR xL Hx. apply: ct_forall_nat => yR yL Hy.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ Hx Hy)).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hm tsk _ _ Hx) (Hm tsk _ _ Hy))).
Qed.

Lemma ccf_AC_proper_arrival_curve (job_task : Job -> Task) aR aL (Ha : CcfArrRel Job aR aL)
    mR mL (Hm : CcfCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.proper_arrival_curve job_task aR mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_proper_arrival_curve Task dT Job dJ job_task aL mL tsk).
Proof.
  apply: ct_and; first exact (ccf_AC_is_arrival_bound job_task aR aL Ha mR mL Hm tsk).
  apply: ct_and; first exact (ccf_AC_zero_arrival_curve mR mL Hm tsk).
  exact (ccf_AC_monotonic_arrival_curve mR mL Hm tsk).
Qed.

Lemma ccf_AC_family_of_proper_arrival_curves (job_task : Job -> Task) aR aL (Ha : CcfArrRel Job aR aL)
    mR mL (Hm : CcfCurveRel mR mL) tsR tsL (Hts : ClListRel cid tsR tsL) :
  PropSPropRel (ArrivalCurves.family_of_proper_arrival_curves job_task aR mR tsR)
    (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_family_of_proper_arrival_curves Task dT Job dJ job_task aL mL tsL).
Proof.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ccf_mem Task tsk _ _ Hts).
  exact (ccf_AC_proper_arrival_curve job_task aR aL Ha mR mL Hm tsk).
Qed.

End AcboundsDefs.

(** * Arrival curves [Task -> time -> nat], with two-way totals *)

Lemma ccf_curve_canonical (Task : eqType) mR : CcfCurveRel Task mR (fun tsk nL => sub_nat_to_imported (mR tsk (sub_nat_to_rocq nL))).
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma ccf_curve_surjective (Task : eqType) mL : CcfCurveRel Task (fun tsk nR => sub_nat_to_rocq (mL tsk (sub_nat_to_imported nR))) mL.
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. exact (sub_nat_rel_surjective _). Qed.

Lemma ccf_forall_curve (Task : eqType) (PR : (Task -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall mR mL, CcfCurveRel Task mR mL -> PropSPropRel (PR mR) (PL mL)) -> PropSPropRel (forall m, PR m) (forall m, PL m).
Proof. exact (ccf_forall_cover _ _ (CcfCurveRel Task) _ _ (ccf_curve_canonical Task) (ccf_curve_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section AcwbDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat).
Hypothesis Htc : CcfParRel Task tcR tcL.
Variables (mR : Task -> nat -> nat) (mL : Task -> Lean.Nat -> Lean.Nat).
Hypothesis Hm : CcfCurveRel Task mR mL.

Lemma ccf_WB_task_request_bound_function tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.task_request_bound_function tcR mR tsk dR) (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_task_request_bound_function Task dT tcL mL tsk dL).
Proof. exact (sub_mul_correspondence _ _ _ _ (Htc tsk) (Hm tsk _ _ Hd)). Qed.

Notation TRBF := ccf_WB_task_request_bound_function.

Lemma ccf_WB_total_hep_request_bound_function_FP hR hL (Hh : CcfRelRel Task hR hL)
    tsR tsL (Hts : ClListRel cid tsR tsL) tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.total_hep_request_bound_function_FP tcR hR mR tsR tsk dR)
    (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_total_hep_request_bound_function_FP Task dT tcL hL mL tsL tsk dL).
Proof. exact (ccf_sum_filtered_rel Task _ _ (fun x => TRBF x dR dL Hd) _ _ (fun x => Hh x tsk) _ _ Hts). Qed.

Lemma ccf_WB_total_ohep_request_bound_function_FP hR hL (Hh : CcfRelRel Task hR hL)
    tsR tsL (Hts : ClListRel cid tsR tsL) tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.total_ohep_request_bound_function_FP tcR hR mR tsR tsk dR)
    (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_total_ohep_request_bound_function_FP Task dT tcL hL mL tsL tsk dL).
Proof.
  exact (ccf_sum_filtered_rel Task _ _ (fun x => TRBF x dR dL Hd) _ _
           (fun x => ct_bool_and _ _ _ _ (Hh x tsk) (ct_bool_not _ _ (ct_decide_eq Task x tsk))) _ _ Hts).
Qed.

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
Hypothesis Hs : CcfSchedRel Job sR sL.

Lemma ccf_RT_is_response_time_bound_of_job aR aL (Ha : CcfParRel Job aR aL) cR cL (Hc : CcfParRel Job cR cL)
    j rR rL (Hr : SubNatRel rR rL) :
  CtBoolRel (ResponseTime.is_response_time_bound_of_job aR cR sR j rR) (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_job Job dJ aL cL sL j rL).
Proof. exact (ccf_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr)). Qed.

Lemma ccf_RT_is_response_time_bound_of_task aR aL (Ha : CcfParRel Job aR aL) cR cL (Hc : CcfParRel Job cR cL)
    (job_task : Job -> Task) arrR arrL (Harr : CcfArrRel Job arrR arrL) tsk rR rL (Hr : SubNatRel rR rL) :
  PropSPropRel (ResponseTime.is_response_time_bound_of_task aR cR job_task arrR sR tsk rR)
    (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_task Task dT Job dJ aL cL job_task arrL sL tsk rL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ccf_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (ccf_RT_is_response_time_bound_of_job aR aL Ha cR cL Hc j rR rL Hr)).
Qed.

End UrtDefs.

Lemma ccf_NP_is_nonpreemptive_schedule (Job : eqType) sR sL (Hs : CcfSchedRel Job sR sL)
    cR cL (Hc : CcfParRel Job cR cL) :
  PropSPropRel (NonpreemptiveSchedule.is_nonpreemptive_schedule cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Nonpreemptive_Schedule_NonpreemptiveSchedule_is_nonpreemptive_schedule Job (ct_decidable_eq Job) cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht Ht').
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccf_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (ccf_US_completed_by Job sR sL Hs cR cL Hc j t'R t'L Ht'))).
  exact (ct_bool_truth _ _ (ccf_US_scheduled_at Job sR sL Hs j t'R t'L Ht')).
Qed.

Section UplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.

Lemma ccf_UP_work_conserving aR aL (Ha : CcfParRel Job aR aL) cR cL (Hc : CcfParRel Job cR cL)
    arrR arrL (Harr : CcfArrRel Job arrR arrL) :
  PropSPropRel (Platform.work_conserving aR cR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Basic_Platform_Platform_work_conserving Job dJ aL cL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ccf_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccf_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (ccf_US_scheduled_at Job sR sL Hs j_other tR tL Ht)).
Qed.

End UplatDefs.

Lemma ccf_iff (P Q : Prop) (PL QL : SProp) :
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
Definition CcfPmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma ccf_pm_canonical pR : CcfPmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma ccf_pm_surjective pL : CcfPmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma ccf_forall_pm (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CcfPmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (ccf_forall_cover _ _ CcfPmRel _ _ ccf_pm_canonical ccf_pm_surjective PR PL). Qed.

End LpdefsPmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LpdefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CcfPmRel Job pR pL.

Notation SA := (ccf_US_scheduled_at Job sR sL Hs).
Notation SV := (ccf_US_service Job sR sL Hs).

Lemma ccf_LP_preemption_time tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_preemption_time Job dJ sL pL tL).
Proof.
  refine (ccf_trs (Hs tR tL Ht)
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
Hypothesis Hp : CcfPmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : CcfParRel Job cR cL) (Hm : CcfParRel Job mR mL) (Htm : CcfParRel Task tmR tmL).

End LpdefsDefs2.

Lemma ccf_getD (T : Type) (s : seq T) sL (Hs : ClListRel cid s sL) (x0 : T) nR nL (Hn : SubNatRel nR nL) :
  Logic.eq (I.List_getD T sL nL x0) (nth x0 s nR).
Proof.
  rewrite (cl_list_logic _ _ _ Hs) (cl_nat_logic _ _ Hn). exact (Logic.eq_sym (cl_nth cid x0 s nR)).
Qed.

Lemma ccf_pred_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ct_sub nL (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Hn. apply: coq_eq_to_imported_eq. rewrite -subn1.
  exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Relations *)

Lemma ccf_eq_transport (T : Type) (a b : T) aL bL : Lean.eq a aL -> Lean.eq b bL ->
  PropSPropRel (Logic.eq a b) (Lean.eq aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (ct_eq_rel T a b). Qed.

(** Functions [nat -> T] (identical values) and [nat -> nat] (values by [SubNatRel]), pointwise on related arguments. *)
Definition CcfRsFunRel (T : Type) (fR : nat -> T) (fL : Lean.Nat -> T) : SProp :=
  forall nR nL, SubNatRel nR nL -> Lean.eq (fR nR) (fL nL).
Definition CcfNatFunRel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) : SProp :=
  forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

(** Interference bound functions [Task -> time -> time -> time], pointwise on related arguments and values. *)
Definition CcfIbfRel (Task : Type) (fR : Task -> nat -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk, forall aR aL, SubNatRel aR aL -> CcfNatFunRel (fR tsk aR) (fL tsk aL).

Definition ccf_ibf_to_target (Task : Type) (fR : Task -> nat -> nat -> nat) : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat :=
  fun tsk aL xL => sub_nat_to_imported (fR tsk (sub_nat_to_rocq aL) (sub_nat_to_rocq xL)).
Definition ccf_ibf_to_source (Task : Type) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : Task -> nat -> nat -> nat :=
  fun tsk aR xR => sub_nat_to_rocq (fL tsk (sub_nat_to_imported aR) (sub_nat_to_imported xR)).

Lemma ccf_ibf_canonical (Task : Type) fR : CcfIbfRel Task fR (ccf_ibf_to_target Task fR).
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  unfold ccf_ibf_to_target. rewrite !sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma ccf_ibf_surjective (Task : Type) fL : CcfIbfRel Task (ccf_ibf_to_source Task fL) fL.
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma ccf_forall_ibf (Task : Type) (PR : (Task -> nat -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, CcfIbfRel Task fR fL -> PropSPropRel (PR fR) (PL fL)) -> PropSPropRel (forall f, PR f) (forall f, PL f).
Proof. exact (ccf_forall_cover _ _ (CcfIbfRel Task) (ccf_ibf_to_target Task) (ccf_ibf_to_source Task) (ccf_ibf_canonical Task) (ccf_ibf_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(* ------------------------------------------------------------------ *)
(** * Interference predicates and interfering workloads *)

Section NPRJISEQARDIRel.
Variable Job : eqType.

Definition CcfIntRel (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (iR j tR) (iL j tL).

Lemma ccf_int_canonical iR : CcfIntRel iR (fun j tL => ct_b2l (iR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma ccf_int_surjective iL : CcfIntRel (fun j tR => ct_l2b (iL j (sub_nat_to_imported tR))) iL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma ccf_forall_int (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall iR iL, CcfIntRel iR iL -> PropSPropRel (PR iR) (PL iL)) -> PropSPropRel (forall i, PR i) (forall i, PL i).
Proof. exact (ccf_forall_cover _ _ CcfIntRel _ _ ccf_int_canonical ccf_int_surjective PR PL). Qed.

Definition CcfWlRel (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (wR j tR) (wL j tL).

Lemma ccf_wl_canonical wR : CcfWlRel wR (fun j tL => sub_nat_to_imported (wR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma ccf_wl_surjective wL : CcfWlRel (fun j tR => sub_nat_to_rocq (wL j (sub_nat_to_imported tR))) wL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (sub_nat_rel_surjective _). Qed.

Lemma ccf_forall_wl (PR : (Job -> nat -> nat) -> Prop) (PL : (Job -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall wR wL, CcfWlRel wR wL -> PropSPropRel (PR wR) (PL wL)) -> PropSPropRel (forall w, PR w) (forall w, PL w).
Proof. exact (ccf_forall_cover _ _ CcfWlRel _ _ ccf_wl_canonical ccf_wl_surjective PR PL). Qed.

End NPRJISEQARDIRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section NPRJISEQARDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Section NPRJISEQARDSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CcfParRel Job aR aL) (Hc : CcfParRel Job cR cL).
Variables (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat).
Hypotheses (Hi : CcfIntRel Job iR iL) (Hw : CcfWlRel Job wR wL).

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
Hypothesis Hc : CcfParRel Job cR cL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CcfArrRel Job arrR arrL.
Variables (lR : Job -> nat) (lL : Job -> Lean.Nat).
Hypothesis Hl : CcfParRel Job lR lL.

Section NPRJISEQLSSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.

End NPRJISEQLSSched.

Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat) (tlR : Task -> nat) (tlL : Task -> Lean.Nat).
Hypotheses (Htc : CcfParRel Task tcR tcL) (Htl : CcfParRel Task tlR tlL).

End NPRJISEQLSDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section NPRJISEQSVDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.

End NPRJISEQSVDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section NPRJISEQSTDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.
Variable job_task : Job -> Task.

End NPRJISEQSTDefs.

(* ------------------------------------------------------------------ *)
(** * [has] against [List.any] *)

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(* ------------------------------------------------------------------ *)
(** * Service of jobs (as in the accepted classic uniprocessor service certificate) *)

Section NPRJILBISvc.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.

End NPRJILBISvc.

(* ------------------------------------------------------------------ *)
(** * Auxiliary relations *)

Lemma ccf_implb aR aL (Ha : CtBoolRel aR aL) bR bL (Hb : CtBoolRel bR bL) :
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
Hypotheses (Hja : CcfParRel Job jaR jaL) (Hc : CcfParRel Job cR cL).
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CcfArrRel Job aR aL.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.
Variables (hR : Job -> Job -> bool) (hL : Job -> Job -> I.Bool).
Hypothesis Hh : CcfRelRel Job hR hL.

Lemma ccf_LP_work_conserving :
  PropSPropRel (LimitedPreemptionPlatform.work_conserving jaR cR aR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_work_conserving Job dJ jaL cL aL sL).
Proof. exact (ccf_UP_work_conserving Job sR sL Hs jaR jaL Hja cR cL Hc aR aL Ha). Qed.

End NPRJILBIDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma ccf_arriving_at (Job : eqType) aR aL (Ha : CcfArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arriving_at aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arriving_at Job (ct_decidable_eq Job) aL tL).
Proof. exact (Ha tR tL Ht). Qed.

Section NPRJIDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.
Variables (hR : Job -> Job -> bool) (hL : Job -> Job -> I.Bool).
Hypothesis Hh : CcfRelRel Job hR hL.
Variable job_task : Job -> Task.

Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CcfParRel Job cR cL.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CcfArrRel Job aR aL.

End NPRJIDefs.

(* ------------------------------------------------------------------ *)
(** * Preemption models *)

Section NPRLPDPmRel.
Variable Job : eqType.
Definition CcfPmRel__NPRLPDPmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma ccf_pm_canonical__NPRLPDPmRel pR : CcfPmRel__NPRLPDPmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma ccf_pm_surjective__NPRLPDPmRel pL : CcfPmRel__NPRLPDPmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma ccf_forall_pm__NPRLPDPmRel (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CcfPmRel__NPRLPDPmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (ccf_forall_cover _ _ CcfPmRel__NPRLPDPmRel _ _ ccf_pm_canonical__NPRLPDPmRel ccf_pm_surjective__NPRLPDPmRel PR PL). Qed.

End NPRLPDPmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section NPRLPDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CcfPmRel Job pR pL.

Notation SA := (ccf_US_scheduled_at Job sR sL Hs).
Notation SV := (ccf_US_service Job sR sL Hs).

Lemma ccf_LPD_preemption_time tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_preemption_time Job dJ sL pL tL).
Proof.
  refine (ccf_trs (Hs tR tL Ht)
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
Hypothesis Hp : CcfPmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : CcfParRel Job cR cL) (Hm : CcfParRel Job mR mL) (Htm : CcfParRel Task tmR tmL).

End NPRLPDDefs2.

Lemma ccf_LPD_work_conserving (Job : eqType) sR sL (Hs : CcfSchedRel Job sR sL) cR cL (Hc : CcfParRel Job cR cL)
    c0R c0L (Hc0 : CcfParRel Job c0R c0L) arrR arrL (Harr : CcfArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.work_conserving cR c0R arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_work_conserving Job (ct_decidable_eq Job) cL c0L arrL sL).
Proof. exact (ccf_UP_work_conserving Job sR sL Hs cR cL Hc c0R c0L Hc0 arrR arrL Harr). Qed.

Section NPRLPDResp.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CcfParRel Job aR aL) (Hc : CcfParRel Job cR cL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CcfArrRel Job arrR arrL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CcfPmRel Job pR pL.

Lemma ccf_LPD_respects_FP_policy_at_preemption_point (job_task : Job -> Task) hR hL (Hh : CcfRelRel Task hR hL) :
  PropSPropRel (LimitedPreemptionPlatform.respects_FP_policy_at_preemption_point aR cR job_task arrR sR pR hR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_respects_FP_policy_at_preemption_point Task dT Job dJ aL cL job_task arrL sL pL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccf_LPD_preemption_time Job sR sL Hs pR pL Hp tR tL Ht)).
  apply: ct_imp; first exact (ccf_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccf_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccf_US_scheduled_at Job sR sL Hs j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh (job_task j_hp) (job_task j))).
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

Lemma ccf_foldr_max_cond : forall s : seq X,
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

Lemma ccf_max_filtered_rel s sL (Hs : ClListRel cid s sL) :
  SubNatRel (\max_(x <- s | PR x) FR x) (I.Prosa_Util_Sum_maxFiltered X sL PL FL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite -(imported_eq_to_coq_eq _ _ Hs).
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_maxFiltered_eq_foldr_cond X PL FL (cl_map cid s))).
  exact (Logic.eq_sym (ccf_foldr_max_cond s)).
Qed.

End NPRPIBMaxSeq.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(* ------------------------------------------------------------------ *)
(** * Preemption models *)

Section LMLPDPmRel.
Variable Job : eqType.
Definition CcfPmRel__LMLPDPmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma ccf_pm_canonical__LMLPDPmRel pR : CcfPmRel__LMLPDPmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma ccf_pm_surjective__LMLPDPmRel pL : CcfPmRel__LMLPDPmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma ccf_forall_pm__LMLPDPmRel (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CcfPmRel__LMLPDPmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (ccf_forall_cover _ _ CcfPmRel__LMLPDPmRel _ _ ccf_pm_canonical__LMLPDPmRel ccf_pm_surjective__LMLPDPmRel PR PL). Qed.

End LMLPDPmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LMLPDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CcfPmRel Job pR pL.

Notation SA := (ccf_US_scheduled_at Job sR sL Hs).
Notation SV := (ccf_US_service Job sR sL Hs).

Lemma ccf_LPD_preemption_time__LMLPDDefs tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_preemption_time Job dJ sL pL tL).
Proof.
  refine (ccf_trs (Hs tR tL Ht)
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
Hypothesis Hp : CcfPmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : CcfParRel Job cR cL) (Hm : CcfParRel Job mR mL) (Htm : CcfParRel Task tmR tmL).

End LMLPDDefs2.

Section LMLPDResp.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CcfSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CcfParRel Job aR aL) (Hc : CcfParRel Job cR cL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CcfArrRel Job arrR arrL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CcfPmRel Job pR pL.

Lemma ccf_LPD_respects_FP_policy_at_preemption_point__LMLPDResp (job_task : Job -> Task) hR hL (Hh : CcfRelRel Task hR hL) :
  PropSPropRel (LimitedPreemptionPlatform.respects_FP_policy_at_preemption_point aR cR job_task arrR sR pR hR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_respects_FP_policy_at_preemption_point Task dT Job dJ aL cL job_task arrL sL pL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccf_LPD_preemption_time Job sR sL Hs pR pL Hp tR tL Ht)).
  apply: ct_imp; first exact (ccf_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccf_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ccf_US_scheduled_at Job sR sL Hs j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh (job_task j_hp) (job_task j))).
Qed.

End LMLPDResp.

(* ------------------------------------------------------------------ *)
(** * Nat lists (universe instance [List_inst1]) through the Nat embedding *)

Notation NL := (I.List_inst1 Lean.Nat).
Notation nc := sub_nat_to_imported.
Definition CcfNlRel (sR : seq nat) (sL : NL) : SProp := ClListRel1 sub_nat_to_imported sR sL.

Lemma ccf_dc x : Logic.eq (sub_nat_to_rocq (sub_nat_to_imported x)) x.
Proof. exact (sub_nat_rocq_roundtrip x). Qed.
Lemma ccf_cd y : Logic.eq (sub_nat_to_imported (sub_nat_to_rocq y)) y.
Proof. exact (imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip y)). Qed.

Notation EQ H := (imported_eq_to_coq_eq _ _ H).

Lemma ccf_distances_eq : forall s,
  Logic.eq (cl1_map nc (prosa.util.nondecreasing.distances s)) (I.Prosa_Util_Nondecreasing_distances (cl1_map nc s)).
Proof.
  elim => [|x s IH]; first exact (Logic.eq_sym (EQ I.Prosa_Validation_ClassicConcreteFpRtaInterface_distances_nil)).
  case: s IH => [|y ys] IH; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_distances_single (nc x)))).
  rewrite (EQ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_distances_cons2 (nc x) (nc y) (cl1_map nc ys))).
  have Hs : Logic.eq (prosa.util.nondecreasing.distances [:: x, y & ys]) ((y - x) :: prosa.util.nondecreasing.distances (y :: ys)) by rewrite /prosa.util.nondecreasing.distances /= drop0.
  rewrite Hs.
  change (Logic.eq (I.List_cons_inst1 Lean.Nat (nc (y - x)) (cl1_map nc (prosa.util.nondecreasing.distances (y :: ys))))
    (I.List_cons_inst1 Lean.Nat (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat) (nc y) (nc x))
       (I.Prosa_Util_Nondecreasing_distances (cl1_map nc (y :: ys))))).
  rewrite -IH. exact (f_equal (fun z => I.List_cons_inst1 Lean.Nat z (cl1_map nc (prosa.util.nondecreasing.distances (y :: ys))))
    (EQ (ct_sub_rel _ _ _ _ (sub_nat_rel_canonical y) (sub_nat_rel_canonical x)))).
Qed.

Lemma ccf_distances sR sL : CcfNlRel sR sL -> CcfNlRel (prosa.util.nondecreasing.distances sR) (I.Prosa_Util_Nondecreasing_distances sL).
Proof.
  intro H. exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (ccf_distances_eq sR))
    (sub_imported_eq_congr I.Prosa_Util_Nondecreasing_distances _ _ H)).
Qed.

Lemma ccf_foldl_max_eq : forall s z,
  Logic.eq (nc (seq.foldl maxn z s)) (I.List_foldl_inst3 Lean.Nat Lean.Nat I.Nat_max (nc z) (cl1_map nc s)).
Proof.
  elim => [|x s IH] z; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_foldl_max_nil (nc z)))).
  rewrite (EQ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_foldl_max_cons (nc z) (nc x) (cl1_map nc s))).
  rewrite -(EQ (ct_max_rel _ _ _ _ (sub_nat_rel_canonical z) (sub_nat_rel_canonical x))).
  exact (IH (maxn z x)).
Qed.

Lemma ccf_max0 sR sL : CcfNlRel sR sL -> SubNatRel (prosa.util.list.max0 sR) (I.Prosa_Util_List_max0 sL).
Proof.
  intro H.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_max0_eq sL))).
  exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (ccf_foldl_max_eq sR 0))
    (sub_imported_eq_congr (fun l => I.List_foldl_inst3 Lean.Nat Lean.Nat I.Nat_max (nc 0) l) _ _ H)).
Qed.

Lemma ccf_first0_eq s : Logic.eq (nc (prosa.util.list.first0 s)) (I.Prosa_Util_List_first0 (cl1_map nc s)).
Proof.
  case: s => [|x s]; first exact (Logic.eq_sym (EQ I.Prosa_Validation_ClassicConcreteFpRtaInterface_first0_nil)).
  exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_first0_cons (nc x) (cl1_map nc s)))).
Qed.

Lemma ccf_first0 sR sL : CcfNlRel sR sL -> SubNatRel (prosa.util.list.first0 sR) (I.Prosa_Util_List_first0 sL).
Proof.
  intro H. exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (ccf_first0_eq sR))
    (sub_imported_eq_congr I.Prosa_Util_List_first0 _ _ H)).
Qed.

Lemma ccf_last0_eq : forall s, Logic.eq (nc (prosa.util.list.last0 s)) (I.Prosa_Util_List_last0 (cl1_map nc s)).
Proof.
  elim => [|x s IH]; first exact (Logic.eq_sym (EQ I.Prosa_Validation_ClassicConcreteFpRtaInterface_last0_nil)).
  case: s IH => [|y ys] IH; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_last0_single (nc x)))).
  rewrite (EQ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_last0_cons2 (nc x) (nc y) (cl1_map nc ys))).
  exact IH.
Qed.

Lemma ccf_last0 sR sL : CcfNlRel sR sL -> SubNatRel (prosa.util.list.last0 sR) (I.Prosa_Util_List_last0 sL).
Proof.
  intro H. exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (ccf_last0_eq sR))
    (sub_imported_eq_congr I.Prosa_Util_List_last0 _ _ H)).
Qed.

Lemma ccf_nth_eq : forall s n,
  Logic.eq (nc (seq.nth 0 s n)) (I.List_getD_inst1 Lean.Nat (cl1_map nc s) (nc n) (nc 0)).
Proof.
  elim => [|x s IH] n; first by case: n => [|n]; exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_getD_nil _ (nc 0)))).
  case: n => [|n]; first exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_getD_cons_zero (nc x) (cl1_map nc s) (nc 0)))).
  exact (Logic.eq_trans (IH n) (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_getD_cons_succ (nc x) (cl1_map nc s) (nc n) (nc 0))))).
Qed.

Lemma ccf_nth sR sL (H : CcfNlRel sR sL) nR nL (Hn : SubNatRel nR nL) :
  SubNatRel (seq.nth 0 sR nR) (I.List_getD_inst1 Lean.Nat sL nL (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))).
Proof.
  exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (ccf_nth_eq sR nR))
    (sub_imported_eq_congr2 (fun l m => I.List_getD_inst1 Lean.Nat l m (nc 0)) _ _ _ _ H Hn)).
Qed.

Lemma ccf_size_eq : forall s, Logic.eq (nc (seq.size s)) (I.List_length_inst1 Lean.Nat (cl1_map nc s)).
Proof.
  elim => [|x s IH]; first exact (Logic.eq_sym (EQ I.Prosa_Validation_ClassicConcreteFpRtaInterface_length_nil)).
  rewrite (EQ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_length_cons (nc x) (cl1_map nc s))) -IH. reflexivity.
Qed.

Lemma ccf_size sR sL : CcfNlRel sR sL -> SubNatRel (seq.size sR) (I.List_length_inst1 Lean.Nat sL).
Proof.
  intro H. exact (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (ccf_size_eq sR))
    (sub_imported_eq_congr (I.List_length_inst1 Lean.Nat) _ _ H)).
Qed.

Lemma ccf_nmem xR xL (Hx : SubNatRel xR xL) sR sL (H : CcfNlRel sR sL) :
  PropSPropRel (xR \in sR)
    (I.Membership_mem_inst3 Lean.Nat NL (I.List_instMembership_inst1 Lean.Nat) sL xL).
Proof.
  rewrite (cl_nat_logic _ _ Hx).
  exact (cl1_mem_rel_list _ Lean.Nat sub_nat_to_imported sub_nat_to_rocq ccf_dc xR sR sL H).
Qed.

Lemma ccf_nl_eq sR sL tR tL (Hs : CcfNlRel sR sL) (Ht : CcfNlRel tR tL) :
  PropSPropRel (Logic.eq sR tR) (Lean.eq sL tL).
Proof.
  rewrite (cl1_list_logic _ _ _ Hs) (cl1_list_logic _ _ _ Ht). clear Hs Ht.
  apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. have E' := imported_eq_to_coq_eq _ _ E.
    by rewrite -(cl1_unmap_map nc sub_nat_to_rocq ccf_dc sR) -(cl1_unmap_map nc sub_nat_to_rocq ccf_dc tR) E'.
Qed.

Lemma ccf_andb_and a b (PA PB : SProp) :
  PropSPropRel (is_true a) PA -> PropSPropRel (is_true b) PB -> PropSPropRel (is_true (a && b)) (And PA PB).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - move=> E. exact (And_intro PA PB (prop_to_sprop _ _ Ha (proj1 (elimT andP E))) (prop_to_sprop _ _ Hb (proj2 (elimT andP E)))).
  - intros [x y]. apply strictly_inhabits. apply/andP. split; [exact (sprop_to_prop _ _ Ha x) | exact (sprop_to_prop _ _ Hb y)].
Qed.

Lemma ccf_nondecreasing sR sL (H : CcfNlRel sR sL) :
  PropSPropRel (prosa.util.nondecreasing.nondecreasing_sequence sR) (I.Prosa_Util_Nondecreasing_nondecreasing_sequence sL).
Proof.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicConcreteFpRtaInterface_nondecreasing_sequence_eq sL)).
  apply: ct_forall_nat => n1R n1L H1. apply: ct_forall_nat => n2R n2L H2.
  apply: ct_imp.
  - exact (ccf_andb_and _ _ _ _ (sub_nat_le_correspondence _ _ _ _ H1 H2) (sub_nat_lt_correspondence _ _ _ _ H2 (ccf_size _ _ H))).
  - exact (sub_nat_le_correspondence _ _ _ _ (ccf_nth _ _ H _ _ H1) (ccf_nth _ _ H _ _ H2)).
Qed.

Definition CcfPpRel (T : Type) (pR : T -> seq nat) (pL : T -> NL) : SProp := forall x, CcfNlRel (pR x) (pL x).

Lemma ccf_forall_pp (T : Type) (PR : (T -> seq nat) -> Prop) (PL : (T -> NL) -> SProp) :
  (forall pR pL, CcfPpRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (ccf_forall_cover _ _ (CcfPpRel T) (fun pR x => cl1_map nc (pR x)) (fun pL x => cl1_unmap sub_nat_to_rocq (pL x))
    (fun pR x => @Lean.eq_refl _ _)
    (fun pL x => coq_eq_to_imported_eq _ _ (cl1_map_unmap nc sub_nat_to_rocq ccf_cd (pL x))) PR PL).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LMJobDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> seq nat) (pL : Job -> NL).
Hypothesis Hp : CcfPpRel Job pR pL.

Lemma ccf_LM_lengths_of_segments j :
  CcfNlRel (@ModelWithLimitedPreemptions.lengths_of_segments Job pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_lengths_of_segments Job dJ pL j).
Proof. exact (ccf_distances _ _ (Hp j)). Qed.

Lemma ccf_LM_job_max_nps j :
  SubNatRel (@ModelWithLimitedPreemptions.job_max_nps Job pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_max_nps Job dJ pL j).
Proof. exact (ccf_max0 _ _ (ccf_LM_lengths_of_segments j)). Qed.

Lemma ccf_LM_job_last_nps j :
  SubNatRel (@ModelWithLimitedPreemptions.job_last_nps Job pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_last_nps Job dJ pL j).
Proof. exact (ccf_last0 _ _ (ccf_LM_lengths_of_segments j)). Qed.

Lemma ccf_LM_can_be_preempted_for_model_with_limited_preemptions j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions Job pR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_can_be_preempted_for_model_with_limited_preemptions Job dJ pL j tL).
Proof. exact (ct_decide_bool _ _ _ (ccf_nmem _ _ Ht _ _ (Hp j))). Qed.

Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CcfParRel Job cR cL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CcfArrRel Job arrR arrL.
Notation ARR := (ccf_arrives_in Job arrR arrL Harr).

Lemma ccf_LM_job_with_zero_cost_consists_of_one_empty_segment :
  PropSPropRel (@ModelWithLimitedPreemptions.job_with_zero_cost_consists_of_one_empty_segment Job cR arrR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_with_zero_cost_consists_of_one_empty_segment Job dJ cL arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (Hc j) (sub_nat_rel_canonical 0)).
  exact (ccf_nl_eq _ _ _ _ (Hp j) (@Lean.eq_refl _ (cl1_map nc [:: 0; 0]))).
Qed.

Lemma ccf_LM_last_segment_is_positive :
  PropSPropRel (@ModelWithLimitedPreemptions.last_segment_is_positive Job cR arrR pR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_last_segment_is_positive Job dJ cL arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (ccf_LM_job_last_nps j)).
Qed.

Lemma ccf_LM_beginning_of_execution_in_preemption_points :
  PropSPropRel (@ModelWithLimitedPreemptions.beginning_of_execution_in_preemption_points Job arrR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_beginning_of_execution_in_preemption_points Job dJ arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (sub_nat_eq_correspondence _ _ _ _ (ccf_first0 _ _ (Hp j)) (sub_nat_rel_canonical 0)).
Qed.

Lemma ccf_LM_end_of_execution_in_preemption_points :
  PropSPropRel (@ModelWithLimitedPreemptions.end_of_execution_in_preemption_points Job cR arrR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_end_of_execution_in_preemption_points Job dJ cL arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (sub_nat_eq_correspondence _ _ _ _ (ccf_last0 _ _ (Hp j)) (Hc j)).
Qed.

Lemma ccf_LM_preemption_points_is_nondecreasing_sequence :
  PropSPropRel (@ModelWithLimitedPreemptions.preemption_points_is_nondecreasing_sequence Job arrR pR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_preemption_points_is_nondecreasing_sequence Job dJ arrL pL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (ccf_nondecreasing _ _ (Hp j)).
Qed.

Lemma ccf_LM_limited_preemptions_job_model :
  PropSPropRel (@ModelWithLimitedPreemptions.limited_preemptions_job_model Job cR arrR pR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_limited_preemptions_job_model Job dJ cL arrL pL).
Proof.
  apply: ct_and; first exact ccf_LM_job_with_zero_cost_consists_of_one_empty_segment.
  apply: ct_and; first exact ccf_LM_last_segment_is_positive.
  apply: ct_and; first exact ccf_LM_beginning_of_execution_in_preemption_points.
  apply: ct_and; first exact ccf_LM_end_of_execution_in_preemption_points.
  exact ccf_LM_preemption_points_is_nondecreasing_sequence.
Qed.

Lemma ccf_LM_is_schedule_with_limited_preemptions sR sL (Hs : CcfSchedRel Job sR sL) :
  PropSPropRel (@ModelWithLimitedPreemptions.is_schedule_with_limited_preemptions Job arrR pR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_is_schedule_with_limited_preemptions Job dJ arrL pL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ARR j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _
    (ccf_LM_can_be_preempted_for_model_with_limited_preemptions j _ _ (ccf_US_service Job sR sL Hs j tR tL Ht)))).
  exact (ct_bool_truth _ _ (ccf_US_scheduled_at Job sR sL Hs j tR tL Ht)).
Qed.

End LMJobDefs.

Section LMTaskDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tpR : Task -> seq nat) (tpL : Task -> NL).
Hypothesis Htp : CcfPpRel Task tpR tpL.

Lemma ccf_LM_task_last_nps tsk :
  SubNatRel (@ModelWithLimitedPreemptions.task_last_nps Task tpR tsk) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_last_nps Task dT tpL tsk).
Proof. exact (ccf_last0 _ _ (ccf_distances _ _ (Htp tsk))). Qed.

Lemma ccf_LM_task_max_nps tsk :
  SubNatRel (@ModelWithLimitedPreemptions.task_max_nps Task tpR tsk) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_max_nps Task dT tpL tsk).
Proof. exact (ccf_max0 _ _ (ccf_distances _ _ (Htp tsk))). Qed.

Variables (tsR : seq Task) (tsL : I.List Task).
Hypothesis Hts : ClListRel cid tsR tsL.
Notation MEM := (fun tsk => ccf_mem Task tsk tsR tsL Hts).

Lemma ccf_LM_task_beginning_of_execution_in_preemption_points :
  PropSPropRel (@ModelWithLimitedPreemptions.task_beginning_of_execution_in_preemption_points Task tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_beginning_of_execution_in_preemption_points Task dT tpL tsL).
Proof.
  apply: ct_forall_identity => tsk. apply: ct_imp; first exact (MEM tsk).
  exact (sub_nat_eq_correspondence _ _ _ _ (ccf_first0 _ _ (Htp tsk)) (sub_nat_rel_canonical 0)).
Qed.

Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat).
Hypothesis Htc : CcfParRel Task tcR tcL.

Lemma ccf_LM_task_end_of_execution_in_preemption_points :
  PropSPropRel (@ModelWithLimitedPreemptions.task_end_of_execution_in_preemption_points Task tcR tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_end_of_execution_in_preemption_points Task dT tcL tpL tsL).
Proof.
  apply: ct_forall_identity => tsk. apply: ct_imp; first exact (MEM tsk).
  exact (sub_nat_eq_correspondence _ _ _ _ (ccf_last0 _ _ (Htp tsk)) (Htc tsk)).
Qed.

Lemma ccf_LM_task_preemption_points_is_nondecreasing_sequence :
  PropSPropRel (@ModelWithLimitedPreemptions.task_preemption_points_is_nondecreasing_sequence Task tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_preemption_points_is_nondecreasing_sequence Task dT tpL tsL).
Proof.
  apply: ct_forall_identity => tsk. apply: ct_imp; first exact (MEM tsk).
  exact (ccf_nondecreasing _ _ (Htp tsk)).
Qed.

Lemma ccf_LM_task_segments_are_nonempty :
  PropSPropRel (@ModelWithLimitedPreemptions.task_segments_are_nonempty Task tpR tsR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_task_segments_are_nonempty Task dT tpL tsL).
Proof.
  apply: ct_forall_identity => tsk. apply: ct_forall_nat => nR nL Hn.
  apply: ct_imp; first exact (MEM tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hn (ccf_size _ _ (ccf_distances _ _ (Htp tsk)))).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical 1) (ccf_nth _ _ (ccf_distances _ _ (Htp tsk)) _ _ Hn)).
Qed.

End LMTaskDefs.

Section LMJobTaskDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variable job_task : Job -> Task.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CcfArrRel Job arrR arrL.
Notation ARR := (ccf_arrives_in Job arrR arrL Harr).
Variables (pR : Job -> seq nat) (pL : Job -> NL).
Hypothesis Hp : CcfPpRel Job pR pL.
Variables (tpR : Task -> seq nat) (tpL : Task -> NL).
Hypothesis Htp : CcfPpRel Task tpR tpL.

Lemma ccf_LM_job_consists_of_the_same_number_of_segments_as_task :
  PropSPropRel (@ModelWithLimitedPreemptions.job_consists_of_the_same_number_of_segments_as_task Task Job job_task arrR pR tpR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_consists_of_the_same_number_of_segments_as_task Task dT Job dJ job_task arrL pL tpL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (sub_nat_eq_correspondence _ _ _ _ (ccf_size _ _ (Hp j)) (ccf_size _ _ (Htp (job_task j)))).
Qed.

Lemma ccf_LM_lengths_of_task_segments_bound_length_of_job_segments :
  PropSPropRel (@ModelWithLimitedPreemptions.lengths_of_task_segments_bound_length_of_job_segments Task Job job_task arrR pR tpR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_lengths_of_task_segments_bound_length_of_job_segments Task dT Job dJ job_task arrL pL tpL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => nR nL Hn.
  apply: ct_imp; first exact (ARR j).
  exact (sub_nat_le_correspondence _ _ _ _ (ccf_nth _ _ (ccf_distances _ _ (Hp j)) _ _ Hn)
    (ccf_nth _ _ (ccf_distances _ _ (Htp (job_task j))) _ _ Hn)).
Qed.

Variables (tsR : seq Task) (tsL : I.List Task).
Hypothesis Hts : ClListRel cid tsR tsL.
Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat).
Hypothesis Htc : CcfParRel Task tcR tcL.

Lemma ccf_LM_fixed_preemption_points_task_model :
  PropSPropRel (@ModelWithLimitedPreemptions.fixed_preemption_points_task_model Task tcR Job job_task arrR pR tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_fixed_preemption_points_task_model Task dT tcL Job dJ job_task arrL pL tpL tsL).
Proof.
  apply: ct_and; first exact (ccf_LM_task_beginning_of_execution_in_preemption_points Task tpR tpL Htp tsR tsL Hts).
  apply: ct_and; first exact (ccf_LM_task_end_of_execution_in_preemption_points Task tpR tpL Htp tsR tsL Hts tcR tcL Htc).
  apply: ct_and; first exact (ccf_LM_task_preemption_points_is_nondecreasing_sequence Task tpR tpL Htp tsR tsL Hts).
  apply: ct_and; first exact ccf_LM_job_consists_of_the_same_number_of_segments_as_task.
  apply: ct_and; first exact ccf_LM_lengths_of_task_segments_bound_length_of_job_segments.
  exact (ccf_LM_task_segments_are_nonempty Task tpR tpL Htp tsR tsL Hts).
Qed.

Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CcfParRel Job cR cL.

Lemma ccf_LM_fixed_preemption_points_model :
  PropSPropRel (@ModelWithLimitedPreemptions.fixed_preemption_points_model Task tcR Job cR job_task arrR pR tpR tsR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_fixed_preemption_points_model Task dT tcL Job dJ cL job_task arrL pL tpL tsL).
Proof.
  apply: ct_and; first exact (ccf_LM_limited_preemptions_job_model Job pR pL Hp cR cL Hc arrR arrL Harr).
  exact ccf_LM_fixed_preemption_points_task_model.
Qed.

Variables (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypothesis Htm : CcfParRel Task tmR tmL.

Lemma ccf_LM_job_max_np_segment_le_task_max_np_segment :
  PropSPropRel (@ModelWithLimitedPreemptions.job_max_np_segment_le_task_max_np_segment Task Job job_task arrR pR tmR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_job_max_np_segment_le_task_max_np_segment Task dT Job dJ job_task arrL pL tmL).
Proof.
  apply: ct_forall_identity => j. apply: ct_imp; first exact (ARR j).
  exact (sub_nat_le_correspondence _ _ _ _ (ccf_LM_job_max_nps Job pR pL Hp j) (Htm (job_task j))).
Qed.

Lemma ccf_LM_model_with_floating_nonpreemptive_regions :
  PropSPropRel (@ModelWithLimitedPreemptions.model_with_floating_nonpreemptive_regions Task Job cR job_task arrR pR tmR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Limited_ModelWithLimitedPreemptions_model_with_floating_nonpreemptive_regions Task dT Job dJ cL job_task arrL pL tmL).
Proof.
  apply: ct_and; first exact (ccf_LM_limited_preemptions_job_model Job pR pL Hp cR cL Hc arrR arrL Harr).
  exact ccf_LM_job_max_np_segment_le_task_max_np_segment.
Qed.

End LMJobTaskDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma ccf_NPM_can_be_preempted_for_fully_nonpreemptive_model (Job : eqType) cR cL (Hc : CcfParRel Job cR cL) :
  CcfPmRel Job (FullyNonPreemptivePlatform.can_be_preempted_for_fully_nonpreemptive_model cR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Nonpreemptive_FullyNonPreemptivePlatform_can_be_preempted_for_fully_nonpreemptive_model Job (ct_decidable_eq Job) cL).
Proof.
  intros j tR tL Ht.
  exact (ct_bool_or _ _ _ _ (ct_decide_eq_nat _ _ _ _ Ht (sub_nat_rel_canonical 0)) (ct_decide_eq_nat _ _ _ _ Ht (Hc j))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma ccf_PM_can_be_preempted_for_fully_preemptive_model (Job : eqType) :
  CcfPmRel Job (FullyPreemptivePlatform.can_be_preempted_for_fully_preemptive_model (Job := Job))
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Preemptive_FullyPreemptivePlatform_can_be_preempted_for_fully_preemptive_model Job (ct_decidable_eq Job)).
Proof. intros j tR tL Ht. exact (ct_bool_canonical true). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

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
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CcfParRel _ f g |- _ => exact (H x) end
  | |- CtBoolRel (?f ?x ?y) (?g ?x ?y) => match goal with H : CcfRelRel _ f g |- _ => exact (H x y) end
  | |- CtBoolRel (?f ?x ?t) (?g ?x ?u) => match goal with H : CcfPmRel _ f g |- _ => eapply H end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | ArrivalSequence.arrival_sequence _ => apply: (ccf_forall_arr _); intros ? ? ?
  | UniprocessorSchedule.schedule _ => apply: (ccf_forall_sched _); intros ? ? ?
  | Priority.FP_policy _ => apply: (ccf_forall_rel _); intros ? ? ?
  | Priority.JLFP_policy _ => apply: (ccf_forall_rel _); intros ? ? ?
  | seq _ => apply: (ccf_forall_list _); intros ? ? ?
  | _ -> seq nat => apply: (ccf_forall_pp _); intros ? ? ?
  | _ -> seq Time.time => apply: (ccf_forall_pp _); intros ? ? ?
  | _ -> nat -> nat => apply: (ccf_forall_curve _); intros ? ? ?
  | _ -> Time.time -> nat => apply: (ccf_forall_curve _); intros ? ? ?
  | _ -> nat -> bool => apply: (ccf_forall_pm _); intros ? ? ?
  | _ -> Time.time -> bool => apply: (ccf_forall_pm _); intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: ccf_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp; crel
  | lazymatch goal with
    | |- forall _, _ => intro; crel
    | |- CcfIntRel _ (JLFPInstantiation.interference _ _) _ => fail; crel
    | |- CcfWlRel _ (JLFPInstantiation.interfering_workload _ _ _ _) _ => fail; crel
    | |- CcfRelRel _ (Priority.FP_to_JLFP _ _) _ => fail; crel
    | |- CcfRelRel _ (Priority.EDF _ _) _ => fail; crel
    | |- CcfIntRel _ (fun _ => _) _ => fail; crel
    | |- CcfWlRel _ (fun _ => _) _ => fail; crel
    | |- CcfRelRel _ (fun _ => _) _ => first [ fail; crel | fail; crel | intros ? ?; cbv beta; crel ]
    | |- CtBoolRel (orb _ _) _ => eapply ct_bool_or; crel
    | |- CcfPmRel _ (fun _ => _) _ => intros ? ? ? ?; cbv beta; crel
    | |- CcfPmRel _ _ _ => first [ assumption | intros ? ? ? ?; cbv beta; crel ]
    | |- CcfFunRel _ _ => intros ? ? ?; cbv beta; crel
    | |- CcfNatFunRel _ _ => intros ? ? ?; cbv beta; crel
    | |- CcfIbfRel _ _ _ => intros ? ? ? ? ? ? ?; cbv beta; crel
    | |- CcfPredRel _ _ _ => intro; cbv beta; crel
    | |- CcfParRel _ (fun _ => _) _ => intro; cbv beta; crel
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
  | S _ => eapply ccf_succ_rel; crel
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
  | _ <-> _ => eapply ccf_iff; crel
  | _ <> _ => eapply ccf_ne
  | ~ _ => eapply ct_imp; [crel | exact ccf_false_rel]
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else crel_eq_defs
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_eq_defs := first [ eapply ct_eq_rel | fail; crel ]
with crel_n_defs := first [ (match goal with |- context [@MaxArrivalsWorkloadBound.task_request_bound_function] => idtac end; eapply ccf_WB_task_request_bound_function; crel)
    | (match goal with |- context [@MaxArrivalsWorkloadBound.total_hep_request_bound_function_FP] => idtac end; eapply ccf_WB_total_hep_request_bound_function_FP; crel)
    | (match goal with |- context [@MaxArrivalsWorkloadBound.total_ohep_request_bound_function_FP] => idtac end; eapply ccf_WB_total_ohep_request_bound_function_FP; crel)
    | eapply ccf_ico; crel
    | eapply ct_bool_to_nat; crel
    | eapply ccf_sum_filtered_rel; crel
    | eapply ccf_sum_rel; crel
    | eapply ccf_max_filtered_rel; crel
    | (match goal with |- context [@ModelWithLimitedPreemptions.task_max_nps] => idtac end; eapply ccf_LM_task_max_nps; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.task_last_nps] => idtac end; eapply ccf_LM_task_last_nps; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.job_max_nps] => idtac end; eapply ccf_LM_job_max_nps; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.job_last_nps] => idtac end; eapply ccf_LM_job_last_nps; crel)
    | (match goal with |- context [@prosa.util.list.max0] => idtac end; eapply ccf_max0; crel)
    | (match goal with |- context [@prosa.util.list.first0] => idtac end; eapply ccf_first0; crel)
    | (match goal with |- context [@prosa.util.list.last0] => idtac end; eapply ccf_last0; crel)
    | (match goal with |- context [@seq.size] => idtac end; eapply ccf_size; crel)
    | (match goal with |- context [@seq.nth] => idtac end; eapply ccf_nth; crel)
    | (match goal with |- context [@UniprocessorSchedule.service] => idtac end; eapply ccf_US_service; crel)
    | (match goal with |- context [@UniprocessorSchedule.service_during] => idtac end; eapply ccf_US_service_during; crel)
    | (match goal with |- context [@UniprocessorSchedule.service_at] => idtac end; eapply ccf_US_service_at; crel) ]
with crel_b_defs := first [ eapply ccf_PM_can_be_preempted_for_fully_preemptive_model; crel
    | eapply ccf_NPM_can_be_preempted_for_fully_nonpreemptive_model; crel
    | (match goal with |- context [@ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions] => idtac end; eapply ccf_LM_can_be_preempted_for_model_with_limited_preemptions; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.preemption_time] => idtac end; eapply ccf_LPD_preemption_time; crel)
    | (match goal with |- context [@UniprocessorSchedule.scheduled_at] => idtac end; eapply ccf_US_scheduled_at; crel)
    | (match goal with |- context [@UniprocessorSchedule.completed_by] => idtac end; eapply ccf_US_completed_by; crel)
    | (match goal with |- context [@UniprocessorSchedule.pending] => idtac end; eapply ccf_US_pending; crel)
    | (match goal with |- context [@UniprocessorSchedule.backlogged] => idtac end; eapply ccf_US_backlogged; crel)
    | (match goal with |- context [@ArrivalSequence.has_arrived] => idtac end; eapply ccf_has_arrived; crel)
    | (match goal with |- context [@ArrivalSequence.arrives_at] => idtac end; eapply ccf_arrives_at; crel)
    | (match goal with |- context [@Job.job_cost_le_task_cost] => idtac end; eapply ccf_J_job_cost_le_task_cost; crel)
    | (match goal with |- context [@TaskArrival.is_job_of_task] => idtac end; eapply ccf_TA_is_job_of_task; crel) ]
with crel_l_defs := first [ (match goal with |- context [@ArrivalSequence.jobs_arrived_between] => idtac end; eapply ccf_jobs_arrived_between; crel)
    | (match goal with |- context [@ArrivalSequence.jobs_arriving_at] => idtac end; eapply ccf_arriving_at; crel)
    | eapply ccf_distances; crel
    | eapply ccf_LM_lengths_of_segments; crel ]
with crel_p_defs := first [ (match goal with |- context [@Priority.FP_is_reflexive] => idtac end; eapply ccf_PR_FP_is_reflexive; crel)
    | (match goal with |- context [@Priority.FP_is_transitive] => idtac end; eapply ccf_PR_FP_is_transitive; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.work_conserving] => idtac end; eapply ccf_LP_work_conserving; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.respects_FP_policy_at_preemption_point] => idtac end; eapply ccf_LPD_respects_FP_policy_at_preemption_point; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.work_conserving] => idtac end; eapply ccf_LPD_work_conserving; crel)
    | (match goal with |- context [@ArrivalCurves.family_of_proper_arrival_curves] => idtac end; eapply ccf_AC_family_of_proper_arrival_curves; crel)
    | (match goal with |- context [@ArrivalCurves.is_arrival_bound] => idtac end; eapply ccf_AC_is_arrival_bound; crel)
    | (match goal with |- context [@ArrivalCurves.proper_arrival_curve] => idtac end; eapply ccf_AC_proper_arrival_curve; crel)
    | (match goal with |- context [@iff] => idtac end; eapply ccf_iff; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.fixed_preemption_points_model] => idtac end; eapply ccf_LM_fixed_preemption_points_model; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.is_schedule_with_limited_preemptions] => idtac end; eapply ccf_LM_is_schedule_with_limited_preemptions; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.model_with_floating_nonpreemptive_regions] => idtac end; eapply ccf_LM_model_with_floating_nonpreemptive_regions; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.limited_preemptions_job_model] => idtac end; eapply ccf_LM_limited_preemptions_job_model; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.fixed_preemption_points_task_model] => idtac end; eapply ccf_LM_fixed_preemption_points_task_model; crel)
    | (match goal with |- context [@ModelWithLimitedPreemptions.job_max_np_segment_le_task_max_np_segment] => idtac end; eapply ccf_LM_job_max_np_segment_le_task_max_np_segment; crel)
    | (match goal with |- context [@NonpreemptiveSchedule.is_nonpreemptive_schedule] => idtac end; eapply ccf_NP_is_nonpreemptive_schedule; crel)
    | (match goal with |- context [@Job.cost_of_jobs_from_arrival_sequence_le_task_cost] => idtac end; eapply ccf_J_cost_of_jobs_from_arrival_sequence_le_task_cost; crel)
    | (match goal with |- context [@prosa.util.nondecreasing.nondecreasing_sequence] => idtac end; eapply ccf_nondecreasing; crel)
    | eapply ccf_nmem; crel
    | (match goal with |- context [@ArrivalSequence.arrives_in] => idtac end; eapply ccf_arrives_in; crel)
    | (match goal with |- context [@ArrivalSequence.arrival_times_are_consistent] => idtac end; eapply ccf_consistent; crel)
    | (match goal with |- context [@ArrivalSequence.arrival_sequence_is_a_set] => idtac end; eapply ccf_is_a_set; crel)
    | eapply ccf_mem; crel
    | eapply ccf_uniq; crel
    | (match goal with |- context [@UniprocessorSchedule.jobs_come_from_arrival_sequence] => idtac end; eapply ccf_US_jobs_come_from_arrival_sequence; crel)
    | (match goal with |- context [@UniprocessorSchedule.jobs_must_arrive_to_execute] => idtac end; eapply ccf_US_jobs_must_arrive_to_execute; crel)
    | (match goal with |- context [@UniprocessorSchedule.completed_jobs_dont_execute] => idtac end; eapply ccf_US_completed_jobs_dont_execute; crel)
    | (match goal with |- context [@UniprocessorSchedule.sequential_jobs] => idtac end; eapply ccf_US_sequential_jobs; crel)
    | (match goal with |- context [@ResponseTime.is_response_time_bound_of_job] => idtac end; eapply ccf_RT_is_response_time_bound_of_job; crel)
    | (match goal with |- context [@ResponseTime.is_response_time_bound_of_task] => idtac end; eapply ccf_RT_is_response_time_bound_of_task; crel) ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_uniprocessor_response_time_bound_fully_preemptive_fp (Task Job : eqType) : Prop :=
  forall p0 : Task -> nat,
    ltac:(type_of_term (@RTAforConcreteModels.uniprocessor_response_time_bound_fully_preemptive_fp Task p0 Job)).
Definition tgt_uniprocessor_response_time_bound_fully_preemptive_fp (Task Job : eqType) : SProp :=
  forall p0 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_FixedPriority_NonprReg_ConcreteModels_ResponseTimeBound_RTAforConcreteModels_uniprocessor_response_time_bound_fully_preemptive_fp Task (ct_decidable_eq Task) p0 Job (ct_decidable_eq Job))).
Theorem RTAforConcreteModels_uniprocessor_response_time_bound_fully_preemptive_fp_correspondence (Task Job : eqType) :
  PropSPropRel (src_uniprocessor_response_time_bound_fully_preemptive_fp Task Job) (tgt_uniprocessor_response_time_bound_fully_preemptive_fp Task Job).
Proof. unfold src_uniprocessor_response_time_bound_fully_preemptive_fp, tgt_uniprocessor_response_time_bound_fully_preemptive_fp. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_uniprocessor_response_time_bound_fully_nonpreemptive_fp (Task Job : eqType) : Prop :=
  forall p0 : Task -> nat,
    ltac:(type_of_term (@RTAforConcreteModels.uniprocessor_response_time_bound_fully_nonpreemptive_fp Task p0 Job)).
Definition tgt_uniprocessor_response_time_bound_fully_nonpreemptive_fp (Task Job : eqType) : SProp :=
  forall p0 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_FixedPriority_NonprReg_ConcreteModels_ResponseTimeBound_RTAforConcreteModels_uniprocessor_response_time_bound_fully_nonpreemptive_fp Task (ct_decidable_eq Task) p0 Job (ct_decidable_eq Job))).
Theorem RTAforConcreteModels_uniprocessor_response_time_bound_fully_nonpreemptive_fp_correspondence (Task Job : eqType) :
  PropSPropRel (src_uniprocessor_response_time_bound_fully_nonpreemptive_fp Task Job) (tgt_uniprocessor_response_time_bound_fully_nonpreemptive_fp Task Job).
Proof. unfold src_uniprocessor_response_time_bound_fully_nonpreemptive_fp, tgt_uniprocessor_response_time_bound_fully_nonpreemptive_fp. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_uniprocessor_response_time_bound_fp_with_fixed_preemption_points (Task Job : eqType) : Prop :=
  forall p0 : Task -> nat,
    ltac:(type_of_term (@RTAforConcreteModels.uniprocessor_response_time_bound_fp_with_fixed_preemption_points Task p0 Job)).
Definition tgt_uniprocessor_response_time_bound_fp_with_fixed_preemption_points (Task Job : eqType) : SProp :=
  forall p0 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_FixedPriority_NonprReg_ConcreteModels_ResponseTimeBound_RTAforConcreteModels_uniprocessor_response_time_bound_fp_with_fixed_preemption_points Task (ct_decidable_eq Task) p0 Job (ct_decidable_eq Job))).
Theorem RTAforConcreteModels_uniprocessor_response_time_bound_fp_with_fixed_preemption_points_correspondence (Task Job : eqType) :
  PropSPropRel (src_uniprocessor_response_time_bound_fp_with_fixed_preemption_points Task Job) (tgt_uniprocessor_response_time_bound_fp_with_fixed_preemption_points Task Job).
Proof. unfold src_uniprocessor_response_time_bound_fp_with_fixed_preemption_points, tgt_uniprocessor_response_time_bound_fp_with_fixed_preemption_points. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions (Task Job : eqType) : Prop :=
  forall p0 : Task -> nat,
    ltac:(type_of_term (@RTAforConcreteModels.uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions Task p0 Job)).
Definition tgt_uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions (Task Job : eqType) : SProp :=
  forall p0 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_FixedPriority_NonprReg_ConcreteModels_ResponseTimeBound_RTAforConcreteModels_uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions Task (ct_decidable_eq Task) p0 Job (ct_decidable_eq Job))).
Theorem RTAforConcreteModels_uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions_correspondence (Task Job : eqType) :
  PropSPropRel (src_uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions Task Job) (tgt_uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions Task Job).
Proof. unfold src_uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions, tgt_uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions. crel_spine. crel. Unshelve. all: crel. Qed.
