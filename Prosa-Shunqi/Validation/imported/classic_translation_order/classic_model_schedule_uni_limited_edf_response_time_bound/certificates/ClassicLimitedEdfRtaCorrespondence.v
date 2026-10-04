From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.service classic.model.schedule.uni.workload classic.model.schedule.uni.schedule_of_task classic.model.schedule.uni.limited.busy_interval classic.model.schedule.uni.limited.abstract_RTA.definitions classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta classic.model.schedule.uni.limited.jlfp_instantiation classic.model.schedule.uni.basic.platform classic.model.priority classic.model.schedule.uni.response_time classic.model.schedule.uni.limited.platform.definitions classic.model.schedule.uni.limited.schedule classic.model.schedule.uni.limited.rbf classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space classic.model.arrival.curves.bounds classic.analysis.uni.arrival_curves.workload_bound classic.model.schedule.uni.limited.edf.response_time_bound.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicLimitedEdfRta.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicLimitedEdfRtaBase ClassicLimitedEdfRtaList.



Module I := ImportedClassicLimitedEdfRta.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/edf/response_time_bound.v] (ProsaBuddy classic, commit f692cb7).

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

Lemma cer_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cer_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cer_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cer_false_rel). Qed.

Lemma cer_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cer_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cer_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cer_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cer_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cer_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cer_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cer_unmap_rel T l) PR PL).
Qed.

Definition CerParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cer_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CerParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cer_forall_cover _ _ (CerParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cer_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cer_natl s') end.

Definition cer_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cer_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cer_one) (cer_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cer_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cer_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cer_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cer_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cer_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cer_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cer_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cer_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cer_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cer_cl_append. reflexivity.
Qed.

Lemma cer_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CerFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cer_bigcat_rel (A : Type) fR fL (Hf : CerFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicLimitedEdfRtaInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cer_iota_range (nR - mR) 0) cer_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cer_cl_map_ext _ _ Hpt) (cer_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cer_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cer_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CerArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cer_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cer_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cer_arr_canonical aR : CerArrRel aR (cer_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cer_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cer_arr_surjective aL : CerArrRel (cer_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cer_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CerArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cer_forall_cover _ _ CerArrRel cer_arr_to_target cer_arr_to_source cer_arr_canonical cer_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cer_jobs_arrived_between aR aL (Ha : CerArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cer_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cer_arrives_in aR aL (Ha : CerArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cer_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cer_consistent pR pL (Hp : CerParRel Job pR pL) aR aL (Ha : CerArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cer_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cer_is_a_set aR aL (Ha : CerArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cer_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cer_arrives_at aR aL (Ha : CerArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cer_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma cer_has_arrived pR pL (Hp : CerParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

Lemma cer_arrived_before pR pL (Hp : CerParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrived_before pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_before Job dJ pL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cer_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cer_snatl s') end.

Lemma cer_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cer_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cer_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cer_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cer_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cer_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cer_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CerFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cer_fun_canonical FR FL (HF : CerFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cer_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cer_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CerFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cer_nat_sub_canonical nR mR.
  rewrite cer_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cer_foldr_add FL FR (cer_fun_canonical FR FL HF)).
  by rewrite cer_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cer_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cer_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cer_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cer_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cer_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CerSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cer_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cer_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cer_sched_canonical sR : CerSchedRel sR (cer_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cer_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cer_sched_surjective sL : CerSchedRel (cer_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cer_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cer_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CerSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cer_forall_cover _ _ CerSchedRel cer_sched_to_target cer_sched_to_source cer_sched_canonical cer_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cer_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CerSchedRel Job sR (cer_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CerSchedRel Job (cer_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cer_sched_canonical Job) (cer_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.

Lemma cer_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cer_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cer_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cer_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cer_US_scheduled_at j tR tL Ht)). Qed.

Lemma cer_service_at_fun j : CerFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cer_US_service_at j kR kL Hk). Qed.

Lemma cer_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cer_ico _ _ _ _ _ _ H1 H2 (cer_service_at_fun j)). Qed.

Lemma cer_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cer_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cer_US_completed_by cR cL (Hc : CerParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cer_US_service j tR tL Ht)). Qed.

Lemma cer_US_pending aR aL (Ha : CerParRel Job aR aL) cR cL (Hc : CerParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cer_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cer_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cer_US_pending_earlier_and_at aR aL (Ha : CerParRel Job aR aL) cR cL (Hc : CerParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending_earlier_and_at aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending_earlier_and_at Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cer_arrived_before Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cer_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cer_US_backlogged aR aL (Ha : CerParRel Job aR aL) cR cL (Hc : CerParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.backlogged aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_backlogged Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cer_US_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (cer_US_scheduled_at j tR tL Ht))).
Qed.

Lemma cer_US_sequential_jobs (Task : eqType) aR aL (Ha : CerParRel Job aR aL) cR cL (Hc : CerParRel Job cR cL)
    (job_task : Job -> Task) :
  PropSPropRel (UniprocessorSchedule.sequential_jobs aR cR sR job_task)
    (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_sequential_jobs Job dJ aL cL sL Task (ct_decidable_eq Task) job_task).
Proof.
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_eq Task (job_task j1) (job_task j2))).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha j1) (Ha j2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cer_US_scheduled_at j2 tR tL Ht)).
  exact (ct_bool_truth _ _ (cer_US_completed_by cR cL Hc j1 tR tL Ht)).
Qed.

Lemma cer_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CerArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cer_US_scheduled_at j tR tL Ht)).
  exact (cer_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cer_US_jobs_must_arrive_to_execute aR aL (Ha : CerParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cer_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cer_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma cer_US_completed_jobs_dont_execute cR cL (Hc : CerParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cer_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cer_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicLimitedEdfRtaInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicLimitedEdfRtaInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cer_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cer_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cer_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicLimitedEdfRtaInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicLimitedEdfRtaInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicLimitedEdfRtaInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cer_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cer_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CerPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma cer_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CerPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cer_forall_cover _ _ (CerPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CerRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cer_rel_canonical (T : Type) (rR : T -> T -> bool) : CerRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cer_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CerRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cer_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CerRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cer_forall_cover _ _ (CerRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cer_rel_canonical T) (cer_rel_surjective T) PR PL).
Qed.

Definition CerJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CerRelRel T (rR tR) (rL tL).

Lemma cer_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CerJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cer_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CerJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cer_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CerJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cer_forall_cover _ _ (CerJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cer_jldp_canonical T) (cer_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cer_PR_JLFP_policy :
  And (forall rR : Priority.JLFP_policy Job, CerRelRel Job rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLFP_policy Job dJ, CerRelRel Job (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cer_rel_canonical Job) (cer_rel_surjective Job)). Qed.

Lemma cer_PR_EDF jaR jaL (Hja : CerParRel Job jaR jaL) jdR jdL (Hjd : CerParRel Job jdR jdL) :
  CerRelRel Job (Priority.EDF jaR jdR) (I.Prosa_Classic_Model_Priority_Priority_EDF Job dJ jaL jdL).
Proof.
  intros a b. exact (ct_decide_le _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja a) (Hjd a))
                                          (sub_add_correspondence _ _ _ _ (Hja b) (Hjd b))).
Qed.

Lemma cer_PR_job_relative_dealine tdR tdL (Htd : CerParRel Task tdR tdL) (job_task : Job -> Task) :
  CerParRel Job (Priority.job_relative_dealine tdR job_task)
    (I.Prosa_Classic_Model_Priority_Priority_job_relative_dealine Task dT tdL Job dJ job_task).
Proof. intro j. exact (Htd (job_task j)). Qed.

End PriodefsDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cer_J_job_cost_positive cR cL (Hc : CerParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

Lemma cer_J_job_cost_le_task_cost tcR tcL (Htc : CerParRel Task tcR tcL) cR cL (Hc : CerParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

Lemma cer_J_cost_of_jobs_from_arrival_sequence_le_task_cost tcR tcL (Htc : CerParRel Task tcR tcL)
    cR cL (Hc : CerParRel Job cR cL) (job_task : Job -> Task) aR aL (Ha : CerArrRel Job aR aL) :
  PropSPropRel (Job.cost_of_jobs_from_arrival_sequence_le_task_cost tcR cR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_cost_of_jobs_from_arrival_sequence_le_task_cost Task dT tcL Job dJ cL job_task aL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp.
  - apply: ct_exists_nat => tR tL Ht. exact (cer_mem Job j _ _ (Ha tR tL Ht)).
  - exact (ct_bool_truth _ _ (cer_J_job_cost_le_task_cost tcR tcL Htc cR cL Hc job_task j)).
Qed.

End JobDefs.

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cer_TA_is_job_of_task (job_task : Job -> Task) tsk j :
  CtBoolRel (TaskArrival.is_job_of_task job_task tsk j)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk j).
Proof. exact (ct_decide_eq Task (job_task j) tsk). Qed.

Lemma cer_TA_arrivals_of_task_between (job_task : Job -> Task) aR aL (Ha : CerArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_between Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans (cl_filter cid _ (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk)
                            (cer_TA_is_job_of_task job_task tsk) _) _).
  exact (f_equal (I.List_filter Job (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk))
           (Logic.eq_sym (cl_list_logic _ _ _ (cer_jobs_arrived_between Job aR aL Ha _ _ _ _ H1 H2)))).
Qed.

Lemma cer_TA_arrivals_of_task_before (job_task : Job -> Task) aR aL (Ha : CerArrRel Job aR aL) tsk
    tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (TaskArrival.arrivals_of_task_before job_task aR tsk tR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_before Task Job dT dJ job_task aL tsk tL).
Proof. exact (cer_TA_arrivals_of_task_between job_task aR aL Ha tsk 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma cer_TA_num_arrivals_of_task (job_task : Job -> Task) aR aL (Ha : CerArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (TaskArrival.num_arrivals_of_task job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_num_arrivals_of_task Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  have H := cer_TA_arrivals_of_task_between job_task aR aL Ha tsk _ _ _ _ H1 H2.
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
Definition CerCurveRel (fR : Task -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk nR nL, SubNatRel nR nL -> SubNatRel (fR tsk nR) (fL tsk nL).

Notation NA := (cer_TA_num_arrivals_of_task Task Job).

Lemma cer_AC_is_arrival_bound (job_task : Job -> Task) aR aL (Ha : CerArrRel Job aR aL)
    mR mL (Hm : CerCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.is_arrival_bound job_task aR mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_is_arrival_bound Task dT Job dJ job_task aL mL tsk).
Proof.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 H2).
  exact (sub_nat_le_correspondence _ _ _ _ (NA job_task aR aL Ha tsk _ _ _ _ H1 H2) (Hm tsk _ _ (ct_sub_rel _ _ _ _ H2 H1))).
Qed.

Lemma cer_AC_zero_arrival_curve mR mL (Hm : CerCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.zero_arrival_curve mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_zero_arrival_curve Task dT mL tsk).
Proof. exact (sub_nat_eq_correspondence _ _ _ _ (Hm tsk _ _ (sub_nat_rel_canonical 0)) (sub_nat_rel_canonical 0)). Qed.

Lemma cer_AC_monotonic_arrival_curve mR mL (Hm : CerCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.monotonic_arrival_curve mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_monotonic_arrival_curve Task dT mL tsk).
Proof.
  apply: ct_forall_nat => xR xL Hx. apply: ct_forall_nat => yR yL Hy.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ Hx Hy)).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hm tsk _ _ Hx) (Hm tsk _ _ Hy))).
Qed.

Lemma cer_AC_proper_arrival_curve (job_task : Job -> Task) aR aL (Ha : CerArrRel Job aR aL)
    mR mL (Hm : CerCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.proper_arrival_curve job_task aR mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_proper_arrival_curve Task dT Job dJ job_task aL mL tsk).
Proof.
  apply: ct_and; first exact (cer_AC_is_arrival_bound job_task aR aL Ha mR mL Hm tsk).
  apply: ct_and; first exact (cer_AC_zero_arrival_curve mR mL Hm tsk).
  exact (cer_AC_monotonic_arrival_curve mR mL Hm tsk).
Qed.

Lemma cer_AC_family_of_proper_arrival_curves (job_task : Job -> Task) aR aL (Ha : CerArrRel Job aR aL)
    mR mL (Hm : CerCurveRel mR mL) tsR tsL (Hts : ClListRel cid tsR tsL) :
  PropSPropRel (ArrivalCurves.family_of_proper_arrival_curves job_task aR mR tsR)
    (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_family_of_proper_arrival_curves Task dT Job dJ job_task aL mL tsL).
Proof.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cer_mem Task tsk _ _ Hts).
  exact (cer_AC_proper_arrival_curve job_task aR aL Ha mR mL Hm tsk).
Qed.

End AcboundsDefs.

(** * Arrival curves [Task -> time -> nat], with two-way totals *)

Lemma cer_curve_canonical (Task : eqType) mR : CerCurveRel Task mR (fun tsk nL => sub_nat_to_imported (mR tsk (sub_nat_to_rocq nL))).
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma cer_curve_surjective (Task : eqType) mL : CerCurveRel Task (fun tsk nR => sub_nat_to_rocq (mL tsk (sub_nat_to_imported nR))) mL.
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. exact (sub_nat_rel_surjective _). Qed.

Lemma cer_forall_curve (Task : eqType) (PR : (Task -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall mR mL, CerCurveRel Task mR mL -> PropSPropRel (PR mR) (PL mL)) -> PropSPropRel (forall m, PR m) (forall m, PL m).
Proof. exact (cer_forall_cover _ _ (CerCurveRel Task) _ _ (cer_curve_canonical Task) (cer_curve_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section AcwbDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat).
Hypothesis Htc : CerParRel Task tcR tcL.
Variables (mR : Task -> nat -> nat) (mL : Task -> Lean.Nat -> Lean.Nat).
Hypothesis Hm : CerCurveRel Task mR mL.

Lemma cer_WB_task_request_bound_function tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.task_request_bound_function tcR mR tsk dR) (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_task_request_bound_function Task dT tcL mL tsk dL).
Proof. exact (sub_mul_correspondence _ _ _ _ (Htc tsk) (Hm tsk _ _ Hd)). Qed.

Notation TRBF := cer_WB_task_request_bound_function.

Lemma cer_WB_total_request_bound_function tsR tsL (Hts : ClListRel cid tsR tsL) dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.total_request_bound_function tcR mR tsR dR) (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_total_request_bound_function Task dT tcL mL tsL dL).
Proof. exact (cer_sum_rel Task _ _ (fun x => TRBF x dR dL Hd) _ _ Hts). Qed.

End AcwbDefs.

Section UwlDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cer_WL_workload_of_jobs cR cL (Hc : CerParRel Job cR cL) jobsR jobsL (Hj : ClListRel cid jobsR jobsL)
    pR pL (Hp : CerPredRel Job pR pL) :
  SubNatRel (Workload.workload_of_jobs cR jobsR pR) (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_workload_of_jobs Job dJ cL jobsL pL).
Proof. exact (cer_sum_filtered_rel Job cR cL Hc pR pL Hp _ _ Hj). Qed.

Lemma cer_WL_task_workload cR cL (Hc : CerParRel Job cR cL) (job_task : Job -> Task) tsk
    jobsR jobsL (Hj : ClListRel cid jobsR jobsL) :
  SubNatRel (Workload.task_workload cR job_task tsk jobsR) (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_task_workload Task dT Job dJ cL job_task tsk jobsL).
Proof. exact (cer_WL_workload_of_jobs cR cL Hc jobsR jobsL Hj _ _ (fun j => ct_decide_eq Task (job_task j) tsk)). Qed.

Lemma cer_WL_task_workload_between cR cL (Hc : CerParRel Job cR cL) (job_task : Job -> Task)
    arrR arrL (Harr : CerArrRel Job arrR arrL) tsk t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Workload.task_workload_between cR job_task arrR tsk t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_task_workload_between Task dT Job dJ cL job_task arrL tsk t1L t2L).
Proof. exact (cer_WL_task_workload cR cL Hc job_task tsk _ _ (cer_jobs_arrived_between Job arrR arrL Harr _ _ _ _ H1 H2)). Qed.

End UwlDefs.

Section UrtDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.

Lemma cer_RT_is_response_time_bound_of_job aR aL (Ha : CerParRel Job aR aL) cR cL (Hc : CerParRel Job cR cL)
    j rR rL (Hr : SubNatRel rR rL) :
  CtBoolRel (ResponseTime.is_response_time_bound_of_job aR cR sR j rR) (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_job Job dJ aL cL sL j rL).
Proof. exact (cer_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr)). Qed.

Lemma cer_RT_is_response_time_bound_of_task aR aL (Ha : CerParRel Job aR aL) cR cL (Hc : CerParRel Job cR cL)
    (job_task : Job -> Task) arrR arrL (Harr : CerArrRel Job arrR arrL) tsk rR rL (Hr : SubNatRel rR rL) :
  PropSPropRel (ResponseTime.is_response_time_bound_of_task aR cR job_task arrR sR tsk rR)
    (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_task Task dT Job dJ aL cL job_task arrL sL tsk rL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cer_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (cer_RT_is_response_time_bound_of_job aR aL Ha cR cL Hc j rR rL Hr)).
Qed.

End UrtDefs.

Section UplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.

Lemma cer_UP_work_conserving aR aL (Ha : CerParRel Job aR aL) cR cL (Hc : CerParRel Job cR cL)
    arrR arrL (Harr : CerArrRel Job arrR arrL) :
  PropSPropRel (Platform.work_conserving aR cR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Basic_Platform_Platform_work_conserving Job dJ aL cL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cer_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cer_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (cer_US_scheduled_at Job sR sL Hs j_other tR tL Ht)).
Qed.

End UplatDefs.

Lemma cer_iff (P Q : Prop) (PL QL : SProp) :
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
Definition CerPmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma cer_pm_canonical pR : CerPmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cer_pm_surjective pL : CerPmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cer_forall_pm (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CerPmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (cer_forall_cover _ _ CerPmRel _ _ cer_pm_canonical cer_pm_surjective PR PL). Qed.

End LpdefsPmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LpdefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CerPmRel Job pR pL.

Notation SA := (cer_US_scheduled_at Job sR sL Hs).
Notation SV := (cer_US_service Job sR sL Hs).

End LpdefsDefs.

Section LpdefsDefs2.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CerPmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : CerParRel Job cR cL) (Hm : CerParRel Job mR mL) (Htm : CerParRel Task tmR tmL).

End LpdefsDefs2.

(* ------------------------------------------------------------------ *)
(** * Relations *)

Lemma cer_eq_transport (T : Type) (a b : T) aL bL : Lean.eq a aL -> Lean.eq b bL ->
  PropSPropRel (Logic.eq a b) (Lean.eq aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (ct_eq_rel T a b). Qed.

(** Functions [nat -> T] (identical values) and [nat -> nat] (values by [SubNatRel]), pointwise on related arguments. *)
Definition CerRsFunRel (T : Type) (fR : nat -> T) (fL : Lean.Nat -> T) : SProp :=
  forall nR nL, SubNatRel nR nL -> Lean.eq (fR nR) (fL nL).
Definition CerNatFunRel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) : SProp :=
  forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

(** Interference bound functions [Task -> time -> time -> time], pointwise on related arguments and values. *)
Definition CerIbfRel (Task : Type) (fR : Task -> nat -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk, forall aR aL, SubNatRel aR aL -> CerNatFunRel (fR tsk aR) (fL tsk aL).

Definition cer_ibf_to_target (Task : Type) (fR : Task -> nat -> nat -> nat) : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat :=
  fun tsk aL xL => sub_nat_to_imported (fR tsk (sub_nat_to_rocq aL) (sub_nat_to_rocq xL)).
Definition cer_ibf_to_source (Task : Type) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : Task -> nat -> nat -> nat :=
  fun tsk aR xR => sub_nat_to_rocq (fL tsk (sub_nat_to_imported aR) (sub_nat_to_imported xR)).

Lemma cer_ibf_canonical (Task : Type) fR : CerIbfRel Task fR (cer_ibf_to_target Task fR).
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  unfold cer_ibf_to_target. rewrite !sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma cer_ibf_surjective (Task : Type) fL : CerIbfRel Task (cer_ibf_to_source Task fL) fL.
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma cer_forall_ibf (Task : Type) (PR : (Task -> nat -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, CerIbfRel Task fR fL -> PropSPropRel (PR fR) (PL fL)) -> PropSPropRel (forall f, PR f) (forall f, PL f).
Proof. exact (cer_forall_cover _ _ (CerIbfRel Task) (cer_ibf_to_target Task) (cer_ibf_to_source Task) (cer_ibf_canonical Task) (cer_ibf_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cer_RS_are_not_equivalent_at_values_less_than (T : eqType) f1R f1L (H1 : CerRsFunRel T f1R f1L)
    f2R f2L (H2 : CerRsFunRel T f2R f2L) BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (AbstractRTAReduction.are_not_equivalent_at_values_less_than f1R f2R BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_are_not_equivalent_at_values_less_than T (ct_decidable_eq T) f1L f2L BL).
Proof.
  apply: ct_exists_nat => xR xL Hx.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Hx HB).
  exact (ct_imp _ _ _ _ (cer_eq_transport T _ _ _ _ (H1 xR xL Hx) (H2 xR xL Hx)) cer_false_rel).
Qed.

Lemma cer_not_equiv_nat f1R f1L (H1 : CerNatFunRel f1R f1L) f2R f2L (H2 : CerNatFunRel f2R f2L) BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (AbstractRTAReduction.are_not_equivalent_at_values_less_than f1R f2R BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_are_not_equivalent_at_values_less_than_inst1 Lean.Nat I.instDecidableEqNat f1L f2L BL).
Proof.
  apply: ct_exists_nat => xR xL Hx.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Hx HB).
  exact (ct_imp _ _ _ _ (sub_nat_eq_correspondence _ _ _ _ (H1 xR xL Hx) (H2 xR xL Hx)) cer_false_rel).
Qed.

Lemma cer_RS_is_in_search_space (Task : eqType) tsk BR BL (HB : SubNatRel BR BL)
    fR fL (Hf : CerIbfRel Task fR fL) AR AL (HA : SubNatRel AR AL) :
  PropSPropRel (AbstractRTAReduction.is_in_search_space tsk BR fR AR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_ReductionOfSearchSpace_AbstractRTAReduction_is_in_search_space Task (ct_decidable_eq Task) tsk BL fL AL).
Proof.
  apply: ct_or; first exact (sub_nat_eq_correspondence _ _ _ _ HA (sub_nat_rel_canonical 0)).
  apply: ct_and.
  - exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) HA) (ct_decide_lt _ _ _ _ HA HB))).
  - exact (cer_not_equiv_nat _ _ (Hf tsk _ _ (ct_sub_rel _ _ _ _ HA (sub_nat_rel_canonical 1))) _ _ (Hf tsk _ _ HA) _ _ HB).
Qed.

(* ------------------------------------------------------------------ *)
(** * Interference predicates and interfering workloads *)

Section JISEQARDIRel.
Variable Job : eqType.

Definition CerIntRel (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (iR j tR) (iL j tL).

Lemma cer_int_canonical iR : CerIntRel iR (fun j tL => ct_b2l (iR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cer_int_surjective iL : CerIntRel (fun j tR => ct_l2b (iL j (sub_nat_to_imported tR))) iL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cer_forall_int (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall iR iL, CerIntRel iR iL -> PropSPropRel (PR iR) (PL iL)) -> PropSPropRel (forall i, PR i) (forall i, PL i).
Proof. exact (cer_forall_cover _ _ CerIntRel _ _ cer_int_canonical cer_int_surjective PR PL). Qed.

Definition CerWlRel (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (wR j tR) (wL j tL).

Lemma cer_wl_canonical wR : CerWlRel wR (fun j tL => sub_nat_to_imported (wR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma cer_wl_surjective wL : CerWlRel (fun j tR => sub_nat_to_rocq (wL j (sub_nat_to_imported tR))) wL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (sub_nat_rel_surjective _). Qed.

Lemma cer_forall_wl (PR : (Job -> nat -> nat) -> Prop) (PL : (Job -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall wR wL, CerWlRel wR wL -> PropSPropRel (PR wR) (PL wL)) -> PropSPropRel (forall w, PR w) (forall w, PL w).
Proof. exact (cer_forall_cover _ _ CerWlRel _ _ cer_wl_canonical cer_wl_surjective PR PL). Qed.

End JISEQARDIRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JISEQARDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cer_ARD_cumul_interference iR iL (Hi : CerIntRel Job iR iL) j t1R t1L (H1 : SubNatRel t1R t1L)
    t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (AbstractRTADefinitions.cumul_interference iR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_cumul_interference Job dJ iL j t1L t2L).
Proof. exact (cer_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (Hi j kR kL Hk))). Qed.

Lemma cer_ARD_cumul_interfering_workload wR wL (Hw : CerWlRel Job wR wL) j t1R t1L (H1 : SubNatRel t1R t1L)
    t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (AbstractRTADefinitions.cumul_interfering_workload wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_cumul_interfering_workload Job dJ wL j t1L t2L).
Proof. exact (cer_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => Hw j kR kL Hk)). Qed.

Notation CI := cer_ARD_cumul_interference.
Notation CW := cer_ARD_cumul_interfering_workload.

Section JISEQARDSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CerParRel Job aR aL) (Hc : CerParRel Job cR cL).
Variables (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat).
Hypotheses (Hi : CerIntRel Job iR iL) (Hw : CerWlRel Job wR wL).

Lemma cer_ARD_quiet_time j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (AbstractRTADefinitions.quiet_time aR cR sR iR wR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_quiet_time Job dJ aL cL sL iL wL j tL).
Proof.
  apply: ct_and.
  - exact (sub_nat_eq_correspondence _ _ _ _ (CI iR iL Hi j 0 _ (sub_nat_rel_canonical 0) tR tL Ht)
             (CW wR wL Hw j 0 _ (sub_nat_rel_canonical 0) tR tL Ht)).
  - exact (ct_bool_truth _ _ (ct_bool_not _ _ (cer_US_pending_earlier_and_at Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht))).
Qed.

Lemma cer_ARD_busy_interval_prefix j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (AbstractRTADefinitions.busy_interval_prefix aR cR sR iR wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_interval_prefix Job dJ aL cL sL iL wL j t1L t2L).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Ha j)) (ct_decide_lt _ _ _ _ (Ha j) H2))).
  apply: ct_and; first exact (cer_ARD_quiet_time j t1R t1L H1).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  exact (ct_imp _ _ _ _ (cer_ARD_quiet_time j tR tL Ht) cer_false_rel).
Qed.

Lemma cer_ARD_busy_interval j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (AbstractRTADefinitions.busy_interval aR cR sR iR wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_interval Job dJ aL cL sL iL wL j t1L t2L).
Proof.
  apply: ct_and; first exact (cer_ARD_busy_interval_prefix j t1R t1L H1 t2R t2L H2).
  exact (cer_ARD_quiet_time j t2R t2L H2).
Qed.

Notation BI := cer_ARD_busy_interval.

Lemma cer_ARD_work_conserving (job_task : Job -> Task) arrR arrL (Harr : CerArrRel Job arrR arrL) tsk :
  PropSPropRel (AbstractRTADefinitions.work_conserving aR cR job_task arrR sR tsk iR wR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_work_conserving Task dT Job dJ aL cL job_task arrL sL tsk iL wL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cer_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  apply: ct_imp; first exact (BI j t1R t1L H1 t2R t2L H2).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: cer_iff.
  - exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (Hi j tR tL Ht)) cer_false_rel).
  - exact (ct_bool_truth _ _ (cer_US_scheduled_at Job sR sL Hs j tR tL Ht)).
Qed.

Lemma cer_ARD_busy_intervals_are_bounded_by (job_task : Job -> Task) arrR arrL (Harr : CerArrRel Job arrR arrL)
    tsk LR LL (HL : SubNatRel LR LL) :
  PropSPropRel (AbstractRTADefinitions.busy_intervals_are_bounded_by aR cR job_task arrR sR tsk iR wR LR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_intervals_are_bounded_by Task dT Job dJ aL cL job_task arrL sL tsk iL wL LL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cer_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  apply: ct_exists_nat => t1R t1L H1. apply: ct_exists_nat => t2R t2L H2.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Ha j)) (ct_decide_lt _ _ _ _ (Ha j) H2))).
  apply: ct_and; first exact (sub_nat_le_correspondence _ _ _ _ H2 (sub_add_correspondence _ _ _ _ H1 HL)).
  exact (BI j t1R t1L H1 t2R t2L H2).
Qed.

End JISEQARDSched.

End JISEQARDDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Module LS := prosa.classic.model.schedule.uni.limited.schedule.

Section JISEQLSDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CerParRel Job cR cL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CerArrRel Job arrR arrL.
Variables (lR : Job -> nat) (lL : Job -> Lean.Nat).
Hypothesis Hl : CerParRel Job lR lL.

Lemma cer_LS_job_lock_in_service_positive :
  PropSPropRel (LS.job_lock_in_service_positive cR arrR lR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_lock_in_service_positive Job dJ cL arrL lL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cer_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cer_J_job_cost_positive Job cR cL Hc j)).
  exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hl j)).
Qed.

Lemma cer_LS_job_lock_in_service_le_job_cost :
  PropSPropRel (LS.job_lock_in_service_le_job_cost cR arrR lR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_lock_in_service_le_job_cost Job dJ cL arrL lL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cer_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cer_J_job_cost_positive Job cR cL Hc j)).
  exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (Hc j)).
Qed.

Section JISEQLSSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.

Lemma cer_LS_job_nonpreemptive_after_lock_in_service :
  PropSPropRel (LS.job_nonpreemptive_after_lock_in_service cR arrR sR lR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_nonpreemptive_after_lock_in_service Job dJ cL arrL sL lL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (cer_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht Ht').
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (cer_US_service Job sR sL Hs j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (cer_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht'))).
  exact (ct_bool_truth _ _ (cer_US_scheduled_at Job sR sL Hs j _ _ Ht')).
Qed.

Lemma cer_LS_proper_job_lock_in_service :
  PropSPropRel (LS.proper_job_lock_in_service cR arrR sR lR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_proper_job_lock_in_service Job dJ cL arrL sL lL).
Proof.
  apply: ct_and; first exact cer_LS_job_lock_in_service_positive.
  apply: ct_and; first exact cer_LS_job_lock_in_service_le_job_cost.
  exact cer_LS_job_nonpreemptive_after_lock_in_service.
Qed.

End JISEQLSSched.

Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat) (tlR : Task -> nat) (tlL : Task -> Lean.Nat).
Hypotheses (Htc : CerParRel Task tcR tcL) (Htl : CerParRel Task tlR tlL).

Lemma cer_LS_task_lock_in_service_le_task_cost tsk :
  PropSPropRel (LS.task_lock_in_service_le_task_cost tcR tlR tsk) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_task_lock_in_service_le_task_cost Task dT tcL tlL tsk).
Proof. exact (sub_nat_le_correspondence _ _ _ _ (Htl tsk) (Htc tsk)). Qed.

Lemma cer_LS_task_lock_in_service_bounds_job_lock_in_service (job_task : Job -> Task) tsk :
  PropSPropRel (LS.task_lock_in_service_bounds_job_lock_in_service job_task arrR lR tlR tsk)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_task_lock_in_service_bounds_job_lock_in_service Task dT Job dJ job_task arrL lL tlL tsk).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cer_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (Htl tsk)).
Qed.

Lemma cer_LS_proper_task_lock_in_service (job_task : Job -> Task) tsk :
  PropSPropRel (LS.proper_task_lock_in_service tcR job_task arrR lR tlR tsk)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_proper_task_lock_in_service Task dT tcL Job dJ job_task arrL lL tlL tsk).
Proof.
  apply: ct_and; first exact (cer_LS_task_lock_in_service_le_task_cost tsk).
  exact (cer_LS_task_lock_in_service_bounds_job_lock_in_service job_task tsk).
Qed.

End JISEQLSDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JISEQSVDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.

Lemma cer_SV_service_of_jobs jobsR jobsL (Hj : ClListRel cid jobsR jobsL) pR pL (Hp : CerPredRel Job pR pL)
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.service_of_jobs sR jobsR pR t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs Job dJ sL jobsL pL t1L t2L).
Proof.
  exact (cer_sum_filtered_rel Job (fun j => UniprocessorSchedule.service_during sR j t1R t2R)
           (fun j => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L)
           (fun j => cer_US_service_during Job sR sL Hs j _ _ H1 _ _ H2) pR pL Hp _ _ Hj).
Qed.

Lemma cer_SV_task_service_of_jobs_received_in (Task : eqType) (job_task : Job -> Task)
    arrR arrL (Harr : CerArrRel Job arrR arrL) tsk a1R a1L (Ha1 : SubNatRel a1R a1L) a2R a2L (Ha2 : SubNatRel a2R a2L)
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.task_service_of_jobs_received_in job_task arrR sR tsk a1R a2R t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_task_service_of_jobs_received_in Task (ct_decidable_eq Task) Job dJ job_task arrL sL tsk a1L a2L t1L t2L).
Proof.
  exact (cer_SV_service_of_jobs _ _ (cer_jobs_arrived_between Job arrR arrL Harr _ _ _ _ Ha1 Ha2)
           _ _ (fun j => ct_decide_eq Task (job_task j) tsk) _ _ H1 _ _ H2).
Qed.

Lemma cer_SV_task_service_between (Task : eqType) (job_task : Job -> Task)
    arrR arrL (Harr : CerArrRel Job arrR arrL) tsk t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.task_service_between job_task arrR sR tsk t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_task_service_between Task (ct_decidable_eq Task) Job dJ job_task arrL sL tsk t1L t2L).
Proof. exact (cer_SV_task_service_of_jobs_received_in Task job_task arrR arrL Harr tsk _ _ H1 _ _ H2 _ _ H1 _ _ H2). Qed.

End JISEQSVDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JISEQSTDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.
Variable job_task : Job -> Task.

Lemma cer_ST_task_scheduled_at tsk tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleOfTask.task_scheduled_at job_task sR tsk tR) (I.Prosa_Classic_Model_Schedule_Uni_ScheduleOfTask_ScheduleOfTask_task_scheduled_at Task dT Job dJ job_task sL tsk tL).
Proof.
  refine (cer_trs (Hs tR tL Ht)
            (fun z => CtBoolRel (ScheduleOfTask.task_scheduled_at job_task sR tsk tR)
                        (match z with
                         | I.Option_some j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk)
                         | I.Option_none => I.Bool_false end)) _).
  rewrite /ScheduleOfTask.task_scheduled_at. destruct (sR tR) as [x|].
  - exact (ct_decide_eq Task (job_task x) tsk).
  - exact (ct_bool_canonical false).
Qed.

End JISEQSTDefs.

(* ------------------------------------------------------------------ *)
(** * [has] against [List.any] *)

Lemma cer_has_eq (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL x)) :
  forall s, Logic.eq (I.List_any T (cl_map cid s) pL) (ct_b2l (has pR s)).
Proof.
  elim => [|x s IH]; first reflexivity.
  have -> : Logic.eq (I.List_any T (cl_map cid (x :: s)) pL) (I.Bool_or (pL x) (I.List_any T (cl_map cid s) pL)).
  { cbn. destruct (pL x); reflexivity. }
  rewrite (ct_bool_rel_logic _ _ (Hp x)) IH /=. by case: (pR x); case: (has pR s).
Qed.

Lemma cer_has (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL x)) :
  forall s, CtBoolRel (has pR s) (I.List_any T (cl_map cid s) pL).
Proof. intro s. exact (coq_eq_to_imported_eq _ _ (Logic.eq_sym (cer_has_eq T pR pL Hp s))). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JISEQDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CerParRel Job aR aL) (Hc : CerParRel Job cR cL).
Variable job_task : Job -> Task.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CerArrRel Job arrR arrL.
Variables (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat).
Hypotheses (Hi : CerIntRel Job iR iL) (Hw : CerWlRel Job wR wL).
Notation BI := (cer_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw).

Lemma cer_SEQ_interference_and_workload_consistent_with_sequential_jobs tsk :
  PropSPropRel (@AbstractSeqRTA.interference_and_workload_consistent_with_sequential_jobs Task Job aR cR job_task arrR sR tsk iR wR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_interference_and_workload_consistent_with_sequential_jobs Task dT Job dJ aL cL job_task arrL sL tsk iL wL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cer_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  apply: ct_imp; first exact (BI j t1R t1L H1 t2R t2L H2).
  exact (sub_nat_eq_correspondence _ _ _ _ (cer_WL_task_workload_between Task Job cR cL Hc job_task arrR arrL Harr tsk _ _ (sub_nat_rel_canonical 0) _ _ H1)
           (cer_SV_task_service_between Job sR sL Hs Task job_task arrR arrL Harr tsk _ _ (sub_nat_rel_canonical 0) _ _ H1)).
Qed.

Lemma cer_SEQ_task_interference_received_before tsk uR uL (Hu : SubNatRel uR uL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@AbstractSeqRTA.task_interference_received_before Task Job job_task arrR sR iR tsk uR tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_task_interference_received_before Task dT Job dJ job_task arrL sL iL tsk uL tL).
Proof.
  apply: ct_bool_and; first exact (ct_bool_not _ _ (cer_ST_task_scheduled_at Task Job sR sL Hs job_task tsk tR tL Ht)).
  refine (cer_trs (cer_TA_arrivals_of_task_before Task Job job_task arrR arrL Harr tsk uR uL Hu)
            (fun z => CtBoolRel _ (I.List_any Job z (fun j => iL j tL))) _).
  exact (cer_has Job _ _ (fun j => Hi j tR tL Ht) _).
Qed.

Lemma cer_SEQ_cumul_task_interference tsk uR uL (Hu : SubNatRel uR uL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (@AbstractSeqRTA.cumul_task_interference Task Job job_task arrR sR iR tsk uR t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_cumul_task_interference Task dT Job dJ job_task arrL sL iL tsk uL t1L t2L).
Proof.
  exact (cer_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (cer_SEQ_task_interference_received_before tsk uR uL Hu kR kL Hk))).
Qed.

Lemma cer_SEQ_task_interference_is_bounded_by tsk fR fL (Hf : CerIbfRel Task fR fL) :
  PropSPropRel (@AbstractSeqRTA.task_interference_is_bounded_by Task Job aR cR job_task arrR sR tsk iR wR fR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_task_interference_is_bounded_by Task dT Job dJ aL cL job_task arrL sL tsk iL wL fL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => RR RL HR.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cer_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  have H1R := sub_add_correspondence _ _ _ _ H1 HR.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ H1R H2).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (cer_US_completed_by Job sR sL Hs cR cL Hc j _ _ H1R))).
  apply: ct_imp; first exact (BI j t1R t1L H1 t2R t2L H2).
  cbv zeta.
  exact (sub_nat_le_correspondence _ _ _ _ (cer_SEQ_cumul_task_interference tsk _ _ H2 _ _ H1 _ _ H1R)
           (Hf tsk _ _ (ct_sub_rel _ _ _ _ (Ha j) H1) _ _ HR)).
Qed.

End JISEQDefs.

(* ------------------------------------------------------------------ *)
(** * Service of jobs (as in the accepted classic uniprocessor service certificate) *)

Section JILBISvc.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.

Lemma cer_service_of_jobs jobsR jobsL (Hj : ClListRel cid jobsR jobsL) pR pL (Hp : CerPredRel Job pR pL)
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.service_of_jobs sR jobsR pR t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs Job dJ sL jobsL pL t1L t2L).
Proof.
  exact (cer_sum_filtered_rel Job (fun j => UniprocessorSchedule.service_during sR j t1R t2R)
           (fun j => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L)
           (fun j => cer_US_service_during Job sR sL Hs j _ _ H1 _ _ H2) pR pL Hp _ _ Hj).
Qed.

End JILBISvc.

(* ------------------------------------------------------------------ *)
(** * Auxiliary relations *)

Lemma cer_implb aR aL (Ha : CtBoolRel aR aL) bR bL (Hb : CtBoolRel bR bL) :
  CtBoolRel (aR ==> bR) (I.Bool_or (I.Bool_not aL) bL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite (ct_bool_rel_logic _ _ Ha) (ct_bool_rel_logic _ _ Hb). clear Ha Hb.
  by case: aR; case: bR.
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JILBIDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CerParRel Job jaR jaL) (Hc : CerParRel Job cR cL).
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CerArrRel Job aR aL.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.
Variables (hR : Job -> Job -> bool) (hL : Job -> Job -> I.Bool).
Hypothesis Hh : CerRelRel Job hR hL.

Lemma cer_LBI_quiet_time j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (@BusyIntervalJLFP.quiet_time Job jaR cR aR sR hR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_quiet_time Job dJ jaL cL aL sL hL j tL).
Proof.
  apply: ct_forall_identity => j_hp.
  apply: ct_imp; first exact (cer_arrives_in Job aR aL Ha j_hp).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hh j_hp j)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cer_arrived_before Job jaR jaL Hja j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (cer_US_completed_by Job sR sL Hs cR cL Hc j_hp tR tL Ht)).
Qed.

Notation QT := cer_LBI_quiet_time.

Lemma cer_not_quiet j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (~ @BusyIntervalJLFP.quiet_time Job jaR cR aR sR hR j tR) (I.Not (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_quiet_time Job dJ jaL cL aL sL hL j tL)).
Proof. exact (ct_imp _ _ _ _ (QT j tR tL Ht) cer_false_rel). Qed.

Lemma cer_LBI_busy_interval_prefix j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (@BusyIntervalJLFP.busy_interval_prefix Job jaR cR aR sR hR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_busy_interval_prefix Job dJ jaL cL aL sL hL j t1L t2L).
Proof.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ H1 H2).
  apply: ct_and; first exact (QT j t1R t1L H1).
  apply: ct_and.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
    exact (cer_not_quiet j tR tL Ht). }
  exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Hja j)) (ct_decide_lt _ _ _ _ (Hja j) H2))).
Qed.

Lemma cer_LBI_is_priority_inversion j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@BusyIntervalJLFP.is_priority_inversion Job sR hR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_is_priority_inversion Job dJ sL hL j tL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite /BusyIntervalJLFP.is_priority_inversion. unfold I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_is_priority_inversion.
  rewrite -(imported_eq_to_coq_eq _ _ (Hs tR tL Ht)).
  case: (sR tR) => [jlp|]; last reflexivity.
  cbn. rewrite (ct_bool_rel_logic _ _ (Hh jlp j)). by case: (hR jlp j).
Qed.

Lemma cer_LBI_cumulative_priority_inversion j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (@BusyIntervalJLFP.cumulative_priority_inversion Job sR hR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_cumulative_priority_inversion Job dJ sL hL j t1L t2L).
Proof.
  exact (cer_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (cer_LBI_is_priority_inversion j kR kL Hk))).
Qed.

Lemma cer_LBI_priority_inversion_of_job_is_bounded_by j BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (@BusyIntervalJLFP.priority_inversion_of_job_is_bounded_by Job jaR cR aR sR hR j BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_priority_inversion_of_job_is_bounded_by Job dJ jaL cL aL sL hL j BL).
Proof.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cer_LBI_busy_interval_prefix j t1R t1L H1 t2R t2L H2).
  exact (sub_nat_le_correspondence _ _ _ _ (cer_LBI_cumulative_priority_inversion j t1R t1L H1 t2R t2L H2) HB).
Qed.

Lemma cer_LBI_priority_inversion_is_bounded_by (Task : eqType) (job_task : Job -> Task) tsk BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (@BusyIntervalJLFP.priority_inversion_is_bounded_by Task Job jaR cR job_task aR sR hR tsk BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_priority_inversion_is_bounded_by Task (ct_decidable_eq Task) Job dJ jaL cL job_task aL sL hL tsk BL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cer_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  exact (cer_LBI_priority_inversion_of_job_is_bounded_by j BR BL HB).
Qed.

Lemma cer_LP_work_conserving :
  PropSPropRel (LimitedPreemptionPlatform.work_conserving jaR cR aR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_work_conserving Job dJ jaL cL aL sL).
Proof. exact (cer_UP_work_conserving Job sR sL Hs jaR jaL Hja cR cL Hc aR aL Ha). Qed.

End JILBIDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cer_arriving_at (Job : eqType) aR aL (Ha : CerArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arriving_at aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arriving_at Job (ct_decidable_eq Job) aL tL).
Proof. exact (Ha tR tL Ht). Qed.

Section JIDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.
Variables (hR : Job -> Job -> bool) (hL : Job -> Job -> I.Bool).
Hypothesis Hh : CerRelRel Job hR hL.
Variable job_task : Job -> Task.

Lemma cer_JI_is_interference_from_another_job_with_higher_eq_priority j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@JLFPInstantiation.is_interference_from_another_job_with_higher_eq_priority Job sR hR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_is_interference_from_another_job_with_higher_eq_priority Job dJ sL hL j tL).
Proof.
  refine (cer_trs (Hs tR tL Ht) (fun z => CtBoolRel _ (match z with
      | I.Option_some jhp => I.Bool_and (hL jhp j) (I.Bool_not (I.Decidable_decide (Lean.eq jhp j) (dJ jhp j)))
      | I.Option_none => I.Bool_false end)) _).
  rewrite /JLFPInstantiation.is_interference_from_another_job_with_higher_eq_priority. destruct (sR tR) as [x|]; cbn.
  - exact (ct_bool_and _ _ _ _ (Hh x j) (ct_bool_not _ _ (ct_decide_eq Job x j))).
  - exact (ct_bool_canonical false).
Qed.

Lemma cer_JI_interference :
  CerIntRel Job (@JLFPInstantiation.interference Job sR hR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_interference Job dJ sL hL).
Proof.
  intros j tR tL Ht.
  exact (ct_bool_or _ _ _ _ (cer_LBI_is_priority_inversion Job sR sL Hs hR hL Hh j tR tL Ht)
           (cer_JI_is_interference_from_another_job_with_higher_eq_priority j tR tL Ht)).
Qed.

Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CerParRel Job cR cL.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CerArrRel Job aR aL.

Lemma cer_JI_interfering_workload_of_jobs_with_hep_priority j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (@JLFPInstantiation.interfering_workload_of_jobs_with_hep_priority Job cR aR hR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_interfering_workload_of_jobs_with_hep_priority Job dJ cL aL hL j tL).
Proof.
  exact (cer_sum_filtered_rel Job cR cL Hc _ _ (fun x => ct_bool_and _ _ _ _ (Hh x j) (ct_bool_not _ _ (ct_decide_eq Job x j)))
           _ _ (Ha tR tL Ht)).
Qed.

Lemma cer_JI_interfering_workload :
  CerWlRel Job (@JLFPInstantiation.interfering_workload Job cR aR sR hR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_interfering_workload Job dJ cL aL sL hL).
Proof.
  intros j tR tL Ht.
  exact (sub_add_correspondence _ _ _ _ (ct_bool_to_nat _ _ (cer_LBI_is_priority_inversion Job sR sL Hs hR hL Hh j tR tL Ht))
           (cer_JI_interfering_workload_of_jobs_with_hep_priority j tR tL Ht)).
Qed.

End JIDefs.

(* ------------------------------------------------------------------ *)
(** * Preemption models *)

Section LPDPmRel.
Variable Job : eqType.
Definition CerPmRel__LPDPmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma cer_pm_canonical__LPDPmRel pR : CerPmRel__LPDPmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cer_pm_surjective__LPDPmRel pL : CerPmRel__LPDPmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cer_forall_pm__LPDPmRel (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CerPmRel__LPDPmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (cer_forall_cover _ _ CerPmRel__LPDPmRel _ _ cer_pm_canonical__LPDPmRel cer_pm_surjective__LPDPmRel PR PL). Qed.

End LPDPmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LPDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CerPmRel Job pR pL.

Notation SA := (cer_US_scheduled_at Job sR sL Hs).
Notation SV := (cer_US_service Job sR sL Hs).

End LPDDefs.

Section LPDDefs2.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CerPmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : CerParRel Job cR cL) (Hm : CerParRel Job mR mL) (Htm : CerParRel Task tmR tmL).

End LPDDefs2.

Lemma cer_LPD_work_conserving (Job : eqType) sR sL (Hs : CerSchedRel Job sR sL) cR cL (Hc : CerParRel Job cR cL)
    c0R c0L (Hc0 : CerParRel Job c0R c0L) arrR arrL (Harr : CerArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.work_conserving cR c0R arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_work_conserving Job (ct_decidable_eq Job) cL c0L arrL sL).
Proof. exact (cer_UP_work_conserving Job sR sL Hs cR cL Hc c0R c0L Hc0 arrR arrL Harr). Qed.

Section LPDResp.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CerSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CerParRel Job aR aL) (Hc : CerParRel Job cR cL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CerArrRel Job arrR arrL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CerPmRel Job pR pL.

End LPDResp.

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

(* ------------------------------------------------------------------ *)
(** * The relative deadline [job_relative_dealine] (Lean helper of the EDF priority: the task deadline of the job's
    task) *)
Lemma cer_jrd (Task Job : eqType) pR pL (Hp : CerParRel Task pR pL) (job_task : Job -> Task) j :
  SubNatRel (pR (job_task j))
    (I.Prosa_Classic_Model_Priority_Priority_job_relative_dealine Task (ct_decidable_eq Task) pL Job (ct_decidable_eq Job) job_task j).
Proof. exact (Hp (job_task j)). Qed.
(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem AbstractRTAforEDFwithArrivalCurves_task_rbf_changes_at_correspondence (Task : eqType) tcR tcL (Htc : CerParRel Task tcR tcL)
    mR mL (Hm : CerCurveRel Task mR mL) tsk AR AL (HA : SubNatRel AR AL) :
  CtBoolRel (@AbstractRTAforEDFwithArrivalCurves.task_rbf_changes_at Task tcR mR tsk AR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_ResponseTimeBound_AbstractRTAforEDFwithArrivalCurves_task_rbf_changes_at Task (ct_decidable_eq Task) tcL mL tsk AL).
Proof.
  have W := cer_WB_task_request_bound_function Task tcR tcL Htc mR mL Hm.
  exact (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _ (W tsk _ _ HA)
    (W tsk _ _ (sub_add_correspondence _ _ _ _ HA (sub_nat_rel_canonical 1))))).
Qed.

Theorem AbstractRTAforEDFwithArrivalCurves_bound_on_total_hep_workload_changes_at_correspondence (Task : eqType) tcR tcL (Htc : CerParRel Task tcR tcL)
    tdR tdL (Htd : CerParRel Task tdR tdL) tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL)
    mR mL (Hm : CerCurveRel Task mR mL) tsk AR AL (HA : SubNatRel AR AL) :
  CtBoolRel (@AbstractRTAforEDFwithArrivalCurves.bound_on_total_hep_workload_changes_at Task tcR tdR tsR mR tsk AR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_ResponseTimeBound_AbstractRTAforEDFwithArrivalCurves_bound_on_total_hep_workload_changes_at Task (ct_decidable_eq Task) tcL tdL tsL mL tsk AL).
Proof.
  have W := cer_WB_task_request_bound_function Task tcR tcL Htc mR mL Hm.
  rewrite -(imported_eq_to_coq_eq _ _ Hts).
  refine (cer_has Task _ _ (fun tsko => _) tsR).
  exact (ct_bool_and _ _ _ _ (ct_bool_not _ _ (ct_decide_eq Task tsk tsko))
    (ct_bool_not _ _ (ct_decide_eq_nat _ _ _ _
      (W tsko _ _ (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ HA (Htd tsk)) (Htd tsko)))
      (W tsko _ _ (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _
          (sub_add_correspondence _ _ _ _ HA (sub_nat_rel_canonical 1)) (Htd tsk)) (Htd tsko)))))).
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
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CerParRel _ f g |- _ => exact (H x) end
  | |- CtBoolRel (?f ?x ?y) (?g ?x ?y) => match goal with H : CerRelRel _ f g |- _ => exact (H x y) end
  | |- CtBoolRel (?f ?x ?t) (?g ?x ?u) => match goal with H : CerPmRel _ f g |- _ => eapply H end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | ArrivalSequence.arrival_sequence _ => apply: (cer_forall_arr _); intros ? ? ?
  | UniprocessorSchedule.schedule _ => apply: (cer_forall_sched _); intros ? ? ?
  | Priority.FP_policy _ => apply: (cer_forall_rel _); intros ? ? ?
  | Priority.JLFP_policy _ => apply: (cer_forall_rel _); intros ? ? ?
  | seq _ => apply: (cer_forall_list _); intros ? ? ?
  | _ -> nat -> nat => apply: (cer_forall_curve _); intros ? ? ?
  | _ -> Time.time -> nat => apply: (cer_forall_curve _); intros ? ? ?
  | _ -> nat -> bool => apply: (cer_forall_pm _); intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: cer_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp; crel
  | lazymatch goal with
    | |- forall _, _ => intro; crel
    | |- SubNatRel _ (I.Prosa_Classic_Model_Priority_Priority_job_relative_dealine _ _ _ _ _ _ _) => eapply cer_jrd; crel
    | |- CerIntRel _ (JLFPInstantiation.interference _ _) _ => eapply cer_JI_interference; crel
    | |- CerWlRel _ (JLFPInstantiation.interfering_workload _ _ _ _) _ => eapply cer_JI_interfering_workload; crel
    | |- CerRelRel _ (Priority.FP_to_JLFP _ _) _ => fail; crel
    | |- CerRelRel _ (Priority.EDF _ _) _ => eapply cer_PR_EDF; crel
    | |- CerIntRel _ (fun _ => _) _ => eapply cer_JI_interference; crel
    | |- CerWlRel _ (fun _ => _) _ => eapply cer_JI_interfering_workload; crel
    | |- CerRelRel _ (fun _ => _) _ => first [ fail; crel | eapply cer_PR_EDF; crel | intros ? ?; cbv beta; crel ]
    | |- CtBoolRel (orb _ _) _ => eapply ct_bool_or; crel
    | |- CerFunRel _ _ => intros ? ? ?; cbv beta; crel
    | |- CerNatFunRel _ _ => intros ? ? ?; cbv beta; crel
    | |- CerIbfRel _ _ _ => intros ? ? ? ? ? ? ?; cbv beta; crel
    | |- CerPredRel _ _ _ => intro; cbv beta; crel
    | |- CerParRel _ (fun _ => _) _ => intro; cbv beta; crel
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
  | S _ => eapply cer_succ_rel; crel
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
  | _ <-> _ => eapply cer_iff; crel
  | _ <> _ => eapply cer_ne
  | ~ _ => eapply ct_imp; [crel | exact cer_false_rel]
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else crel_eq_defs
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_eq_defs := first [ eapply ct_eq_rel | fail; crel ]
with crel_n_defs := first [ (match goal with |- context [@MaxArrivalsWorkloadBound.task_request_bound_function] => idtac end; eapply cer_WB_task_request_bound_function; crel)
    | (match goal with |- context [@MaxArrivalsWorkloadBound.total_request_bound_function] => idtac end; eapply cer_WB_total_request_bound_function; crel)
    | eapply cer_ico; crel
    | eapply ct_bool_to_nat; crel
    | (match goal with |- context [@AbstractRTADefinitions.cumul_interference] => idtac end; eapply cer_ARD_cumul_interference; crel)
    | (match goal with |- context [@AbstractRTADefinitions.cumul_interfering_workload] => idtac end; eapply cer_ARD_cumul_interfering_workload; crel)
    | (match goal with |- context [@AbstractSeqRTA.cumul_task_interference] => idtac end; eapply cer_SEQ_cumul_task_interference; crel)
    | (match goal with |- context [@Service.service_of_jobs] => idtac end; eapply cer_SV_service_of_jobs; crel)
    | (match goal with |- context [@Workload.workload_of_jobs] => idtac end; eapply cer_WL_workload_of_jobs; crel)
    | (match goal with |- context [@BusyIntervalJLFP.cumulative_priority_inversion] => idtac end; eapply cer_LBI_cumulative_priority_inversion; crel)
    | eapply cer_sum_filtered_rel; crel
    | eapply cer_sum_rel; crel
    | eapply cib_min_rel; crel
    | (match goal with |- context [@UniprocessorSchedule.service] => idtac end; eapply cer_US_service; crel)
    | (match goal with |- context [@UniprocessorSchedule.service_during] => idtac end; eapply cer_US_service_during; crel)
    | (match goal with |- context [@UniprocessorSchedule.service_at] => idtac end; eapply cer_US_service_at; crel) ]
with crel_b_defs := first [ (match goal with |- context [@AbstractSeqRTA.task_interference_received_before] => idtac end; eapply cer_SEQ_task_interference_received_before; crel)
    | (match goal with |- context [@BusyIntervalJLFP.is_priority_inversion] => idtac end; eapply cer_LBI_is_priority_inversion; crel)
    | (match goal with |- context [@AbstractRTAReduction.is_in_search_space] => idtac end; eapply cer_RS_is_in_search_space; crel)
    | (match goal with |- context [@AbstractRTAforEDFwithArrivalCurves.task_rbf_changes_at] => idtac end; eapply AbstractRTAforEDFwithArrivalCurves_task_rbf_changes_at_correspondence; crel)
    | (match goal with |- context [@AbstractRTAforEDFwithArrivalCurves.bound_on_total_hep_workload_changes_at] => idtac end; eapply AbstractRTAforEDFwithArrivalCurves_bound_on_total_hep_workload_changes_at_correspondence; crel)
    | (match goal with |- context [@UniprocessorSchedule.scheduled_at] => idtac end; eapply cer_US_scheduled_at; crel)
    | (match goal with |- context [@UniprocessorSchedule.completed_by] => idtac end; eapply cer_US_completed_by; crel)
    | (match goal with |- context [@UniprocessorSchedule.pending] => idtac end; eapply cer_US_pending; crel)
    | (match goal with |- context [@UniprocessorSchedule.backlogged] => idtac end; eapply cer_US_backlogged; crel)
    | (match goal with |- context [@UniprocessorSchedule.pending_earlier_and_at] => idtac end; eapply cer_US_pending_earlier_and_at; crel)
    | (match goal with |- context [@ArrivalSequence.has_arrived] => idtac end; eapply cer_has_arrived; crel)
    | (match goal with |- context [@ArrivalSequence.arrived_before] => idtac end; eapply cer_arrived_before; crel)
    | (match goal with |- context [@ArrivalSequence.arrives_at] => idtac end; eapply cer_arrives_at; crel)
    | (match goal with |- context [@Job.job_cost_positive] => idtac end; eapply cer_J_job_cost_positive; crel)
    | (match goal with |- context [@Job.job_cost_le_task_cost] => idtac end; eapply cer_J_job_cost_le_task_cost; crel)
    | (match goal with |- context [@TaskArrival.is_job_of_task] => idtac end; eapply cer_TA_is_job_of_task; crel) ]
with crel_l_defs := first [ (match goal with |- context [@ArrivalSequence.jobs_arrived_between] => idtac end; eapply cer_jobs_arrived_between; crel)
    | (match goal with |- context [@ArrivalSequence.jobs_arriving_at] => idtac end; eapply cer_arriving_at; crel) ]
with crel_p_defs := first [ (match goal with |- context [@AbstractRTADefinitions.work_conserving] => idtac end; eapply cer_ARD_work_conserving; crel)
    | (match goal with |- context [@AbstractRTADefinitions.busy_intervals_are_bounded_by] => idtac end; eapply cer_ARD_busy_intervals_are_bounded_by; crel)
    | (match goal with |- context [@AbstractRTADefinitions.quiet_time] => idtac end; eapply cer_ARD_quiet_time; crel)
    | (match goal with |- context [@AbstractRTADefinitions.busy_interval] => idtac end; eapply cer_ARD_busy_interval; crel)
    | (match goal with |- context [@AbstractSeqRTA.interference_and_workload_consistent_with_sequential_jobs] => idtac end; eapply cer_SEQ_interference_and_workload_consistent_with_sequential_jobs; crel)
    | (match goal with |- context [@AbstractSeqRTA.task_interference_is_bounded_by] => idtac end; eapply cer_SEQ_task_interference_is_bounded_by; crel)
    | (match goal with |- context [@BusyIntervalJLFP.priority_inversion_is_bounded_by] => idtac end; eapply cer_LBI_priority_inversion_is_bounded_by; crel)
    | (match goal with |- context [@BusyIntervalJLFP.quiet_time] => idtac end; eapply cer_LBI_quiet_time; crel)
    | (match goal with |- context [@BusyIntervalJLFP.busy_interval_prefix] => idtac end; eapply cer_LBI_busy_interval_prefix; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.work_conserving] => idtac end; eapply cer_LP_work_conserving; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.work_conserving] => idtac end; eapply cer_LPD_work_conserving; crel)
    | (match goal with |- context [@LS.job_lock_in_service_positive] => idtac end; eapply cer_LS_job_lock_in_service_positive; crel)
    | (match goal with |- context [@LS.job_lock_in_service_le_job_cost] => idtac end; eapply cer_LS_job_lock_in_service_le_job_cost; crel)
    | (match goal with |- context [@LS.job_nonpreemptive_after_lock_in_service] => idtac end; eapply cer_LS_job_nonpreemptive_after_lock_in_service; crel)
    | (match goal with |- context [@LS.proper_job_lock_in_service] => idtac end; eapply cer_LS_proper_job_lock_in_service; crel)
    | (match goal with |- context [@LS.task_lock_in_service_le_task_cost] => idtac end; eapply cer_LS_task_lock_in_service_le_task_cost; crel)
    | (match goal with |- context [@LS.task_lock_in_service_bounds_job_lock_in_service] => idtac end; eapply cer_LS_task_lock_in_service_bounds_job_lock_in_service; crel)
    | (match goal with |- context [@LS.proper_task_lock_in_service] => idtac end; eapply cer_LS_proper_task_lock_in_service; crel)
    | (match goal with |- context [@ArrivalCurves.family_of_proper_arrival_curves] => idtac end; eapply cer_AC_family_of_proper_arrival_curves; crel)
    | (match goal with |- context [@ArrivalCurves.is_arrival_bound] => idtac end; eapply cer_AC_is_arrival_bound; crel)
    | (match goal with |- context [@ArrivalCurves.proper_arrival_curve] => idtac end; eapply cer_AC_proper_arrival_curve; crel)
    | (match goal with |- context [@AbstractRTAReduction.are_not_equivalent_at_values_less_than] => idtac end; eapply cer_RS_are_not_equivalent_at_values_less_than; crel)
    | (match goal with |- context [@AbstractRTAReduction.is_in_search_space] => idtac end; eapply cer_RS_is_in_search_space; crel)
    | (match goal with |- context [@iff] => idtac end; eapply cer_iff; crel)
    | (match goal with |- context [@ArrivalSequence.arrives_in] => idtac end; eapply cer_arrives_in; crel)
    | (match goal with |- context [@ArrivalSequence.arrival_times_are_consistent] => idtac end; eapply cer_consistent; crel)
    | (match goal with |- context [@ArrivalSequence.arrival_sequence_is_a_set] => idtac end; eapply cer_is_a_set; crel)
    | eapply cer_mem; crel
    | eapply cer_uniq; crel
    | (match goal with |- context [@UniprocessorSchedule.jobs_come_from_arrival_sequence] => idtac end; eapply cer_US_jobs_come_from_arrival_sequence; crel)
    | (match goal with |- context [@UniprocessorSchedule.jobs_must_arrive_to_execute] => idtac end; eapply cer_US_jobs_must_arrive_to_execute; crel)
    | (match goal with |- context [@UniprocessorSchedule.completed_jobs_dont_execute] => idtac end; eapply cer_US_completed_jobs_dont_execute; crel)
    | (match goal with |- context [@UniprocessorSchedule.sequential_jobs] => idtac end; eapply cer_US_sequential_jobs; crel)
    | (match goal with |- context [@Job.cost_of_jobs_from_arrival_sequence_le_task_cost] => idtac end; eapply cer_J_cost_of_jobs_from_arrival_sequence_le_task_cost; crel)
    | (match goal with |- context [@ResponseTime.is_response_time_bound_of_job] => idtac end; eapply cer_RT_is_response_time_bound_of_job; crel)
    | (match goal with |- context [@ResponseTime.is_response_time_bound_of_task] => idtac end; eapply cer_RT_is_response_time_bound_of_task; crel) ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_instantiated_i_and_w_are_coherent_with_schedule (Task Job : eqType) : Prop :=
  forall p0 : Task -> nat,
    ltac:(type_of_term (@AbstractRTAforEDFwithArrivalCurves.instantiated_i_and_w_are_coherent_with_schedule Task p0 Job)).
Definition tgt_instantiated_i_and_w_are_coherent_with_schedule (Task Job : eqType) : SProp :=
  forall p0 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_ResponseTimeBound_AbstractRTAforEDFwithArrivalCurves_instantiated_i_and_w_are_coherent_with_schedule Task (ct_decidable_eq Task) p0 Job (ct_decidable_eq Job))).
Theorem AbstractRTAforEDFwithArrivalCurves_instantiated_i_and_w_are_coherent_with_schedule_correspondence (Task Job : eqType) :
  PropSPropRel (src_instantiated_i_and_w_are_coherent_with_schedule Task Job) (tgt_instantiated_i_and_w_are_coherent_with_schedule Task Job).
Proof. unfold src_instantiated_i_and_w_are_coherent_with_schedule, tgt_instantiated_i_and_w_are_coherent_with_schedule. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_instantiated_interference_and_workload_consistent_with_sequential_jobs (Task Job : eqType) : Prop :=
  forall p0 : Task -> nat,
    ltac:(type_of_term (@AbstractRTAforEDFwithArrivalCurves.instantiated_interference_and_workload_consistent_with_sequential_jobs Task p0 Job)).
Definition tgt_instantiated_interference_and_workload_consistent_with_sequential_jobs (Task Job : eqType) : SProp :=
  forall p0 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_ResponseTimeBound_AbstractRTAforEDFwithArrivalCurves_instantiated_interference_and_workload_consistent_with_sequential_jobs Task (ct_decidable_eq Task) p0 Job (ct_decidable_eq Job))).
Theorem AbstractRTAforEDFwithArrivalCurves_instantiated_interference_and_workload_consistent_with_sequential_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_instantiated_interference_and_workload_consistent_with_sequential_jobs Task Job) (tgt_instantiated_interference_and_workload_consistent_with_sequential_jobs Task Job).
Proof. unfold src_instantiated_interference_and_workload_consistent_with_sequential_jobs, tgt_instantiated_interference_and_workload_consistent_with_sequential_jobs. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_instantiated_busy_intervals_are_bounded (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@AbstractRTAforEDFwithArrivalCurves.instantiated_busy_intervals_are_bounded Task p0 p1 Job)).
Definition tgt_instantiated_busy_intervals_are_bounded (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_ResponseTimeBound_AbstractRTAforEDFwithArrivalCurves_instantiated_busy_intervals_are_bounded Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem AbstractRTAforEDFwithArrivalCurves_instantiated_busy_intervals_are_bounded_correspondence (Task Job : eqType) :
  PropSPropRel (src_instantiated_busy_intervals_are_bounded Task Job) (tgt_instantiated_busy_intervals_are_bounded Task Job).
Proof. unfold src_instantiated_busy_intervals_are_bounded, tgt_instantiated_busy_intervals_are_bounded. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_instantiated_task_interference_is_bounded (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@AbstractRTAforEDFwithArrivalCurves.instantiated_task_interference_is_bounded Task p0 p1 Job)).
Definition tgt_instantiated_task_interference_is_bounded (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_ResponseTimeBound_AbstractRTAforEDFwithArrivalCurves_instantiated_task_interference_is_bounded Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem AbstractRTAforEDFwithArrivalCurves_instantiated_task_interference_is_bounded_correspondence (Task Job : eqType) :
  PropSPropRel (src_instantiated_task_interference_is_bounded Task Job) (tgt_instantiated_task_interference_is_bounded Task Job).
Proof. unfold src_instantiated_task_interference_is_bounded, tgt_instantiated_task_interference_is_bounded. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_A_is_in_concrete_search_space (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@AbstractRTAforEDFwithArrivalCurves.A_is_in_concrete_search_space Task p0 p1 Job)).
Definition tgt_A_is_in_concrete_search_space (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_ResponseTimeBound_AbstractRTAforEDFwithArrivalCurves_A_is_in_concrete_search_space Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem AbstractRTAforEDFwithArrivalCurves_A_is_in_concrete_search_space_correspondence (Task Job : eqType) :
  PropSPropRel (src_A_is_in_concrete_search_space Task Job) (tgt_A_is_in_concrete_search_space Task Job).
Proof. unfold src_A_is_in_concrete_search_space, tgt_A_is_in_concrete_search_space. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_correct_search_space (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@AbstractRTAforEDFwithArrivalCurves.correct_search_space Task p0 p1 Job)).
Definition tgt_correct_search_space (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_ResponseTimeBound_AbstractRTAforEDFwithArrivalCurves_correct_search_space Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem AbstractRTAforEDFwithArrivalCurves_correct_search_space_correspondence (Task Job : eqType) :
  PropSPropRel (src_correct_search_space Task Job) (tgt_correct_search_space Task Job).
Proof. unfold src_correct_search_space, tgt_correct_search_space. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_uniprocessor_response_time_bound_edf (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@AbstractRTAforEDFwithArrivalCurves.uniprocessor_response_time_bound_edf Task p0 p1 Job)).
Definition tgt_uniprocessor_response_time_bound_edf (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_Edf_ResponseTimeBound_AbstractRTAforEDFwithArrivalCurves_uniprocessor_response_time_bound_edf Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem AbstractRTAforEDFwithArrivalCurves_uniprocessor_response_time_bound_edf_correspondence (Task Job : eqType) :
  PropSPropRel (src_uniprocessor_response_time_bound_edf Task Job) (tgt_uniprocessor_response_time_bound_edf Task Job).
Proof. unfold src_uniprocessor_response_time_bound_edf, tgt_uniprocessor_response_time_bound_edf. crel_spine. crel. Unshelve. all: crel. Qed.
