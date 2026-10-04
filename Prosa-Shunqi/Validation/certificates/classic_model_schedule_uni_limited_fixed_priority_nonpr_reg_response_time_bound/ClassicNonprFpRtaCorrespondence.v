From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.service classic.model.schedule.uni.workload classic.model.schedule.uni.schedule_of_task classic.model.schedule.uni.limited.busy_interval classic.model.schedule.uni.limited.abstract_RTA.definitions classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta classic.model.schedule.uni.limited.jlfp_instantiation classic.model.schedule.uni.basic.platform classic.model.priority classic.model.schedule.uni.response_time classic.model.schedule.uni.limited.platform.definitions classic.model.schedule.uni.limited.schedule classic.model.schedule.uni.limited.rbf classic.model.schedule.uni.limited.abstract_RTA.reduction_of_search_space classic.model.arrival.curves.bounds classic.analysis.uni.arrival_curves.workload_bound classic.model.schedule.uni.limited.fixed_priority.nonpr_reg.response_time_bound classic.model.schedule.uni.limited.platform.priority_inversion_is_bounded classic.model.schedule.uni.limited.fixed_priority.response_time_bound.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicNonprFpRta.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicNonprFpRtaBase ClassicNonprFpRtaList.



Module I := ImportedClassicNonprFpRta.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/fixed_priority/nonpr_reg/response_time_bound.v] (ProsaBuddy classic, commit f692cb7).

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

Lemma cnf_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cnf_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cnf_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cnf_false_rel). Qed.

Lemma cnf_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cnf_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cnf_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cnf_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cnf_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cnf_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cnf_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cnf_unmap_rel T l) PR PL).
Qed.

Definition CnfParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cnf_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CnfParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cnf_forall_cover _ _ (CnfParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cnf_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cnf_natl s') end.

Definition cnf_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cnf_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cnf_one) (cnf_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cnf_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cnf_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cnf_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cnf_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cnf_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cnf_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cnf_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cnf_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cnf_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cnf_cl_append. reflexivity.
Qed.

Lemma cnf_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CnfFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cnf_bigcat_rel (A : Type) fR fL (Hf : CnfFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicNonprFpRtaInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cnf_iota_range (nR - mR) 0) cnf_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cnf_cl_map_ext _ _ Hpt) (cnf_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cnf_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cnf_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CnfArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cnf_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cnf_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cnf_arr_canonical aR : CnfArrRel aR (cnf_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cnf_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cnf_arr_surjective aL : CnfArrRel (cnf_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cnf_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CnfArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cnf_forall_cover _ _ CnfArrRel cnf_arr_to_target cnf_arr_to_source cnf_arr_canonical cnf_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cnf_jobs_arrived_between aR aL (Ha : CnfArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cnf_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cnf_arrives_in aR aL (Ha : CnfArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cnf_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cnf_consistent pR pL (Hp : CnfParRel Job pR pL) aR aL (Ha : CnfArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cnf_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cnf_is_a_set aR aL (Ha : CnfArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cnf_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cnf_jobs_arrived_before aR aL (Ha : CnfArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job dJ aL tL).
Proof. exact (cnf_jobs_arrived_between Job aR aL Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma cnf_arrives_at aR aL (Ha : CnfArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cnf_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma cnf_has_arrived pR pL (Hp : CnfParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

Lemma cnf_arrived_before pR pL (Hp : CnfParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrived_before pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_before Job dJ pL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cnf_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cnf_snatl s') end.

Lemma cnf_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cnf_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cnf_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cnf_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cnf_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cnf_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cnf_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CnfFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cnf_fun_canonical FR FL (HF : CnfFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cnf_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cnf_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CnfFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cnf_nat_sub_canonical nR mR.
  rewrite cnf_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cnf_foldr_add FL FR (cnf_fun_canonical FR FL HF)).
  by rewrite cnf_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cnf_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cnf_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cnf_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cnf_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cnf_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CnfSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cnf_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cnf_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cnf_sched_canonical sR : CnfSchedRel sR (cnf_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cnf_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cnf_sched_surjective sL : CnfSchedRel (cnf_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cnf_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cnf_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CnfSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cnf_forall_cover _ _ CnfSchedRel cnf_sched_to_target cnf_sched_to_source cnf_sched_canonical cnf_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cnf_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CnfSchedRel Job sR (cnf_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CnfSchedRel Job (cnf_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cnf_sched_canonical Job) (cnf_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnfSchedRel Job sR sL.

Lemma cnf_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cnf_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cnf_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cnf_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cnf_US_scheduled_at j tR tL Ht)). Qed.

Lemma cnf_service_at_fun j : CnfFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cnf_US_service_at j kR kL Hk). Qed.

Lemma cnf_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cnf_ico _ _ _ _ _ _ H1 H2 (cnf_service_at_fun j)). Qed.

Lemma cnf_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cnf_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cnf_US_completed_by cR cL (Hc : CnfParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cnf_US_service j tR tL Ht)). Qed.

Lemma cnf_US_pending aR aL (Ha : CnfParRel Job aR aL) cR cL (Hc : CnfParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cnf_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cnf_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cnf_US_backlogged aR aL (Ha : CnfParRel Job aR aL) cR cL (Hc : CnfParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.backlogged aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_backlogged Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cnf_US_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (cnf_US_scheduled_at j tR tL Ht))).
Qed.

Lemma cnf_US_sequential_jobs (Task : eqType) aR aL (Ha : CnfParRel Job aR aL) cR cL (Hc : CnfParRel Job cR cL)
    (job_task : Job -> Task) :
  PropSPropRel (UniprocessorSchedule.sequential_jobs aR cR sR job_task)
    (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_sequential_jobs Job dJ aL cL sL Task (ct_decidable_eq Task) job_task).
Proof.
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_eq Task (job_task j1) (job_task j2))).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha j1) (Ha j2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnf_US_scheduled_at j2 tR tL Ht)).
  exact (ct_bool_truth _ _ (cnf_US_completed_by cR cL Hc j1 tR tL Ht)).
Qed.

Lemma cnf_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CnfArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnf_US_scheduled_at j tR tL Ht)).
  exact (cnf_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cnf_US_jobs_must_arrive_to_execute aR aL (Ha : CnfParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnf_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cnf_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma cnf_US_completed_jobs_dont_execute cR cL (Hc : CnfParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cnf_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cnf_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicNonprFpRtaInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicNonprFpRtaInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cnf_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cnf_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cnf_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicNonprFpRtaInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicNonprFpRtaInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicNonprFpRtaInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cnf_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cnf_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CnfPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma cnf_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CnfPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cnf_forall_cover _ _ (CnfPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CnfRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cnf_rel_canonical (T : Type) (rR : T -> T -> bool) : CnfRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cnf_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CnfRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cnf_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CnfRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cnf_forall_cover _ _ (CnfRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cnf_rel_canonical T) (cnf_rel_surjective T) PR PL).
Qed.

Definition CnfJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CnfRelRel T (rR tR) (rL tL).

Lemma cnf_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CnfJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cnf_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CnfJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cnf_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CnfJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cnf_forall_cover _ _ (CnfJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cnf_jldp_canonical T) (cnf_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cnf_PR_FP_policy :
  And (forall rR : Priority.FP_policy Task, CnfRelRel Task rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_FP_policy Task dT, CnfRelRel Task (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cnf_rel_canonical Task) (cnf_rel_surjective Task)). Qed.

Lemma cnf_PR_JLFP_policy :
  And (forall rR : Priority.JLFP_policy Job, CnfRelRel Job rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLFP_policy Job dJ, CnfRelRel Job (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cnf_rel_canonical Job) (cnf_rel_surjective Job)). Qed.

Lemma cnf_PR_FP_to_JLFP (job_task : Job -> Task) rR rL (Hr : CnfRelRel Task rR rL) :
  CnfRelRel Job (Priority.FP_to_JLFP job_task rR)
    (I.Prosa_Classic_Model_Priority_Priority_FP_to_JLFP Task Job dT dJ job_task rL).
Proof. intros a b. exact (Hr (job_task a) (job_task b)). Qed.

Lemma cnf_reflexive (T : Type) rR rL (Hr : CnfRelRel T rR rL) :
  PropSPropRel (reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_reflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (Hr x x)). Qed.

Lemma cnf_transitive (T : Type) rR rL (Hr : CnfRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma cnf_PR_FP_is_reflexive rR rL (Hr : CnfRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_reflexive Task dT rL).
Proof. exact (cnf_reflexive Task rR rL Hr). Qed.

Lemma cnf_PR_FP_is_transitive rR rL (Hr : CnfRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_transitive Task dT rL).
Proof. exact (cnf_transitive Task rR rL Hr). Qed.

End PriodefsDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cnf_J_job_cost_positive cR cL (Hc : CnfParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

Lemma cnf_J_job_cost_le_task_cost tcR tcL (Htc : CnfParRel Task tcR tcL) cR cL (Hc : CnfParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

Lemma cnf_J_cost_of_jobs_from_arrival_sequence_le_task_cost tcR tcL (Htc : CnfParRel Task tcR tcL)
    cR cL (Hc : CnfParRel Job cR cL) (job_task : Job -> Task) aR aL (Ha : CnfArrRel Job aR aL) :
  PropSPropRel (Job.cost_of_jobs_from_arrival_sequence_le_task_cost tcR cR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_cost_of_jobs_from_arrival_sequence_le_task_cost Task dT tcL Job dJ cL job_task aL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp.
  - apply: ct_exists_nat => tR tL Ht. exact (cnf_mem Job j _ _ (Ha tR tL Ht)).
  - exact (ct_bool_truth _ _ (cnf_J_job_cost_le_task_cost tcR tcL Htc cR cL Hc job_task j)).
Qed.

End JobDefs.

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cnf_TA_is_job_of_task (job_task : Job -> Task) tsk j :
  CtBoolRel (TaskArrival.is_job_of_task job_task tsk j)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk j).
Proof. exact (ct_decide_eq Task (job_task j) tsk). Qed.

Lemma cnf_TA_arrivals_of_task_between (job_task : Job -> Task) aR aL (Ha : CnfArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_between Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans (cl_filter cid _ (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk)
                            (cnf_TA_is_job_of_task job_task tsk) _) _).
  exact (f_equal (I.List_filter Job (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk))
           (Logic.eq_sym (cl_list_logic _ _ _ (cnf_jobs_arrived_between Job aR aL Ha _ _ _ _ H1 H2)))).
Qed.

Lemma cnf_TA_num_arrivals_of_task (job_task : Job -> Task) aR aL (Ha : CnfArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  SubNatRel (TaskArrival.num_arrivals_of_task job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_num_arrivals_of_task Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  have H := cnf_TA_arrivals_of_task_between job_task aR aL Ha tsk _ _ _ _ H1 H2.
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
Definition CnfCurveRel (fR : Task -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk nR nL, SubNatRel nR nL -> SubNatRel (fR tsk nR) (fL tsk nL).

Notation NA := (cnf_TA_num_arrivals_of_task Task Job).

Lemma cnf_AC_is_arrival_bound (job_task : Job -> Task) aR aL (Ha : CnfArrRel Job aR aL)
    mR mL (Hm : CnfCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.is_arrival_bound job_task aR mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_is_arrival_bound Task dT Job dJ job_task aL mL tsk).
Proof.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 H2).
  exact (sub_nat_le_correspondence _ _ _ _ (NA job_task aR aL Ha tsk _ _ _ _ H1 H2) (Hm tsk _ _ (ct_sub_rel _ _ _ _ H2 H1))).
Qed.

Lemma cnf_AC_zero_arrival_curve mR mL (Hm : CnfCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.zero_arrival_curve mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_zero_arrival_curve Task dT mL tsk).
Proof. exact (sub_nat_eq_correspondence _ _ _ _ (Hm tsk _ _ (sub_nat_rel_canonical 0)) (sub_nat_rel_canonical 0)). Qed.

Lemma cnf_AC_monotonic_arrival_curve mR mL (Hm : CnfCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.monotonic_arrival_curve mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_monotonic_arrival_curve Task dT mL tsk).
Proof.
  apply: ct_forall_nat => xR xL Hx. apply: ct_forall_nat => yR yL Hy.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ Hx Hy)).
  exact (ct_bool_truth _ _ (ct_decide_le _ _ _ _ (Hm tsk _ _ Hx) (Hm tsk _ _ Hy))).
Qed.

Lemma cnf_AC_proper_arrival_curve (job_task : Job -> Task) aR aL (Ha : CnfArrRel Job aR aL)
    mR mL (Hm : CnfCurveRel mR mL) tsk :
  PropSPropRel (ArrivalCurves.proper_arrival_curve job_task aR mR tsk) (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_proper_arrival_curve Task dT Job dJ job_task aL mL tsk).
Proof.
  apply: ct_and; first exact (cnf_AC_is_arrival_bound job_task aR aL Ha mR mL Hm tsk).
  apply: ct_and; first exact (cnf_AC_zero_arrival_curve mR mL Hm tsk).
  exact (cnf_AC_monotonic_arrival_curve mR mL Hm tsk).
Qed.

Lemma cnf_AC_family_of_proper_arrival_curves (job_task : Job -> Task) aR aL (Ha : CnfArrRel Job aR aL)
    mR mL (Hm : CnfCurveRel mR mL) tsR tsL (Hts : ClListRel cid tsR tsL) :
  PropSPropRel (ArrivalCurves.family_of_proper_arrival_curves job_task aR mR tsR)
    (I.Prosa_Classic_Model_Arrival_Curves_Bounds_ArrivalCurves_family_of_proper_arrival_curves Task dT Job dJ job_task aL mL tsL).
Proof.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (cnf_mem Task tsk _ _ Hts).
  exact (cnf_AC_proper_arrival_curve job_task aR aL Ha mR mL Hm tsk).
Qed.

End AcboundsDefs.

(** * Arrival curves [Task -> time -> nat], with two-way totals *)

Lemma cnf_curve_canonical (Task : eqType) mR : CnfCurveRel Task mR (fun tsk nL => sub_nat_to_imported (mR tsk (sub_nat_to_rocq nL))).
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma cnf_curve_surjective (Task : eqType) mL : CnfCurveRel Task (fun tsk nR => sub_nat_to_rocq (mL tsk (sub_nat_to_imported nR))) mL.
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. exact (sub_nat_rel_surjective _). Qed.

Lemma cnf_forall_curve (Task : eqType) (PR : (Task -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall mR mL, CnfCurveRel Task mR mL -> PropSPropRel (PR mR) (PL mL)) -> PropSPropRel (forall m, PR m) (forall m, PL m).
Proof. exact (cnf_forall_cover _ _ (CnfCurveRel Task) _ _ (cnf_curve_canonical Task) (cnf_curve_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section AcwbDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat).
Hypothesis Htc : CnfParRel Task tcR tcL.
Variables (mR : Task -> nat -> nat) (mL : Task -> Lean.Nat -> Lean.Nat).
Hypothesis Hm : CnfCurveRel Task mR mL.

Lemma cnf_WB_task_request_bound_function tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.task_request_bound_function tcR mR tsk dR) (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_task_request_bound_function Task dT tcL mL tsk dL).
Proof. exact (sub_mul_correspondence _ _ _ _ (Htc tsk) (Hm tsk _ _ Hd)). Qed.

Notation TRBF := cnf_WB_task_request_bound_function.

Lemma cnf_WB_total_hep_request_bound_function_FP hR hL (Hh : CnfRelRel Task hR hL)
    tsR tsL (Hts : ClListRel cid tsR tsL) tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.total_hep_request_bound_function_FP tcR hR mR tsR tsk dR)
    (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_total_hep_request_bound_function_FP Task dT tcL hL mL tsL tsk dL).
Proof. exact (cnf_sum_filtered_rel Task _ _ (fun x => TRBF x dR dL Hd) _ _ (fun x => Hh x tsk) _ _ Hts). Qed.

Lemma cnf_WB_total_ohep_request_bound_function_FP hR hL (Hh : CnfRelRel Task hR hL)
    tsR tsL (Hts : ClListRel cid tsR tsL) tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (MaxArrivalsWorkloadBound.total_ohep_request_bound_function_FP tcR hR mR tsR tsk dR)
    (I.Prosa_Classic_Analysis_Uni_ArrivalCurves_WorkloadBound_MaxArrivalsWorkloadBound_total_ohep_request_bound_function_FP Task dT tcL hL mL tsL tsk dL).
Proof.
  exact (cnf_sum_filtered_rel Task _ _ (fun x => TRBF x dR dL Hd) _ _
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
Hypothesis Hs : CnfSchedRel Job sR sL.

Lemma cnf_RT_is_response_time_bound_of_job aR aL (Ha : CnfParRel Job aR aL) cR cL (Hc : CnfParRel Job cR cL)
    j rR rL (Hr : SubNatRel rR rL) :
  CtBoolRel (ResponseTime.is_response_time_bound_of_job aR cR sR j rR) (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_job Job dJ aL cL sL j rL).
Proof. exact (cnf_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr)). Qed.

Lemma cnf_RT_is_response_time_bound_of_task aR aL (Ha : CnfParRel Job aR aL) cR cL (Hc : CnfParRel Job cR cL)
    (job_task : Job -> Task) arrR arrL (Harr : CnfArrRel Job arrR arrL) tsk rR rL (Hr : SubNatRel rR rL) :
  PropSPropRel (ResponseTime.is_response_time_bound_of_task aR cR job_task arrR sR tsk rR)
    (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_task Task dT Job dJ aL cL job_task arrL sL tsk rL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cnf_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (cnf_RT_is_response_time_bound_of_job aR aL Ha cR cL Hc j rR rL Hr)).
Qed.

End UrtDefs.

Section UplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnfSchedRel Job sR sL.

Lemma cnf_UP_work_conserving aR aL (Ha : CnfParRel Job aR aL) cR cL (Hc : CnfParRel Job cR cL)
    arrR arrL (Harr : CnfArrRel Job arrR arrL) :
  PropSPropRel (Platform.work_conserving aR cR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Basic_Platform_Platform_work_conserving Job dJ aL cL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cnf_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnf_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (cnf_US_scheduled_at Job sR sL Hs j_other tR tL Ht)).
Qed.

End UplatDefs.

Lemma cnf_iff (P Q : Prop) (PL QL : SProp) :
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
Definition CnfPmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma cnf_pm_canonical pR : CnfPmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cnf_pm_surjective pL : CnfPmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cnf_forall_pm (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CnfPmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (cnf_forall_cover _ _ CnfPmRel _ _ cnf_pm_canonical cnf_pm_surjective PR PL). Qed.

End LpdefsPmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LpdefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnfSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CnfPmRel Job pR pL.

Notation SA := (cnf_US_scheduled_at Job sR sL Hs).
Notation SV := (cnf_US_service Job sR sL Hs).

Lemma cnf_LP_preemption_time tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_preemption_time Job dJ sL pL tL).
Proof.
  refine (cnf_trs (Hs tR tL Ht)
            (fun z => CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR)
                        (match z with
                         | I.Option_some j => pL j (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL)
                         | I.Option_none => I.Bool_true end)) _).
  rewrite /LimitedPreemptionPlatform.preemption_time. destruct (sR tR) as [x|].
  - exact (Hp x _ _ (SV x tR tL Ht)).
  - exact (ct_bool_canonical true).
Qed.

Lemma cnf_LP_not_preemptive_implies_scheduled j :
  PropSPropRel (LimitedPreemptionPlatform.not_preemptive_implies_scheduled sR pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_not_preemptive_implies_scheduled Job dJ sL pL j).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (Hp j _ _ (SV j tR tL Ht)))).
  exact (ct_bool_truth _ _ (SA j tR tL Ht)).
Qed.

Lemma cnf_LP_execution_starts_with_preemption_point j :
  PropSPropRel (LimitedPreemptionPlatform.execution_starts_with_preemption_point sR pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_execution_starts_with_preemption_point Job dJ sL pL j).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  have Ht1 := cnf_succ_rel _ _ Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (SA j tR tL Ht))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j _ _ Ht1)).
  exact (ct_bool_truth _ _ (Hp j _ _ (SV j _ _ Ht1))).
Qed.

Lemma cnf_LP_correct_preemption_model arrR arrL (Harr : CnfArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.correct_preemption_model arrR sR pR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_correct_preemption_model Job dJ arrL sL pL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cnf_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (cnf_LP_not_preemptive_implies_scheduled j).
  exact (cnf_LP_execution_starts_with_preemption_point j).
Qed.

End LpdefsDefs.

Section LpdefsDefs2.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CnfPmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : CnfParRel Job cR cL) (Hm : CnfParRel Job mR mL) (Htm : CnfParRel Task tmR tmL).

Lemma cnf_LP_job_cannot_become_nonpreemptive_before_execution j :
  PropSPropRel (LimitedPreemptionPlatform.job_cannot_become_nonpreemptive_before_execution pR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_cannot_become_nonpreemptive_before_execution Job dJ pL j).
Proof. exact (ct_bool_truth _ _ (Hp j _ _ (sub_nat_rel_canonical 0))). Qed.

Lemma cnf_LP_job_cannot_be_nonpreemptive_after_completion j :
  PropSPropRel (LimitedPreemptionPlatform.job_cannot_be_nonpreemptive_after_completion cR pR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_cannot_be_nonpreemptive_after_completion Job dJ cL pL j).
Proof. exact (ct_bool_truth _ _ (Hp j _ _ (Hc j))). Qed.

Lemma cnf_LP_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment (job_task : Job -> Task)
    arrR arrL (Harr : CnfArrRel Job arrR arrL) j :
  PropSPropRel (LimitedPreemptionPlatform.job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arrR mR tmR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment Task dT Job dJ job_task arrL mL tmL j).
Proof.
  apply: ct_imp; first exact (cnf_arrives_in Job arrR arrL Harr j).
  exact (sub_nat_le_correspondence _ _ _ _ (Hm j) (Htm (job_task j))).
Qed.

Lemma cnf_LP_nonpreemptive_regions_have_bounded_length j :
  PropSPropRel (LimitedPreemptionPlatform.nonpreemptive_regions_have_bounded_length cR pR mR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_nonpreemptive_regions_have_bounded_length Job dJ cL pL mL j).
Proof.
  apply: ct_forall_nat => gR gL Hg.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ (sub_nat_rel_canonical 0) Hg) (ct_decide_le _ _ _ _ Hg (Hc j)))).
  apply: ct_exists_nat => xR xL Hx.
  apply: ct_and.
  - exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Hg Hx)
             (ct_decide_le _ _ _ _ Hx (sub_add_correspondence _ _ _ _ Hg (ct_sub_rel _ _ _ _ (Hm j) (sub_nat_rel_canonical 1)))))).
  - exact (ct_bool_truth _ _ (Hp j _ _ Hx)).
Qed.

Lemma cnf_LP_model_with_bounded_nonpreemptive_segments (job_task : Job -> Task)
    arrR arrL (Harr : CnfArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.model_with_bounded_nonpreemptive_segments cR job_task arrR pR mR tmR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_model_with_bounded_nonpreemptive_segments Task dT Job dJ cL job_task arrL pL mL tmL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cnf_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (cnf_LP_job_cannot_become_nonpreemptive_before_execution j).
  apply: ct_and; first exact (cnf_LP_job_cannot_be_nonpreemptive_after_completion j).
  apply: ct_and; first exact (cnf_LP_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arrR arrL Harr j).
  exact (cnf_LP_nonpreemptive_regions_have_bounded_length j).
Qed.

End LpdefsDefs2.

(* ------------------------------------------------------------------ *)
(** * Relations *)

Lemma cnf_eq_transport (T : Type) (a b : T) aL bL : Lean.eq a aL -> Lean.eq b bL ->
  PropSPropRel (Logic.eq a b) (Lean.eq aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (ct_eq_rel T a b). Qed.

(** Functions [nat -> T] (identical values) and [nat -> nat] (values by [SubNatRel]), pointwise on related arguments. *)
Definition CnfRsFunRel (T : Type) (fR : nat -> T) (fL : Lean.Nat -> T) : SProp :=
  forall nR nL, SubNatRel nR nL -> Lean.eq (fR nR) (fL nL).
Definition CnfNatFunRel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) : SProp :=
  forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

(** Interference bound functions [Task -> time -> time -> time], pointwise on related arguments and values. *)
Definition CnfIbfRel (Task : Type) (fR : Task -> nat -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk, forall aR aL, SubNatRel aR aL -> CnfNatFunRel (fR tsk aR) (fL tsk aL).

Definition cnf_ibf_to_target (Task : Type) (fR : Task -> nat -> nat -> nat) : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat :=
  fun tsk aL xL => sub_nat_to_imported (fR tsk (sub_nat_to_rocq aL) (sub_nat_to_rocq xL)).
Definition cnf_ibf_to_source (Task : Type) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : Task -> nat -> nat -> nat :=
  fun tsk aR xR => sub_nat_to_rocq (fL tsk (sub_nat_to_imported aR) (sub_nat_to_imported xR)).

Lemma cnf_ibf_canonical (Task : Type) fR : CnfIbfRel Task fR (cnf_ibf_to_target Task fR).
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  unfold cnf_ibf_to_target. rewrite !sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma cnf_ibf_surjective (Task : Type) fL : CnfIbfRel Task (cnf_ibf_to_source Task fL) fL.
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma cnf_forall_ibf (Task : Type) (PR : (Task -> nat -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, CnfIbfRel Task fR fL -> PropSPropRel (PR fR) (PL fL)) -> PropSPropRel (forall f, PR f) (forall f, PL f).
Proof. exact (cnf_forall_cover _ _ (CnfIbfRel Task) (cnf_ibf_to_target Task) (cnf_ibf_to_source Task) (cnf_ibf_canonical Task) (cnf_ibf_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(* ------------------------------------------------------------------ *)
(** * Interference predicates and interfering workloads *)

Section JISEQARDIRel.
Variable Job : eqType.

Definition CnfIntRel (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (iR j tR) (iL j tL).

Lemma cnf_int_canonical iR : CnfIntRel iR (fun j tL => ct_b2l (iR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cnf_int_surjective iL : CnfIntRel (fun j tR => ct_l2b (iL j (sub_nat_to_imported tR))) iL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cnf_forall_int (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall iR iL, CnfIntRel iR iL -> PropSPropRel (PR iR) (PL iL)) -> PropSPropRel (forall i, PR i) (forall i, PL i).
Proof. exact (cnf_forall_cover _ _ CnfIntRel _ _ cnf_int_canonical cnf_int_surjective PR PL). Qed.

Definition CnfWlRel (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (wR j tR) (wL j tL).

Lemma cnf_wl_canonical wR : CnfWlRel wR (fun j tL => sub_nat_to_imported (wR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma cnf_wl_surjective wL : CnfWlRel (fun j tR => sub_nat_to_rocq (wL j (sub_nat_to_imported tR))) wL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (sub_nat_rel_surjective _). Qed.

Lemma cnf_forall_wl (PR : (Job -> nat -> nat) -> Prop) (PL : (Job -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall wR wL, CnfWlRel wR wL -> PropSPropRel (PR wR) (PL wL)) -> PropSPropRel (forall w, PR w) (forall w, PL w).
Proof. exact (cnf_forall_cover _ _ CnfWlRel _ _ cnf_wl_canonical cnf_wl_surjective PR PL). Qed.

End JISEQARDIRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JISEQARDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Section JISEQARDSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnfSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CnfParRel Job aR aL) (Hc : CnfParRel Job cR cL).
Variables (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat).
Hypotheses (Hi : CnfIntRel Job iR iL) (Hw : CnfWlRel Job wR wL).

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
Hypothesis Hc : CnfParRel Job cR cL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CnfArrRel Job arrR arrL.
Variables (lR : Job -> nat) (lL : Job -> Lean.Nat).
Hypothesis Hl : CnfParRel Job lR lL.

Lemma cnf_LS_job_lock_in_service_positive :
  PropSPropRel (LS.job_lock_in_service_positive cR arrR lR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_lock_in_service_positive Job dJ cL arrL lL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cnf_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnf_J_job_cost_positive Job cR cL Hc j)).
  exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hl j)).
Qed.

Lemma cnf_LS_job_lock_in_service_le_job_cost :
  PropSPropRel (LS.job_lock_in_service_le_job_cost cR arrR lR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_lock_in_service_le_job_cost Job dJ cL arrL lL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cnf_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnf_J_job_cost_positive Job cR cL Hc j)).
  exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (Hc j)).
Qed.

Section JISEQLSSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnfSchedRel Job sR sL.

Lemma cnf_LS_job_nonpreemptive_after_lock_in_service :
  PropSPropRel (LS.job_nonpreemptive_after_lock_in_service cR arrR sR lR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_job_nonpreemptive_after_lock_in_service Job dJ cL arrL sL lL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (cnf_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht Ht').
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (cnf_US_service Job sR sL Hs j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (cnf_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht'))).
  exact (ct_bool_truth _ _ (cnf_US_scheduled_at Job sR sL Hs j _ _ Ht')).
Qed.

Lemma cnf_LS_proper_job_lock_in_service :
  PropSPropRel (LS.proper_job_lock_in_service cR arrR sR lR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_proper_job_lock_in_service Job dJ cL arrL sL lL).
Proof.
  apply: ct_and; first exact cnf_LS_job_lock_in_service_positive.
  apply: ct_and; first exact cnf_LS_job_lock_in_service_le_job_cost.
  exact cnf_LS_job_nonpreemptive_after_lock_in_service.
Qed.

End JISEQLSSched.

Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat) (tlR : Task -> nat) (tlL : Task -> Lean.Nat).
Hypotheses (Htc : CnfParRel Task tcR tcL) (Htl : CnfParRel Task tlR tlL).

Lemma cnf_LS_task_lock_in_service_le_task_cost tsk :
  PropSPropRel (LS.task_lock_in_service_le_task_cost tcR tlR tsk) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_task_lock_in_service_le_task_cost Task dT tcL tlL tsk).
Proof. exact (sub_nat_le_correspondence _ _ _ _ (Htl tsk) (Htc tsk)). Qed.

Lemma cnf_LS_task_lock_in_service_bounds_job_lock_in_service (job_task : Job -> Task) tsk :
  PropSPropRel (LS.task_lock_in_service_bounds_job_lock_in_service job_task arrR lR tlR tsk)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_task_lock_in_service_bounds_job_lock_in_service Task dT Job dJ job_task arrL lL tlL tsk).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cnf_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (sub_nat_le_correspondence _ _ _ _ (Hl j) (Htl tsk)).
Qed.

Lemma cnf_LS_proper_task_lock_in_service (job_task : Job -> Task) tsk :
  PropSPropRel (LS.proper_task_lock_in_service tcR job_task arrR lR tlR tsk)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Schedule_proper_task_lock_in_service Task dT tcL Job dJ job_task arrL lL tlL tsk).
Proof.
  apply: ct_and; first exact (cnf_LS_task_lock_in_service_le_task_cost tsk).
  exact (cnf_LS_task_lock_in_service_bounds_job_lock_in_service job_task tsk).
Qed.

End JISEQLSDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JISEQSVDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnfSchedRel Job sR sL.

End JISEQSVDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JISEQSTDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnfSchedRel Job sR sL.
Variable job_task : Job -> Task.

End JISEQSTDefs.

(* ------------------------------------------------------------------ *)
(** * [has] against [List.any] *)

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(* ------------------------------------------------------------------ *)
(** * Service of jobs (as in the accepted classic uniprocessor service certificate) *)

Section JILBISvc.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnfSchedRel Job sR sL.

End JILBISvc.

(* ------------------------------------------------------------------ *)
(** * Auxiliary relations *)

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JILBIDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CnfParRel Job jaR jaL) (Hc : CnfParRel Job cR cL).
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CnfArrRel Job aR aL.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnfSchedRel Job sR sL.
Variables (hR : Job -> Job -> bool) (hL : Job -> Job -> I.Bool).
Hypothesis Hh : CnfRelRel Job hR hL.

Lemma cnf_LBI_quiet_time j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (@BusyIntervalJLFP.quiet_time Job jaR cR aR sR hR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_quiet_time Job dJ jaL cL aL sL hL j tL).
Proof.
  apply: ct_forall_identity => j_hp.
  apply: ct_imp; first exact (cnf_arrives_in Job aR aL Ha j_hp).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hh j_hp j)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnf_arrived_before Job jaR jaL Hja j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (cnf_US_completed_by Job sR sL Hs cR cL Hc j_hp tR tL Ht)).
Qed.

Notation QT := cnf_LBI_quiet_time.

Lemma cnf_not_quiet j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (~ @BusyIntervalJLFP.quiet_time Job jaR cR aR sR hR j tR) (I.Not (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_quiet_time Job dJ jaL cL aL sL hL j tL)).
Proof. exact (ct_imp _ _ _ _ (QT j tR tL Ht) cnf_false_rel). Qed.

Lemma cnf_LBI_busy_interval_prefix j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (@BusyIntervalJLFP.busy_interval_prefix Job jaR cR aR sR hR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_busy_interval_prefix Job dJ jaL cL aL sL hL j t1L t2L).
Proof.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ H1 H2).
  apply: ct_and; first exact (QT j t1R t1L H1).
  apply: ct_and.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
    exact (cnf_not_quiet j tR tL Ht). }
  exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Hja j)) (ct_decide_lt _ _ _ _ (Hja j) H2))).
Qed.

Lemma cnf_LBI_is_priority_inversion j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@BusyIntervalJLFP.is_priority_inversion Job sR hR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_is_priority_inversion Job dJ sL hL j tL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite /BusyIntervalJLFP.is_priority_inversion. unfold I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_is_priority_inversion.
  rewrite -(imported_eq_to_coq_eq _ _ (Hs tR tL Ht)).
  case: (sR tR) => [jlp|]; last reflexivity.
  cbn. rewrite (ct_bool_rel_logic _ _ (Hh jlp j)). by case: (hR jlp j).
Qed.

Lemma cnf_LBI_cumulative_priority_inversion j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (@BusyIntervalJLFP.cumulative_priority_inversion Job sR hR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_cumulative_priority_inversion Job dJ sL hL j t1L t2L).
Proof.
  exact (cnf_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (cnf_LBI_is_priority_inversion j kR kL Hk))).
Qed.

Lemma cnf_LBI_priority_inversion_of_job_is_bounded_by j BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (@BusyIntervalJLFP.priority_inversion_of_job_is_bounded_by Job jaR cR aR sR hR j BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_priority_inversion_of_job_is_bounded_by Job dJ jaL cL aL sL hL j BL).
Proof.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (cnf_LBI_busy_interval_prefix j t1R t1L H1 t2R t2L H2).
  exact (sub_nat_le_correspondence _ _ _ _ (cnf_LBI_cumulative_priority_inversion j t1R t1L H1 t2R t2L H2) HB).
Qed.

Lemma cnf_LBI_priority_inversion_is_bounded_by (Task : eqType) (job_task : Job -> Task) tsk BR BL (HB : SubNatRel BR BL) :
  PropSPropRel (@BusyIntervalJLFP.priority_inversion_is_bounded_by Task Job jaR cR job_task aR sR hR tsk BR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_priority_inversion_is_bounded_by Task (ct_decidable_eq Task) Job dJ jaL cL job_task aL sL hL tsk BL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cnf_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  exact (cnf_LBI_priority_inversion_of_job_is_bounded_by j BR BL HB).
Qed.

Lemma cnf_LP_work_conserving :
  PropSPropRel (LimitedPreemptionPlatform.work_conserving jaR cR aR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_work_conserving Job dJ jaL cL aL sL).
Proof. exact (cnf_UP_work_conserving Job sR sL Hs jaR jaL Hja cR cL Hc aR aL Ha). Qed.

End JILBIDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cnf_arriving_at (Job : eqType) aR aL (Ha : CnfArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arriving_at aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arriving_at Job (ct_decidable_eq Job) aL tL).
Proof. exact (Ha tR tL Ht). Qed.

Section JIDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnfSchedRel Job sR sL.
Variables (hR : Job -> Job -> bool) (hL : Job -> Job -> I.Bool).
Hypothesis Hh : CnfRelRel Job hR hL.
Variable job_task : Job -> Task.

Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CnfParRel Job cR cL.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CnfArrRel Job aR aL.

End JIDefs.

(* ------------------------------------------------------------------ *)
(** * Preemption models *)

Section LPDPmRel.
Variable Job : eqType.
Definition CnfPmRel__LPDPmRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).

Lemma cnf_pm_canonical__LPDPmRel pR : CnfPmRel__LPDPmRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cnf_pm_surjective__LPDPmRel pL : CnfPmRel__LPDPmRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cnf_forall_pm__LPDPmRel (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CnfPmRel__LPDPmRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (cnf_forall_cover _ _ CnfPmRel__LPDPmRel _ _ cnf_pm_canonical__LPDPmRel cnf_pm_surjective__LPDPmRel PR PL). Qed.

End LPDPmRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LPDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnfSchedRel Job sR sL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CnfPmRel Job pR pL.

Notation SA := (cnf_US_scheduled_at Job sR sL Hs).
Notation SV := (cnf_US_service Job sR sL Hs).

Lemma cnf_LPD_preemption_time tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_preemption_time Job dJ sL pL tL).
Proof.
  refine (cnf_trs (Hs tR tL Ht)
            (fun z => CtBoolRel (LimitedPreemptionPlatform.preemption_time sR pR tR)
                        (match z with
                         | I.Option_some j => pL j (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL)
                         | I.Option_none => I.Bool_true end)) _).
  rewrite /LimitedPreemptionPlatform.preemption_time. destruct (sR tR) as [x|].
  - exact (Hp x _ _ (SV x tR tL Ht)).
  - exact (ct_bool_canonical true).
Qed.

Lemma cnf_LPD_not_preemptive_implies_scheduled j :
  PropSPropRel (LimitedPreemptionPlatform.not_preemptive_implies_scheduled sR pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_not_preemptive_implies_scheduled Job dJ sL pL j).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (Hp j _ _ (SV j tR tL Ht)))).
  exact (ct_bool_truth _ _ (SA j tR tL Ht)).
Qed.

Lemma cnf_LPD_execution_starts_with_preemption_point j :
  PropSPropRel (LimitedPreemptionPlatform.execution_starts_with_preemption_point sR pR j) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_execution_starts_with_preemption_point Job dJ sL pL j).
Proof.
  apply: ct_forall_nat => tR tL Ht.
  have Ht1 := cnf_succ_rel _ _ Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (SA j tR tL Ht))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j _ _ Ht1)).
  exact (ct_bool_truth _ _ (Hp j _ _ (SV j _ _ Ht1))).
Qed.

Lemma cnf_LPD_correct_preemption_model arrR arrL (Harr : CnfArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.correct_preemption_model arrR sR pR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_correct_preemption_model Job dJ arrL sL pL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cnf_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (cnf_LPD_not_preemptive_implies_scheduled j).
  exact (cnf_LPD_execution_starts_with_preemption_point j).
Qed.

End LPDDefs.

Section LPDDefs2.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CnfPmRel Job pR pL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat) (mR : Job -> nat) (mL : Job -> Lean.Nat) (tmR : Task -> nat) (tmL : Task -> Lean.Nat).
Hypotheses (Hc : CnfParRel Job cR cL) (Hm : CnfParRel Job mR mL) (Htm : CnfParRel Task tmR tmL).

Lemma cnf_LPD_job_cannot_become_nonpreemptive_before_execution j :
  PropSPropRel (LimitedPreemptionPlatform.job_cannot_become_nonpreemptive_before_execution pR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_cannot_become_nonpreemptive_before_execution Job dJ pL j).
Proof. exact (ct_bool_truth _ _ (Hp j _ _ (sub_nat_rel_canonical 0))). Qed.

Lemma cnf_LPD_job_cannot_be_nonpreemptive_after_completion j :
  PropSPropRel (LimitedPreemptionPlatform.job_cannot_be_nonpreemptive_after_completion cR pR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_cannot_be_nonpreemptive_after_completion Job dJ cL pL j).
Proof. exact (ct_bool_truth _ _ (Hp j _ _ (Hc j))). Qed.

Lemma cnf_LPD_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment (job_task : Job -> Task)
    arrR arrL (Harr : CnfArrRel Job arrR arrL) j :
  PropSPropRel (LimitedPreemptionPlatform.job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arrR mR tmR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment Task dT Job dJ job_task arrL mL tmL j).
Proof.
  apply: ct_imp; first exact (cnf_arrives_in Job arrR arrL Harr j).
  exact (sub_nat_le_correspondence _ _ _ _ (Hm j) (Htm (job_task j))).
Qed.

Lemma cnf_LPD_nonpreemptive_regions_have_bounded_length j :
  PropSPropRel (LimitedPreemptionPlatform.nonpreemptive_regions_have_bounded_length cR pR mR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_nonpreemptive_regions_have_bounded_length Job dJ cL pL mL j).
Proof.
  apply: ct_forall_nat => gR gL Hg.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ (sub_nat_rel_canonical 0) Hg) (ct_decide_le _ _ _ _ Hg (Hc j)))).
  apply: ct_exists_nat => xR xL Hx.
  apply: ct_and.
  - exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ Hg Hx)
             (ct_decide_le _ _ _ _ Hx (sub_add_correspondence _ _ _ _ Hg (ct_sub_rel _ _ _ _ (Hm j) (sub_nat_rel_canonical 1)))))).
  - exact (ct_bool_truth _ _ (Hp j _ _ Hx)).
Qed.

Lemma cnf_LPD_model_with_bounded_nonpreemptive_segments (job_task : Job -> Task)
    arrR arrL (Harr : CnfArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.model_with_bounded_nonpreemptive_segments cR job_task arrR pR mR tmR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_model_with_bounded_nonpreemptive_segments Task dT Job dJ cL job_task arrL pL mL tmL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cnf_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (cnf_LPD_job_cannot_become_nonpreemptive_before_execution j).
  apply: ct_and; first exact (cnf_LPD_job_cannot_be_nonpreemptive_after_completion j).
  apply: ct_and; first exact (cnf_LPD_job_max_nonpreemptive_segment_le_task_max_nonpreemptive_segment job_task arrR arrL Harr j).
  exact (cnf_LPD_nonpreemptive_regions_have_bounded_length j).
Qed.

End LPDDefs2.

Lemma cnf_LPD_work_conserving (Job : eqType) sR sL (Hs : CnfSchedRel Job sR sL) cR cL (Hc : CnfParRel Job cR cL)
    c0R c0L (Hc0 : CnfParRel Job c0R c0L) arrR arrL (Harr : CnfArrRel Job arrR arrL) :
  PropSPropRel (LimitedPreemptionPlatform.work_conserving cR c0R arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_work_conserving Job (ct_decidable_eq Job) cL c0L arrL sL).
Proof. exact (cnf_UP_work_conserving Job sR sL Hs cR cL Hc c0R c0L Hc0 arrR arrL Harr). Qed.

Section LPDResp.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CnfSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CnfParRel Job aR aL) (Hc : CnfParRel Job cR cL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CnfArrRel Job arrR arrL.
Variables (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool).
Hypothesis Hp : CnfPmRel Job pR pL.

Lemma cnf_LPD_respects_FP_policy_at_preemption_point (job_task : Job -> Task) hR hL (Hh : CnfRelRel Task hR hL) :
  PropSPropRel (LimitedPreemptionPlatform.respects_FP_policy_at_preemption_point aR cR job_task arrR sR pR hR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_Definitions_LimitedPreemptionPlatform_respects_FP_policy_at_preemption_point Task dT Job dJ aL cL job_task arrL sL pL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnf_LPD_preemption_time Job sR sL Hs pR pL Hp tR tL Ht)).
  apply: ct_imp; first exact (cnf_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnf_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cnf_US_scheduled_at Job sR sL Hs j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh (job_task j_hp) (job_task j))).
Qed.

End LPDResp.

(* ------------------------------------------------------------------ *)
(** * [\max] over a filtered sequence against the v0.6 [maxFiltered] (through the exported equation
    [maxFiltered_eq_foldr_cond]) *)

Section PIBMaxSeq.
Variable X : Type.
Variables (PR : X -> bool) (PL : X -> I.Bool).
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).
Variables (FR : X -> nat) (FL : X -> Lean.Nat).
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cnf_foldr_max_cond : forall s : seq X,
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

Lemma cnf_max_filtered_rel s sL (Hs : ClListRel cid s sL) :
  SubNatRel (\max_(x <- s | PR x) FR x) (I.Prosa_Util_Sum_maxFiltered X sL PL FL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite -(imported_eq_to_coq_eq _ _ Hs).
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicNonprFpRtaInterface_maxFiltered_eq_foldr_cond X PL FL (cl_map cid s))).
  exact (Logic.eq_sym (cnf_foldr_max_cond s)).
Qed.

End PIBMaxSeq.

Lemma cnf_PIB_max_length_of_priority_inversion (Job : eqType) mR mL (Hm : CnfParRel Job mR mL)
    arrR arrL (Harr : CnfArrRel Job arrR arrL) hR hL (Hh : CnfRelRel Job hR hL) j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (@PriorityInversionIsBounded.max_length_of_priority_inversion Job mR arrR hR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_Platform_PriorityInversionIsBounded_PriorityInversionIsBounded_max_length_of_priority_inversion Job (ct_decidable_eq Job) mL arrL hL j tL).
Proof.
  exact (cnf_max_filtered_rel Job _ _ (fun x => ct_bool_not _ _ (Hh x j)) _ _ (fun x => ct_sub_rel _ _ _ _ (Hm x) (sub_nat_rel_canonical 1))
           _ _ (cnf_jobs_arrived_before Job arrR arrL Harr tR tL Ht)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves_blocking_bound_correspondence (Task : eqType) mR mL (Hm : CnfParRel Task mR mL) hR hL (Hh : CnfRelRel Task hR hL)
    tsR tsL (Hts : ClListRel (B := Task) cid tsR tsL) tsk :
  SubNatRel (@RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound Task mR hR tsR tsk) (I.Prosa_Classic_Model_Schedule_Uni_Limited_FixedPriority_NonprReg_ResponseTimeBound_RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves_blocking_bound Task (ct_decidable_eq Task) mL hL tsL tsk).
Proof.
  exact (cnf_max_filtered_rel Task _ _ (fun x => ct_bool_not _ _ (Hh x tsk)) _ _ (fun x => ct_sub_rel _ _ _ _ (Hm x) (sub_nat_rel_canonical 1)) tsR tsL Hts).
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
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CnfParRel _ f g |- _ => exact (H x) end
  | |- CtBoolRel (?f ?x ?y) (?g ?x ?y) => match goal with H : CnfRelRel _ f g |- _ => exact (H x y) end
  | |- CtBoolRel (?f ?x ?t) (?g ?x ?u) => match goal with H : CnfPmRel _ f g |- _ => eapply H end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | ArrivalSequence.arrival_sequence _ => apply: (cnf_forall_arr _); intros ? ? ?
  | UniprocessorSchedule.schedule _ => apply: (cnf_forall_sched _); intros ? ? ?
  | Priority.FP_policy _ => apply: (cnf_forall_rel _); intros ? ? ?
  | Priority.JLFP_policy _ => apply: (cnf_forall_rel _); intros ? ? ?
  | seq _ => apply: (cnf_forall_list _); intros ? ? ?
  | _ -> nat -> nat => apply: (cnf_forall_curve _); intros ? ? ?
  | _ -> Time.time -> nat => apply: (cnf_forall_curve _); intros ? ? ?
  | _ -> nat -> bool => apply: (cnf_forall_pm _); intros ? ? ?
  | _ -> Time.time -> bool => apply: (cnf_forall_pm _); intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: cnf_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp; crel
  | lazymatch goal with
    | |- forall _, _ => intro; crel
    | |- CnfIntRel _ (JLFPInstantiation.interference _ _) _ => fail; crel
    | |- CnfWlRel _ (JLFPInstantiation.interfering_workload _ _ _ _) _ => fail; crel
    | |- CnfRelRel _ (Priority.FP_to_JLFP _ _) _ => eapply cnf_PR_FP_to_JLFP; crel
    | |- CnfRelRel _ (Priority.EDF _ _) _ => fail; crel
    | |- CnfIntRel _ (fun _ => _) _ => fail; crel
    | |- CnfWlRel _ (fun _ => _) _ => fail; crel
    | |- CnfRelRel _ (fun _ => _) _ => first [ eapply cnf_PR_FP_to_JLFP; crel | fail; crel | intros ? ?; cbv beta; crel ]
    | |- CtBoolRel (orb _ _) _ => fail; crel
    | |- CnfFunRel _ _ => intros ? ? ?; cbv beta; crel
    | |- CnfNatFunRel _ _ => intros ? ? ?; cbv beta; crel
    | |- CnfIbfRel _ _ _ => intros ? ? ? ? ? ? ?; cbv beta; crel
    | |- CnfPredRel _ _ _ => intro; cbv beta; crel
    | |- CnfParRel _ (fun _ => _) _ => intro; cbv beta; crel
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
  | S _ => eapply cnf_succ_rel; crel
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
  | _ <-> _ => eapply cnf_iff; crel
  | _ <> _ => eapply cnf_ne
  | ~ _ => eapply ct_imp; [crel | exact cnf_false_rel]
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else crel_eq_defs
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_eq_defs := first [ eapply ct_eq_rel | fail; crel ]
with crel_n_defs := first [ (match goal with |- context [@MaxArrivalsWorkloadBound.task_request_bound_function] => idtac end; eapply cnf_WB_task_request_bound_function; crel)
    | (match goal with |- context [@MaxArrivalsWorkloadBound.total_hep_request_bound_function_FP] => idtac end; eapply cnf_WB_total_hep_request_bound_function_FP; crel)
    | (match goal with |- context [@MaxArrivalsWorkloadBound.total_ohep_request_bound_function_FP] => idtac end; eapply cnf_WB_total_ohep_request_bound_function_FP; crel)
    | eapply cnf_ico; crel
    | eapply ct_bool_to_nat; crel
    | (match goal with |- context [@BusyIntervalJLFP.cumulative_priority_inversion] => idtac end; eapply cnf_LBI_cumulative_priority_inversion; crel)
    | eapply cnf_sum_filtered_rel; crel
    | eapply cnf_sum_rel; crel
    | (match goal with |- context [@RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves.blocking_bound] => idtac end; eapply RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves_blocking_bound_correspondence; crel)
    | (match goal with |- context [@PriorityInversionIsBounded.max_length_of_priority_inversion] => idtac end; eapply cnf_PIB_max_length_of_priority_inversion; crel)
    | (match goal with |- context [@UniprocessorSchedule.service] => idtac end; eapply cnf_US_service; crel)
    | (match goal with |- context [@UniprocessorSchedule.service_during] => idtac end; eapply cnf_US_service_during; crel)
    | (match goal with |- context [@UniprocessorSchedule.service_at] => idtac end; eapply cnf_US_service_at; crel) ]
with crel_b_defs := first [ (match goal with |- context [@BusyIntervalJLFP.is_priority_inversion] => idtac end; eapply cnf_LBI_is_priority_inversion; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.preemption_time] => idtac end; eapply cnf_LPD_preemption_time; crel)
    | (match goal with |- context [@UniprocessorSchedule.scheduled_at] => idtac end; eapply cnf_US_scheduled_at; crel)
    | (match goal with |- context [@UniprocessorSchedule.completed_by] => idtac end; eapply cnf_US_completed_by; crel)
    | (match goal with |- context [@UniprocessorSchedule.pending] => idtac end; eapply cnf_US_pending; crel)
    | (match goal with |- context [@UniprocessorSchedule.backlogged] => idtac end; eapply cnf_US_backlogged; crel)
    | (match goal with |- context [@ArrivalSequence.has_arrived] => idtac end; eapply cnf_has_arrived; crel)
    | (match goal with |- context [@ArrivalSequence.arrived_before] => idtac end; eapply cnf_arrived_before; crel)
    | (match goal with |- context [@ArrivalSequence.arrives_at] => idtac end; eapply cnf_arrives_at; crel)
    | (match goal with |- context [@Job.job_cost_positive] => idtac end; eapply cnf_J_job_cost_positive; crel)
    | (match goal with |- context [@Job.job_cost_le_task_cost] => idtac end; eapply cnf_J_job_cost_le_task_cost; crel)
    | (match goal with |- context [@TaskArrival.is_job_of_task] => idtac end; eapply cnf_TA_is_job_of_task; crel) ]
with crel_l_defs := first [ (match goal with |- context [@ArrivalSequence.jobs_arrived_before] => idtac end; eapply cnf_jobs_arrived_before; crel)
    | (match goal with |- context [@ArrivalSequence.jobs_arrived_between] => idtac end; eapply cnf_jobs_arrived_between; crel)
    | (match goal with |- context [@ArrivalSequence.jobs_arriving_at] => idtac end; eapply cnf_arriving_at; crel) ]
with crel_p_defs := first [ (match goal with |- context [@Priority.FP_is_reflexive] => idtac end; eapply cnf_PR_FP_is_reflexive; crel)
    | (match goal with |- context [@Priority.FP_is_transitive] => idtac end; eapply cnf_PR_FP_is_transitive; crel)
    | (match goal with |- context [@BusyIntervalJLFP.priority_inversion_is_bounded_by] => idtac end; eapply cnf_LBI_priority_inversion_is_bounded_by; crel)
    | (match goal with |- context [@BusyIntervalJLFP.quiet_time] => idtac end; eapply cnf_LBI_quiet_time; crel)
    | (match goal with |- context [@BusyIntervalJLFP.busy_interval_prefix] => idtac end; eapply cnf_LBI_busy_interval_prefix; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.work_conserving] => idtac end; eapply cnf_LP_work_conserving; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.correct_preemption_model] => idtac end; eapply cnf_LPD_correct_preemption_model; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.model_with_bounded_nonpreemptive_segments] => idtac end; eapply cnf_LPD_model_with_bounded_nonpreemptive_segments; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.respects_FP_policy_at_preemption_point] => idtac end; eapply cnf_LPD_respects_FP_policy_at_preemption_point; crel)
    | (match goal with |- context [@LimitedPreemptionPlatform.work_conserving] => idtac end; eapply cnf_LPD_work_conserving; crel)
    | (match goal with |- context [@LS.job_lock_in_service_positive] => idtac end; eapply cnf_LS_job_lock_in_service_positive; crel)
    | (match goal with |- context [@LS.job_lock_in_service_le_job_cost] => idtac end; eapply cnf_LS_job_lock_in_service_le_job_cost; crel)
    | (match goal with |- context [@LS.job_nonpreemptive_after_lock_in_service] => idtac end; eapply cnf_LS_job_nonpreemptive_after_lock_in_service; crel)
    | (match goal with |- context [@LS.proper_job_lock_in_service] => idtac end; eapply cnf_LS_proper_job_lock_in_service; crel)
    | (match goal with |- context [@LS.task_lock_in_service_le_task_cost] => idtac end; eapply cnf_LS_task_lock_in_service_le_task_cost; crel)
    | (match goal with |- context [@LS.task_lock_in_service_bounds_job_lock_in_service] => idtac end; eapply cnf_LS_task_lock_in_service_bounds_job_lock_in_service; crel)
    | (match goal with |- context [@LS.proper_task_lock_in_service] => idtac end; eapply cnf_LS_proper_task_lock_in_service; crel)
    | (match goal with |- context [@ArrivalCurves.family_of_proper_arrival_curves] => idtac end; eapply cnf_AC_family_of_proper_arrival_curves; crel)
    | (match goal with |- context [@ArrivalCurves.is_arrival_bound] => idtac end; eapply cnf_AC_is_arrival_bound; crel)
    | (match goal with |- context [@ArrivalCurves.proper_arrival_curve] => idtac end; eapply cnf_AC_proper_arrival_curve; crel)
    | (match goal with |- context [@iff] => idtac end; eapply cnf_iff; crel)
    | (match goal with |- context [@BusyIntervalJLFP.priority_inversion_of_job_is_bounded_by] => idtac end; eapply cnf_LBI_priority_inversion_of_job_is_bounded_by; crel)
    | (match goal with |- context [@ArrivalSequence.arrives_in] => idtac end; eapply cnf_arrives_in; crel)
    | (match goal with |- context [@ArrivalSequence.arrival_times_are_consistent] => idtac end; eapply cnf_consistent; crel)
    | (match goal with |- context [@ArrivalSequence.arrival_sequence_is_a_set] => idtac end; eapply cnf_is_a_set; crel)
    | eapply cnf_mem; crel
    | eapply cnf_uniq; crel
    | (match goal with |- context [@UniprocessorSchedule.jobs_come_from_arrival_sequence] => idtac end; eapply cnf_US_jobs_come_from_arrival_sequence; crel)
    | (match goal with |- context [@UniprocessorSchedule.jobs_must_arrive_to_execute] => idtac end; eapply cnf_US_jobs_must_arrive_to_execute; crel)
    | (match goal with |- context [@UniprocessorSchedule.completed_jobs_dont_execute] => idtac end; eapply cnf_US_completed_jobs_dont_execute; crel)
    | (match goal with |- context [@UniprocessorSchedule.sequential_jobs] => idtac end; eapply cnf_US_sequential_jobs; crel)
    | (match goal with |- context [@Job.cost_of_jobs_from_arrival_sequence_le_task_cost] => idtac end; eapply cnf_J_cost_of_jobs_from_arrival_sequence_le_task_cost; crel)
    | (match goal with |- context [@ResponseTime.is_response_time_bound_of_job] => idtac end; eapply cnf_RT_is_response_time_bound_of_job; crel)
    | (match goal with |- context [@ResponseTime.is_response_time_bound_of_task] => idtac end; eapply cnf_RT_is_response_time_bound_of_task; crel) ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_priority_inversion_is_bounded_by_blocking (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves.priority_inversion_is_bounded_by_blocking Task p0 p1 Job)).
Definition tgt_priority_inversion_is_bounded_by_blocking (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_FixedPriority_NonprReg_ResponseTimeBound_RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves_priority_inversion_is_bounded_by_blocking Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves_priority_inversion_is_bounded_by_blocking_correspondence (Task Job : eqType) :
  PropSPropRel (src_priority_inversion_is_bounded_by_blocking Task Job) (tgt_priority_inversion_is_bounded_by_blocking Task Job).
Proof. unfold src_priority_inversion_is_bounded_by_blocking, tgt_priority_inversion_is_bounded_by_blocking. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_priority_inversion_is_bounded (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves.priority_inversion_is_bounded Task p0 p1 Job)).
Definition tgt_priority_inversion_is_bounded (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_FixedPriority_NonprReg_ResponseTimeBound_RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves_priority_inversion_is_bounded Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves_priority_inversion_is_bounded_correspondence (Task Job : eqType) :
  PropSPropRel (src_priority_inversion_is_bounded Task Job) (tgt_priority_inversion_is_bounded Task Job).
Proof. unfold src_priority_inversion_is_bounded, tgt_priority_inversion_is_bounded. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves.uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments Task p0 p1 Job)).
Definition tgt_uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_FixedPriority_NonprReg_ResponseTimeBound_RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves_uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem RTAforFPwithBoundedNonpreemptiveSegmentsWithArrivalCurves_uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments_correspondence (Task Job : eqType) :
  PropSPropRel (src_uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments Task Job) (tgt_uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments Task Job).
Proof. unfold src_uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments, tgt_uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments. crel_spine. crel. Unshelve. all: crel. Qed.
