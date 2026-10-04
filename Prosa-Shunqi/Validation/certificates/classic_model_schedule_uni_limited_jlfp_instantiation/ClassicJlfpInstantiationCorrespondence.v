From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.notation classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.service classic.model.schedule.uni.workload classic.model.schedule.uni.schedule_of_task classic.model.schedule.uni.limited.busy_interval classic.model.schedule.uni.limited.abstract_RTA.definitions classic.model.schedule.uni.limited.abstract_RTA.abstract_seq_rta classic.model.schedule.uni.limited.jlfp_instantiation.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicJlfpInstantiation.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicJlfpInstantiationBase ClassicJlfpInstantiationList.



Module I := ImportedClassicJlfpInstantiation.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/limited/jlfp_instantiation.v] (ProsaBuddy classic, commit f692cb7).

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

Lemma cji_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cji_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cji_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cji_false_rel). Qed.

Lemma cji_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cji_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cji_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cji_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cji_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cji_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cji_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cji_unmap_rel T l) PR PL).
Qed.

Definition CjiParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cji_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CjiParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cji_forall_cover _ _ (CjiParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cji_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cji_natl s') end.

Definition cji_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cji_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cji_one) (cji_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cji_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cji_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cji_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cji_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cji_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cji_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cji_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cji_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cji_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cji_cl_append. reflexivity.
Qed.

Lemma cji_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CjiFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cji_bigcat_rel (A : Type) fR fL (Hf : CjiFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJlfpInstantiationInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cji_iota_range (nR - mR) 0) cji_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cji_cl_map_ext _ _ Hpt) (cji_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cji_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cji_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CjiArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cji_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cji_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cji_arr_canonical aR : CjiArrRel aR (cji_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cji_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cji_arr_surjective aL : CjiArrRel (cji_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cji_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CjiArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cji_forall_cover _ _ CjiArrRel cji_arr_to_target cji_arr_to_source cji_arr_canonical cji_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cji_jobs_arrived_between aR aL (Ha : CjiArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cji_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cji_arrives_in aR aL (Ha : CjiArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cji_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cji_consistent pR pL (Hp : CjiParRel Job pR pL) aR aL (Ha : CjiArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cji_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cji_is_a_set aR aL (Ha : CjiArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cji_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cji_jobs_arrived_before aR aL (Ha : CjiArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job dJ aL tL).
Proof. exact (cji_jobs_arrived_between Job aR aL Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma cji_arrives_at aR aL (Ha : CjiArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cji_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma cji_has_arrived pR pL (Hp : CjiParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

Lemma cji_arrived_before pR pL (Hp : CjiParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrived_before pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_before Job dJ pL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cji_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cji_snatl s') end.

Lemma cji_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cji_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cji_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cji_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cji_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cji_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cji_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CjiFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cji_fun_canonical FR FL (HF : CjiFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cji_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cji_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CjiFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cji_nat_sub_canonical nR mR.
  rewrite cji_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cji_foldr_add FL FR (cji_fun_canonical FR FL HF)).
  by rewrite cji_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cji_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cji_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cji_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cji_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cji_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CjiSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cji_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cji_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cji_sched_canonical sR : CjiSchedRel sR (cji_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cji_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cji_sched_surjective sL : CjiSchedRel (cji_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cji_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cji_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CjiSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cji_forall_cover _ _ CjiSchedRel cji_sched_to_target cji_sched_to_source cji_sched_canonical cji_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cji_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CjiSchedRel Job sR (cji_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CjiSchedRel Job (cji_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cji_sched_canonical Job) (cji_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjiSchedRel Job sR sL.

Lemma cji_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cji_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cji_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cji_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cji_US_scheduled_at j tR tL Ht)). Qed.

Lemma cji_service_at_fun j : CjiFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cji_US_service_at j kR kL Hk). Qed.

Lemma cji_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cji_ico _ _ _ _ _ _ H1 H2 (cji_service_at_fun j)). Qed.

Lemma cji_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cji_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cji_US_completed_by cR cL (Hc : CjiParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cji_US_service j tR tL Ht)). Qed.

Lemma cji_US_pending_earlier_and_at aR aL (Ha : CjiParRel Job aR aL) cR cL (Hc : CjiParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending_earlier_and_at aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending_earlier_and_at Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cji_arrived_before Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cji_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cji_US_sequential_jobs (Task : eqType) aR aL (Ha : CjiParRel Job aR aL) cR cL (Hc : CjiParRel Job cR cL)
    (job_task : Job -> Task) :
  PropSPropRel (UniprocessorSchedule.sequential_jobs aR cR sR job_task)
    (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_sequential_jobs Job dJ aL cL sL Task (ct_decidable_eq Task) job_task).
Proof.
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_eq Task (job_task j1) (job_task j2))).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha j1) (Ha j2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cji_US_scheduled_at j2 tR tL Ht)).
  exact (ct_bool_truth _ _ (cji_US_completed_by cR cL Hc j1 tR tL Ht)).
Qed.

Lemma cji_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CjiArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cji_US_scheduled_at j tR tL Ht)).
  exact (cji_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cji_US_jobs_must_arrive_to_execute aR aL (Ha : CjiParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cji_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cji_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma cji_US_completed_jobs_dont_execute cR cL (Hc : CjiParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cji_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cji_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicJlfpInstantiationInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicJlfpInstantiationInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cji_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cji_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cji_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicJlfpInstantiationInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicJlfpInstantiationInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicJlfpInstantiationInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cji_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cji_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CjiPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma cji_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CjiPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cji_forall_cover _ _ (CjiPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CjiRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cji_rel_canonical (T : Type) (rR : T -> T -> bool) : CjiRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cji_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CjiRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cji_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CjiRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cji_forall_cover _ _ (CjiRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cji_rel_canonical T) (cji_rel_surjective T) PR PL).
Qed.

Definition CjiJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CjiRelRel T (rR tR) (rL tL).

Lemma cji_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CjiJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cji_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CjiJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cji_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CjiJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cji_forall_cover _ _ (CjiJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cji_jldp_canonical T) (cji_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cji_PR_JLFP_policy :
  And (forall rR : Priority.JLFP_policy Job, CjiRelRel Job rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLFP_policy Job dJ, CjiRelRel Job (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cji_rel_canonical Job) (cji_rel_surjective Job)). Qed.

Lemma cji_reflexive (T : Type) rR rL (Hr : CjiRelRel T rR rL) :
  PropSPropRel (reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_reflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (Hr x x)). Qed.

Lemma cji_PR_JLFP_is_reflexive rR rL (Hr : CjiRelRel Job rR rL) :
  PropSPropRel (Priority.JLFP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_JLFP_is_reflexive Job dJ rL).
Proof. exact (cji_reflexive Job rR rL Hr). Qed.

Lemma cji_PR_JLFP_respects_sequential_jobs (job_task : Job -> Task) jaR jaL (Hja : CjiParRel Job jaR jaL)
    rR rL (Hr : CjiRelRel Job rR rL) :
  PropSPropRel (Priority.JLFP_respects_sequential_jobs job_task jaR rR)
    (I.Prosa_Classic_Model_Priority_Priority_JLFP_respects_sequential_jobs Task Job dT dJ job_task jaL rL).
Proof.
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_eq Task (job_task j1) (job_task j2))).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j1) (Hja j2)).
  exact (ct_bool_truth _ _ (Hr j1 j2)).
Qed.

End PriodefsDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cji_J_job_cost_positive cR cL (Hc : CjiParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

End JobDefs.

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cji_TA_is_job_of_task (job_task : Job -> Task) tsk j :
  CtBoolRel (TaskArrival.is_job_of_task job_task tsk j)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk j).
Proof. exact (ct_decide_eq Task (job_task j) tsk). Qed.

Lemma cji_TA_arrivals_of_task_between (job_task : Job -> Task) aR aL (Ha : CjiArrRel Job aR aL) tsk
    t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (TaskArrival.arrivals_of_task_between job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_between Task Job dT dJ job_task aL tsk t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans (cl_filter cid _ (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk)
                            (cji_TA_is_job_of_task job_task tsk) _) _).
  exact (f_equal (I.List_filter Job (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk))
           (Logic.eq_sym (cl_list_logic _ _ _ (cji_jobs_arrived_between Job aR aL Ha _ _ _ _ H1 H2)))).
Qed.

Lemma cji_TA_arrivals_of_task_before (job_task : Job -> Task) aR aL (Ha : CjiArrRel Job aR aL) tsk
    tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (TaskArrival.arrivals_of_task_before job_task aR tsk tR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_arrivals_of_task_before Task Job dT dJ job_task aL tsk tL).
Proof. exact (cji_TA_arrivals_of_task_between job_task aR aL Ha tsk 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

End TaskArrivalDefs.

Section AcboundsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

(** Curves [Task -> nat -> nat] pointwise on related arguments. *)
Definition CjiCurveRel (fR : Task -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk nR nL, SubNatRel nR nL -> SubNatRel (fR tsk nR) (fL tsk nL).

End AcboundsDefs.

(** * Arrival curves [Task -> time -> nat], with two-way totals *)

Lemma cji_curve_canonical (Task : eqType) mR : CjiCurveRel Task mR (fun tsk nL => sub_nat_to_imported (mR tsk (sub_nat_to_rocq nL))).
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma cji_curve_surjective (Task : eqType) mL : CjiCurveRel Task (fun tsk nR => sub_nat_to_rocq (mL tsk (sub_nat_to_imported nR))) mL.
Proof. intros tsk nR nL Hn. have E := cl_nat_logic _ _ Hn. subst nL. exact (sub_nat_rel_surjective _). Qed.

Lemma cji_forall_curve (Task : eqType) (PR : (Task -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall mR mL, CjiCurveRel Task mR mL -> PropSPropRel (PR mR) (PL mL)) -> PropSPropRel (forall m, PR m) (forall m, PL m).
Proof. exact (cji_forall_cover _ _ (CjiCurveRel Task) _ _ (cji_curve_canonical Task) (cji_curve_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section AcwbDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat).
Hypothesis Htc : CjiParRel Task tcR tcL.
Variables (mR : Task -> nat -> nat) (mL : Task -> Lean.Nat -> Lean.Nat).
Hypothesis Hm : CjiCurveRel Task mR mL.

End AcwbDefs.

Section UwlDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cji_WL_workload_of_jobs cR cL (Hc : CjiParRel Job cR cL) jobsR jobsL (Hj : ClListRel cid jobsR jobsL)
    pR pL (Hp : CjiPredRel Job pR pL) :
  SubNatRel (Workload.workload_of_jobs cR jobsR pR) (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_workload_of_jobs Job dJ cL jobsL pL).
Proof. exact (cji_sum_filtered_rel Job cR cL Hc pR pL Hp _ _ Hj). Qed.

End UwlDefs.

Section UrtDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjiSchedRel Job sR sL.

End UrtDefs.

Section UplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjiSchedRel Job sR sL.

End UplatDefs.

Lemma cji_iff (P Q : Prop) (PL QL : SProp) :
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

Lemma cji_eq_transport (T : Type) (a b : T) aL bL : Lean.eq a aL -> Lean.eq b bL ->
  PropSPropRel (Logic.eq a b) (Lean.eq aL bL).
Proof. intros Ha Hb. destruct Ha. destruct Hb. exact (ct_eq_rel T a b). Qed.

(** Functions [nat -> T] (identical values) and [nat -> nat] (values by [SubNatRel]), pointwise on related arguments. *)
Definition CjiRsFunRel (T : Type) (fR : nat -> T) (fL : Lean.Nat -> T) : SProp :=
  forall nR nL, SubNatRel nR nL -> Lean.eq (fR nR) (fL nL).
Definition CjiNatFunRel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) : SProp :=
  forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

(** Interference bound functions [Task -> time -> time -> time], pointwise on related arguments and values. *)
Definition CjiIbfRel (Task : Type) (fR : Task -> nat -> nat -> nat) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : SProp :=
  forall tsk, forall aR aL, SubNatRel aR aL -> CjiNatFunRel (fR tsk aR) (fL tsk aL).

Definition cji_ibf_to_target (Task : Type) (fR : Task -> nat -> nat -> nat) : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat :=
  fun tsk aL xL => sub_nat_to_imported (fR tsk (sub_nat_to_rocq aL) (sub_nat_to_rocq xL)).
Definition cji_ibf_to_source (Task : Type) (fL : Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) : Task -> nat -> nat -> nat :=
  fun tsk aR xR => sub_nat_to_rocq (fL tsk (sub_nat_to_imported aR) (sub_nat_to_imported xR)).

Lemma cji_ibf_canonical (Task : Type) fR : CjiIbfRel Task fR (cji_ibf_to_target Task fR).
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  unfold cji_ibf_to_target. rewrite !sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma cji_ibf_surjective (Task : Type) fL : CjiIbfRel Task (cji_ibf_to_source Task fL) fL.
Proof.
  intros tsk aR aL Ha xR xL Hx. have Ea := cl_nat_logic _ _ Ha. have Ex := cl_nat_logic _ _ Hx. subst aL xL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma cji_forall_ibf (Task : Type) (PR : (Task -> nat -> nat -> nat) -> Prop) (PL : (Task -> Lean.Nat -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, CjiIbfRel Task fR fL -> PropSPropRel (PR fR) (PL fL)) -> PropSPropRel (forall f, PR f) (forall f, PL f).
Proof. exact (cji_forall_cover _ _ (CjiIbfRel Task) (cji_ibf_to_target Task) (cji_ibf_to_source Task) (cji_ibf_canonical Task) (cji_ibf_surjective Task) PR PL). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(* ------------------------------------------------------------------ *)
(** * Interference predicates and interfering workloads *)

Section SEQARDIRel.
Variable Job : eqType.

Definition CjiIntRel (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (iR j tR) (iL j tL).

Lemma cji_int_canonical iR : CjiIntRel iR (fun j tL => ct_b2l (iR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (ct_bool_canonical _). Qed.

Lemma cji_int_surjective iL : CjiIntRel (fun j tR => ct_l2b (iL j (sub_nat_to_imported tR))) iL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

Lemma cji_forall_int (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall iR iL, CjiIntRel iR iL -> PropSPropRel (PR iR) (PL iL)) -> PropSPropRel (forall i, PR i) (forall i, PL i).
Proof. exact (cji_forall_cover _ _ CjiIntRel _ _ cji_int_canonical cji_int_surjective PR PL). Qed.

Definition CjiWlRel (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (wR j tR) (wL j tL).

Lemma cji_wl_canonical wR : CjiWlRel wR (fun j tL => sub_nat_to_imported (wR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _). Qed.

Lemma cji_wl_surjective wL : CjiWlRel (fun j tR => sub_nat_to_rocq (wL j (sub_nat_to_imported tR))) wL.
Proof. intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL. exact (sub_nat_rel_surjective _). Qed.

Lemma cji_forall_wl (PR : (Job -> nat -> nat) -> Prop) (PL : (Job -> Lean.Nat -> Lean.Nat) -> SProp) :
  (forall wR wL, CjiWlRel wR wL -> PropSPropRel (PR wR) (PL wL)) -> PropSPropRel (forall w, PR w) (forall w, PL w).
Proof. exact (cji_forall_cover _ _ CjiWlRel _ _ cji_wl_canonical cji_wl_surjective PR PL). Qed.

End SEQARDIRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section SEQARDDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cji_ARD_cumul_interference iR iL (Hi : CjiIntRel Job iR iL) j t1R t1L (H1 : SubNatRel t1R t1L)
    t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (AbstractRTADefinitions.cumul_interference iR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_cumul_interference Job dJ iL j t1L t2L).
Proof. exact (cji_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (Hi j kR kL Hk))). Qed.

Lemma cji_ARD_cumul_interfering_workload wR wL (Hw : CjiWlRel Job wR wL) j t1R t1L (H1 : SubNatRel t1R t1L)
    t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (AbstractRTADefinitions.cumul_interfering_workload wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_cumul_interfering_workload Job dJ wL j t1L t2L).
Proof. exact (cji_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => Hw j kR kL Hk)). Qed.

Notation CI := cji_ARD_cumul_interference.
Notation CW := cji_ARD_cumul_interfering_workload.

Section SEQARDSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjiSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CjiParRel Job aR aL) (Hc : CjiParRel Job cR cL).
Variables (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat).
Hypotheses (Hi : CjiIntRel Job iR iL) (Hw : CjiWlRel Job wR wL).

Lemma cji_ARD_quiet_time j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (AbstractRTADefinitions.quiet_time aR cR sR iR wR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_quiet_time Job dJ aL cL sL iL wL j tL).
Proof.
  apply: ct_and.
  - exact (sub_nat_eq_correspondence _ _ _ _ (CI iR iL Hi j 0 _ (sub_nat_rel_canonical 0) tR tL Ht)
             (CW wR wL Hw j 0 _ (sub_nat_rel_canonical 0) tR tL Ht)).
  - exact (ct_bool_truth _ _ (ct_bool_not _ _ (cji_US_pending_earlier_and_at Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht))).
Qed.

Lemma cji_ARD_busy_interval_prefix j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (AbstractRTADefinitions.busy_interval_prefix aR cR sR iR wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_interval_prefix Job dJ aL cL sL iL wL j t1L t2L).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Ha j)) (ct_decide_lt _ _ _ _ (Ha j) H2))).
  apply: ct_and; first exact (cji_ARD_quiet_time j t1R t1L H1).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  exact (ct_imp _ _ _ _ (cji_ARD_quiet_time j tR tL Ht) cji_false_rel).
Qed.

Lemma cji_ARD_busy_interval j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (AbstractRTADefinitions.busy_interval aR cR sR iR wR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_Definitions_AbstractRTADefinitions_busy_interval Job dJ aL cL sL iL wL j t1L t2L).
Proof.
  apply: ct_and; first exact (cji_ARD_busy_interval_prefix j t1R t1L H1 t2R t2L H2).
  exact (cji_ARD_quiet_time j t2R t2L H2).
Qed.

Notation BI := cji_ARD_busy_interval.

End SEQARDSched.

End SEQARDDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Module LS := prosa.classic.model.schedule.uni.limited.schedule.

Section SEQLSDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CjiParRel Job cR cL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CjiArrRel Job arrR arrL.
Variables (lR : Job -> nat) (lL : Job -> Lean.Nat).
Hypothesis Hl : CjiParRel Job lR lL.

Section SEQLSSched.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjiSchedRel Job sR sL.

End SEQLSSched.

Variables (tcR : Task -> nat) (tcL : Task -> Lean.Nat) (tlR : Task -> nat) (tlL : Task -> Lean.Nat).
Hypotheses (Htc : CjiParRel Task tcR tcL) (Htl : CjiParRel Task tlR tlL).

End SEQLSDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section SEQSVDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjiSchedRel Job sR sL.

Lemma cji_SV_service_of_jobs jobsR jobsL (Hj : ClListRel cid jobsR jobsL) pR pL (Hp : CjiPredRel Job pR pL)
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.service_of_jobs sR jobsR pR t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs Job dJ sL jobsL pL t1L t2L).
Proof.
  exact (cji_sum_filtered_rel Job (fun j => UniprocessorSchedule.service_during sR j t1R t2R)
           (fun j => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L)
           (fun j => cji_US_service_during Job sR sL Hs j _ _ H1 _ _ H2) pR pL Hp _ _ Hj).
Qed.

End SEQSVDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section SEQSTDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjiSchedRel Job sR sL.
Variable job_task : Job -> Task.

Lemma cji_ST_task_scheduled_at tsk tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleOfTask.task_scheduled_at job_task sR tsk tR) (I.Prosa_Classic_Model_Schedule_Uni_ScheduleOfTask_ScheduleOfTask_task_scheduled_at Task dT Job dJ job_task sL tsk tL).
Proof.
  refine (cji_trs (Hs tR tL Ht)
            (fun z => CtBoolRel (ScheduleOfTask.task_scheduled_at job_task sR tsk tR)
                        (match z with
                         | I.Option_some j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk)
                         | I.Option_none => I.Bool_false end)) _).
  rewrite /ScheduleOfTask.task_scheduled_at. destruct (sR tR) as [x|].
  - exact (ct_decide_eq Task (job_task x) tsk).
  - exact (ct_bool_canonical false).
Qed.

End SEQSTDefs.

(* ------------------------------------------------------------------ *)
(** * [has] against [List.any] *)

Lemma cji_has_eq (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL x)) :
  forall s, Logic.eq (I.List_any T (cl_map cid s) pL) (ct_b2l (has pR s)).
Proof.
  elim => [|x s IH]; first reflexivity.
  have -> : Logic.eq (I.List_any T (cl_map cid (x :: s)) pL) (I.Bool_or (pL x) (I.List_any T (cl_map cid s) pL)).
  { cbn. destruct (pL x); reflexivity. }
  rewrite (ct_bool_rel_logic _ _ (Hp x)) IH /=. by case: (pR x); case: (has pR s).
Qed.

Lemma cji_has (T : Type) (pR : T -> bool) (pL : T -> I.Bool) (Hp : forall x, CtBoolRel (pR x) (pL x)) :
  forall s, CtBoolRel (has pR s) (I.List_any T (cl_map cid s) pL).
Proof. intro s. exact (coq_eq_to_imported_eq _ _ (Logic.eq_sym (cji_has_eq T pR pL Hp s))). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section SEQDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjiSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CjiParRel Job aR aL) (Hc : CjiParRel Job cR cL).
Variable job_task : Job -> Task.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CjiArrRel Job arrR arrL.
Variables (iR : Job -> nat -> bool) (iL : Job -> Lean.Nat -> I.Bool) (wR : Job -> nat -> nat) (wL : Job -> Lean.Nat -> Lean.Nat).
Hypotheses (Hi : CjiIntRel Job iR iL) (Hw : CjiWlRel Job wR wL).
Notation BI := (cji_ARD_busy_interval Job sR sL Hs aR aL cR cL Ha Hc iR iL wR wL Hi Hw).

Lemma cji_SEQ_task_interference_received_before tsk uR uL (Hu : SubNatRel uR uL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@AbstractSeqRTA.task_interference_received_before Task Job job_task arrR sR iR tsk uR tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_task_interference_received_before Task dT Job dJ job_task arrL sL iL tsk uL tL).
Proof.
  apply: ct_bool_and; first exact (ct_bool_not _ _ (cji_ST_task_scheduled_at Task Job sR sL Hs job_task tsk tR tL Ht)).
  refine (cji_trs (cji_TA_arrivals_of_task_before Task Job job_task arrR arrL Harr tsk uR uL Hu)
            (fun z => CtBoolRel _ (I.List_any Job z (fun j => iL j tL))) _).
  exact (cji_has Job _ _ (fun j => Hi j tR tL Ht) _).
Qed.

Lemma cji_SEQ_cumul_task_interference tsk uR uL (Hu : SubNatRel uR uL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (@AbstractSeqRTA.cumul_task_interference Task Job job_task arrR sR iR tsk uR t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_AbstractRTA_AbstractSeqRta_AbstractSeqRTA_cumul_task_interference Task dT Job dJ job_task arrL sL iL tsk uL t1L t2L).
Proof.
  exact (cji_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (cji_SEQ_task_interference_received_before tsk uR uL Hu kR kL Hk))).
Qed.

End SEQDefs.

(* ------------------------------------------------------------------ *)
(** * Service of jobs (as in the accepted classic uniprocessor service certificate) *)

Section LBISvc.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjiSchedRel Job sR sL.

Lemma cji_service_of_jobs jobsR jobsL (Hj : ClListRel cid jobsR jobsL) pR pL (Hp : CjiPredRel Job pR pL)
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.service_of_jobs sR jobsR pR t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs Job dJ sL jobsL pL t1L t2L).
Proof.
  exact (cji_sum_filtered_rel Job (fun j => UniprocessorSchedule.service_during sR j t1R t2R)
           (fun j => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L)
           (fun j => cji_US_service_during Job sR sL Hs j _ _ H1 _ _ H2) pR pL Hp _ _ Hj).
Qed.

End LBISvc.

(* ------------------------------------------------------------------ *)
(** * Auxiliary relations *)

Lemma cji_implb aR aL (Ha : CtBoolRel aR aL) bR bL (Hb : CtBoolRel bR bL) :
  CtBoolRel (aR ==> bR) (I.Bool_or (I.Bool_not aL) bL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite (ct_bool_rel_logic _ _ Ha) (ct_bool_rel_logic _ _ Hb). clear Ha Hb.
  by case: aR; case: bR.
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section LBIDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Hja : CjiParRel Job jaR jaL) (Hc : CjiParRel Job cR cL).
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CjiArrRel Job aR aL.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjiSchedRel Job sR sL.
Variables (hR : Job -> Job -> bool) (hL : Job -> Job -> I.Bool).
Hypothesis Hh : CjiRelRel Job hR hL.

Lemma cji_LBI_quiet_time j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (@BusyIntervalJLFP.quiet_time Job jaR cR aR sR hR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_quiet_time Job dJ jaL cL aL sL hL j tL).
Proof.
  apply: ct_forall_identity => j_hp.
  apply: ct_imp; first exact (cji_arrives_in Job aR aL Ha j_hp).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hh j_hp j)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cji_arrived_before Job jaR jaL Hja j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (cji_US_completed_by Job sR sL Hs cR cL Hc j_hp tR tL Ht)).
Qed.

Notation QT := cji_LBI_quiet_time.

Lemma cji_not_quiet j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (~ @BusyIntervalJLFP.quiet_time Job jaR cR aR sR hR j tR) (I.Not (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_quiet_time Job dJ jaL cL aL sL hL j tL)).
Proof. exact (ct_imp _ _ _ _ (QT j tR tL Ht) cji_false_rel). Qed.

Lemma cji_LBI_busy_interval_prefix j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (@BusyIntervalJLFP.busy_interval_prefix Job jaR cR aR sR hR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_busy_interval_prefix Job dJ jaL cL aL sL hL j t1L t2L).
Proof.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ H1 H2).
  apply: ct_and; first exact (QT j t1R t1L H1).
  apply: ct_and.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
    exact (cji_not_quiet j tR tL Ht). }
  exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (Hja j)) (ct_decide_lt _ _ _ _ (Hja j) H2))).
Qed.

Lemma cji_LBI_busy_interval j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (@BusyIntervalJLFP.busy_interval Job jaR cR aR sR hR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_busy_interval Job dJ jaL cL aL sL hL j t1L t2L).
Proof. exact (ct_and _ _ _ _ (cji_LBI_busy_interval_prefix j t1R t1L H1 t2R t2L H2) (QT j t2R t2L H2)). Qed.

Lemma cji_LBI_is_priority_inversion j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@BusyIntervalJLFP.is_priority_inversion Job sR hR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_is_priority_inversion Job dJ sL hL j tL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite /BusyIntervalJLFP.is_priority_inversion. unfold I.Prosa_Classic_Model_Schedule_Uni_Limited_BusyInterval_BusyIntervalJLFP_is_priority_inversion.
  rewrite -(imported_eq_to_coq_eq _ _ (Hs tR tL Ht)).
  case: (sR tR) => [jlp|]; last reflexivity.
  cbn. rewrite (ct_bool_rel_logic _ _ (Hh jlp j)). by case: (hR jlp j).
Qed.

End LBIDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cji_arriving_at (Job : eqType) aR aL (Ha : CjiArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arriving_at aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arriving_at Job (ct_decidable_eq Job) aL tL).
Proof. exact (Ha tR tL Ht). Qed.

Section Defs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjiSchedRel Job sR sL.
Variables (hR : Job -> Job -> bool) (hL : Job -> Job -> I.Bool).
Hypothesis Hh : CjiRelRel Job hR hL.
Variable job_task : Job -> Task.

Theorem JLFPInstantiation_is_interference_from_another_job_with_higher_eq_priority_correspondence j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@JLFPInstantiation.is_interference_from_another_job_with_higher_eq_priority Job sR hR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_is_interference_from_another_job_with_higher_eq_priority Job dJ sL hL j tL).
Proof.
  refine (cji_trs (Hs tR tL Ht) (fun z => CtBoolRel _ (match z with
      | I.Option_some jhp => I.Bool_and (hL jhp j) (I.Bool_not (I.Decidable_decide (Lean.eq jhp j) (dJ jhp j)))
      | I.Option_none => I.Bool_false end)) _).
  rewrite /JLFPInstantiation.is_interference_from_another_job_with_higher_eq_priority. destruct (sR tR) as [x|]; cbn.
  - exact (ct_bool_and _ _ _ _ (Hh x j) (ct_bool_not _ _ (ct_decide_eq Job x j))).
  - exact (ct_bool_canonical false).
Qed.

Theorem JLFPInstantiation_is_interference_from_another_task_with_higher_eq_priority_correspondence j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (@JLFPInstantiation.is_interference_from_another_task_with_higher_eq_priority Task Job job_task sR hR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_is_interference_from_another_task_with_higher_eq_priority Task dT Job dJ job_task sL hL j tL).
Proof.
  refine (cji_trs (Hs tR tL Ht) (fun z => CtBoolRel _ (match z with
      | I.Option_some jhp => I.Bool_and (hL jhp j) (I.Bool_not (I.Decidable_decide (Lean.eq (job_task jhp) (job_task j)) (dT (job_task jhp) (job_task j))))
      | I.Option_none => I.Bool_false end)) _).
  rewrite /JLFPInstantiation.is_interference_from_another_task_with_higher_eq_priority. destruct (sR tR) as [x|]; cbn.
  - exact (ct_bool_and _ _ _ _ (Hh x j) (ct_bool_not _ _ (ct_decide_eq Task (job_task x) (job_task j)))).
  - exact (ct_bool_canonical false).
Qed.

Theorem JLFPInstantiation_interference_correspondence :
  CjiIntRel Job (@JLFPInstantiation.interference Job sR hR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_interference Job dJ sL hL).
Proof.
  intros j tR tL Ht.
  exact (ct_bool_or _ _ _ _ (cji_LBI_is_priority_inversion Job sR sL Hs hR hL Hh j tR tL Ht)
           (JLFPInstantiation_is_interference_from_another_job_with_higher_eq_priority_correspondence j tR tL Ht)).
Qed.

Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CjiParRel Job cR cL.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CjiArrRel Job aR aL.

Theorem JLFPInstantiation_interfering_workload_of_jobs_with_hep_priority_correspondence j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (@JLFPInstantiation.interfering_workload_of_jobs_with_hep_priority Job cR aR hR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_interfering_workload_of_jobs_with_hep_priority Job dJ cL aL hL j tL).
Proof.
  exact (cji_sum_filtered_rel Job cR cL Hc _ _ (fun x => ct_bool_and _ _ _ _ (Hh x j) (ct_bool_not _ _ (ct_decide_eq Job x j)))
           _ _ (Ha tR tL Ht)).
Qed.

Theorem JLFPInstantiation_interfering_workload_correspondence :
  CjiWlRel Job (@JLFPInstantiation.interfering_workload Job cR aR sR hR) (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_interfering_workload Job dJ cL aL sL hL).
Proof.
  intros j tR tL Ht.
  exact (sub_add_correspondence _ _ _ _ (ct_bool_to_nat _ _ (cji_LBI_is_priority_inversion Job sR sL Hs hR hL Hh j tR tL Ht))
           (JLFPInstantiation_interfering_workload_of_jobs_with_hep_priority_correspondence j tR tL Ht)).
Qed.

End Defs.

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
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CjiParRel _ f g |- _ => exact (H x) end
  | |- CtBoolRel (?f ?x ?y) (?g ?x ?y) => match goal with H : CjiRelRel _ f g |- _ => exact (H x y) end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | ArrivalSequence.arrival_sequence _ => apply: (cji_forall_arr _); intros ? ? ?
  | UniprocessorSchedule.schedule _ => apply: (cji_forall_sched _); intros ? ? ?
  | Priority.JLFP_policy _ => apply: (cji_forall_rel _); intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: cji_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp
  | lazymatch goal with
    | |- forall _, _ => intro; crel
    | |- CjiIntRel _ (JLFPInstantiation.interference _ _) _ => eapply JLFPInstantiation_interference_correspondence; crel
    | |- CjiWlRel _ (JLFPInstantiation.interfering_workload _ _ _ _) _ => eapply JLFPInstantiation_interfering_workload_correspondence; crel
    | |- CjiFunRel _ _ => intros ? ? ?; cbv beta; crel
    | |- CjiPredRel _ _ _ => intro; cbv beta; crel
    | |- CjiParRel _ (fun _ => _) _ => intro; cbv beta; crel
    | |- SubNatRel ?a _ => crel_n a
    | |- CtBoolRel ?b _ => crel_b b
    | |- ClListRel _ ?l _ => crel_l l
    | |- PropSPropRel ?P _ => crel_p P
    end ]
with crel_n a :=
  lazymatch a with
  | addn _ _ => eapply sub_add_correspondence; crel
  | subn _ _ => eapply ct_sub_rel; crel
  | S _ => eapply cji_succ_rel; crel
  | _ => first [ exact (sub_nat_rel_canonical _) | crel_n_defs ]
  end
with crel_b b :=
  lazymatch b with
  | andb _ _ => eapply ct_bool_and; crel
  | negb _ => eapply ct_bool_not; crel
  | leq _ _ => first [ eapply ct_decide_lt; crel | eapply ct_decide_le; crel ]
  | @eq_op ?T _ _ => first [ fail; crel | eapply ct_decide_eq; crel ]
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
  | _ <-> _ => eapply cji_iff; crel
  | _ <> _ => eapply cji_ne
  | ~ _ => eapply ct_imp; [crel | exact cji_false_rel]
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else crel_eq_defs
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_eq_defs := first [ eapply ct_eq_rel | fail; crel ]
with crel_n_defs := first [ eapply cji_ico; crel
    | eapply ct_bool_to_nat; crel
    | eapply cji_ARD_cumul_interference; crel
    | eapply cji_ARD_cumul_interfering_workload; crel
    | eapply cji_SEQ_cumul_task_interference; crel
    | eapply cji_SV_service_of_jobs; crel
    | eapply cji_WL_workload_of_jobs; crel
    | eapply JLFPInstantiation_interfering_workload_of_jobs_with_hep_priority_correspondence; crel
    | eapply cji_US_service; crel
    | eapply cji_US_service_during; crel
    | eapply cji_US_service_at; crel ]
with crel_b_defs := first [ eapply cji_SEQ_task_interference_received_before; crel
    | eapply JLFPInstantiation_is_interference_from_another_job_with_higher_eq_priority_correspondence; crel
    | eapply JLFPInstantiation_is_interference_from_another_task_with_higher_eq_priority_correspondence; crel
    | eapply cji_LBI_is_priority_inversion; crel
    | eapply cji_US_completed_by; crel
    | eapply cji_US_scheduled_at; crel
    | eapply ct_bool_or; crel
    | eapply cji_US_pending_earlier_and_at; crel
    | eapply cji_has_arrived; crel
    | eapply cji_arrived_before; crel
    | eapply cji_arrives_at; crel
    | eapply cji_J_job_cost_positive; crel
    | eapply cji_TA_is_job_of_task; crel ]
with crel_l_defs := first [ eapply cji_jobs_arrived_before; crel
    | eapply cji_jobs_arrived_between; crel
    | eapply cji_arriving_at; crel ]
with crel_p_defs := first [ eapply cji_arrives_in; crel
    | eapply cji_consistent; crel
    | eapply cji_is_a_set; crel
    | eapply cji_mem; crel
    | eapply cji_US_jobs_come_from_arrival_sequence; crel
    | eapply cji_US_jobs_must_arrive_to_execute; crel
    | eapply cji_US_completed_jobs_dont_execute; crel
    | eapply cji_US_sequential_jobs; crel
    | eapply cji_PR_JLFP_is_reflexive; crel
    | eapply cji_PR_JLFP_respects_sequential_jobs; crel
    | eapply cji_LBI_quiet_time; crel
    | eapply cji_LBI_busy_interval; crel
    | eapply cji_ARD_quiet_time; crel
    | eapply cji_ARD_busy_interval; crel
    | eapply cji_uniq; crel ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_cumulative_interference_split (Job : eqType) : Prop :=
  ltac:(type_of_term (@JLFPInstantiation.cumulative_interference_split Job)).
Definition tgt_cumulative_interference_split (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_cumulative_interference_split Job (ct_decidable_eq Job))).
Theorem JLFPInstantiation_cumulative_interference_split_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_interference_split Job) (tgt_cumulative_interference_split Job).
Proof. unfold src_cumulative_interference_split, tgt_cumulative_interference_split. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_cumulative_task_interference_split (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JLFPInstantiation.cumulative_task_interference_split Task Job)).
Definition tgt_cumulative_task_interference_split (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_cumulative_task_interference_split Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JLFPInstantiation_cumulative_task_interference_split_correspondence (Task Job : eqType) :
  PropSPropRel (src_cumulative_task_interference_split Task Job) (tgt_cumulative_task_interference_split Task Job).
Proof. unfold src_cumulative_task_interference_split, tgt_cumulative_task_interference_split. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs (Job : eqType) : Prop :=
  ltac:(type_of_term (@JLFPInstantiation.instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs Job)).
Definition tgt_instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs Job (ct_decidable_eq Job))).
Theorem JLFPInstantiation_instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs_correspondence (Job : eqType) :
  PropSPropRel (src_instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs Job) (tgt_instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs Job).
Proof. unfold src_instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs, tgt_instantiated_cumulative_workload_of_hep_jobs_equal_total_workload_of_hep_jobs. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs (Job : eqType) : Prop :=
  ltac:(type_of_term (@JLFPInstantiation.instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs Job)).
Definition tgt_instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs Job (ct_decidable_eq Job))).
Theorem JLFPInstantiation_instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs_correspondence (Job : eqType) :
  PropSPropRel (src_instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs Job) (tgt_instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs Job).
Proof. unfold src_instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs, tgt_instantiated_cumulative_interference_of_hep_jobs_equal_total_interference_of_hep_jobs. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JLFPInstantiation.instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks Task Job)).
Definition tgt_instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JLFPInstantiation_instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks_correspondence (Task Job : eqType) :
  PropSPropRel (src_instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks Task Job) (tgt_instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks Task Job).
Proof. unfold src_instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks, tgt_instantiated_cumulative_interference_of_hep_tasks_equal_total_interference_of_hep_tasks. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_instantiated_quiet_time_equivalent_edf_quiet_time (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JLFPInstantiation.instantiated_quiet_time_equivalent_edf_quiet_time Task Job)).
Definition tgt_instantiated_quiet_time_equivalent_edf_quiet_time (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_instantiated_quiet_time_equivalent_edf_quiet_time Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JLFPInstantiation_instantiated_quiet_time_equivalent_edf_quiet_time_correspondence (Task Job : eqType) :
  PropSPropRel (src_instantiated_quiet_time_equivalent_edf_quiet_time Task Job) (tgt_instantiated_quiet_time_equivalent_edf_quiet_time Task Job).
Proof. unfold src_instantiated_quiet_time_equivalent_edf_quiet_time, tgt_instantiated_quiet_time_equivalent_edf_quiet_time. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_instantiated_busy_interval_equivalent_edf_busy_interval (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JLFPInstantiation.instantiated_busy_interval_equivalent_edf_busy_interval Task Job)).
Definition tgt_instantiated_busy_interval_equivalent_edf_busy_interval (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Limited_JlfpInstantiation_JLFPInstantiation_instantiated_busy_interval_equivalent_edf_busy_interval Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JLFPInstantiation_instantiated_busy_interval_equivalent_edf_busy_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_instantiated_busy_interval_equivalent_edf_busy_interval Task Job) (tgt_instantiated_busy_interval_equivalent_edf_busy_interval Task Job).
Proof. unfold src_instantiated_busy_interval_equivalent_edf_busy_interval, tgt_instantiated_busy_interval_equivalent_edf_busy_interval. crel_spine. crel. Unshelve. all: crel. Qed.
