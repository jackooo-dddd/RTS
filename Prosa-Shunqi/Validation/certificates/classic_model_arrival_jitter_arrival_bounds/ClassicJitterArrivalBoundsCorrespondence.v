From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path bigop div.
From prosa Require Import classic.util.div_mod classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.task_arrival classic.model.arrival.jitter.arrival_sequence classic.model.arrival.jitter.job classic.model.arrival.jitter.task_arrival classic.model.arrival.jitter.arrival_bounds.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicJitterArrivalBounds.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicJitterArrivalBoundsBase ClassicJitterArrivalBoundsList.

Module I := ImportedClassicJitterArrivalBounds.
Local Open Scope nat_scope.

(** Certificates for [classic/model/arrival/jitter/arrival_bounds.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job/task parameters
    pointwise through [SubNatRel]; arrival sequences pointwise on related times; all with two-way totals.  The imported
    arrival-sequence, task-arrival and jitter definitions are related as in the accepted classic certificates (re-bound
    below, through the kernel-checked [bigCat_range'], [mergeSort_isChain] / [mergeSort_filter_class] and
    [DivModInterface] equations of the interface).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used).  Where the binder lists put task parameters before the job type, the job type is fixed as an
    [eqType] with its canonical Lean instance and the task parameters stay universally quantified on both sides. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cav_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cav_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cav_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cav_false_rel). Qed.

Lemma cav_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cav_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cav_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cav_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cav_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cav_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cav_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cav_unmap_rel T l) PR PL).
Qed.

Definition CavParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cav_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CavParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cav_forall_cover _ _ (CavParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cav_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cav_natl s') end.

Definition cav_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cav_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cav_one) (cav_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cav_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cav_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cav_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cav_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cav_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cav_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cav_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cav_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cav_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cav_cl_append. reflexivity.
Qed.

Lemma cav_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CavFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cav_bigcat_rel (A : Type) fR fL (Hf : CavFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterArrivalBoundsInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cav_iota_range (nR - mR) 0) cav_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cav_cl_map_ext _ _ Hpt) (cav_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cav_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cav_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CavArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cav_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cav_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cav_arr_canonical aR : CavArrRel aR (cav_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cav_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cav_arr_surjective aL : CavArrRel (cav_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cav_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CavArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cav_forall_cover _ _ CavArrRel cav_arr_to_target cav_arr_to_source cav_arr_canonical cav_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cav_jobs_arrived_between aR aL (Ha : CavArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cav_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cav_arrives_in aR aL (Ha : CavArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cav_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cav_consistent pR pL (Hp : CavParRel Job pR pL) aR aL (Ha : CavArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cav_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cav_is_a_set aR aL (Ha : CavArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cav_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cav_jobs_arrived_before aR aL (Ha : CavArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job dJ aL tL).
Proof. exact (cav_jobs_arrived_between Job aR aL Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma cav_arrives_at aR aL (Ha : CavArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cav_mem Job j _ _ (Ha tR tL Ht))). Qed.

End ArrivalDefs2.

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cav_TA_sporadic_task_model tpR tpL (Htp : CavParRel Task tpR tpL)
    jaR jaL (Hja : CavParRel Job jaR jaL) (job_task : Job -> Task) aR aL (Ha : CavArrRel Job aR aL) :
  PropSPropRel (TaskArrival.sporadic_task_model tpR jaR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model Task dT tpL Job dJ jaL job_task aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'.
  apply: ct_imp; first exact (cav_ne Job j j').
  apply: ct_imp; first exact (cav_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cav_arrives_in Job aR aL Ha j').
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j')).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htp (job_task j))) (Hja j')).
Qed.

Lemma cav_TA_is_job_of_task (job_task : Job -> Task) tsk j :
  CtBoolRel (TaskArrival.is_job_of_task job_task tsk j)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk j).
Proof. exact (ct_decide_eq Task (job_task j) tsk). Qed.

End TaskArrivalDefs.

(** The imported [ArrivalSequenceWithJitter] definitions (as in the accepted classic jitter arrival_sequence certificate). *)
Section JitterArrDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cav_AJ_actual_arrival pR pL (Hp : CavParRel Job pR pL) qR qL (Hq : CavParRel Job qR qL) j :
  SubNatRel (ArrivalSequenceWithJitter.actual_arrival pR qR j) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Hp j) (Hq j)). Qed.

Lemma cav_AJ_actual_arrivals_between pR pL (Hp : CavParRel Job pR pL) qR qL (Hq : CavParRel Job qR qL)
    aR aL (Ha : CavArrRel Job aR aL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_between pR qR aR t1R t2R) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_between Job dJ pL qL aL t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cav_jobs_arrived_before Job aR aL Ha t2R t2L H2).
  have F := cl_filter cid _
              (fun j => I.Bool_and
                 (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j))
                    (I.Nat_decLe t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j)))
                 (I.Decidable_decide (I.LT_lt_inst1 Lean.Nat I.instLTNat (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)
                    (I.Nat_decLt (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)))
              (fun j => ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (cav_AJ_actual_arrival pR pL Hp qR qL Hq j))
                                          (ct_decide_lt _ _ _ _ (cav_AJ_actual_arrival pR pL Hp qR qL Hq j) H2))
              (ArrivalSequence.jobs_arrived_before aR t2R).
  rewrite -E in F. exact F.
Qed.

End JitterArrDefs.

(* ------------------------------------------------------------------ *)
(** * Stable sorting: MathComp [sort] against the core [List.mergeSort] *)

Section SortUniq.
Variables (T : eqType) (f : T -> nat).
Notation leT := (fun a b : T => f a <= f b).
Notation cls x := (fun y : T => f y == f x).

Lemma cav_leT_trans : transitive leT.
Proof. move=> y x z. exact: leq_trans. Qed.

Lemma cav_leT_total : total leT.
Proof. move=> a b. exact: leq_total. Qed.

Lemma cav_class_sorted x : forall l : seq T, all (cls x) l -> sorted leT l.
Proof.
  case => [|a l] //= /andP [Ha Hl]. elim: l a Ha Hl => [|b l IH] a Ha //= /andP [Hb Hl].
  rewrite (eqP Ha) (eqP Hb) leqnn /=. exact: IH.
Qed.

Lemma cav_sort_filter_class s x : filter (cls x) (sort leT s) = filter (cls x) s.
Proof.
  rewrite (filter_sort cav_leT_total cav_leT_trans).
  apply: (sorted_sort cav_leT_trans). apply: cav_class_sorted. exact: filter_all.
Qed.

Lemma cav_sorted_class_uniq : forall u t : seq T, sorted leT u -> sorted leT t ->
  (forall x, filter (cls x) u = filter (cls x) t) -> u = t.
Proof.
  elim => [|a u IH] t Su St H.
  { case: t St H => [//|b t] St H. by have := H b; rewrite /= eqxx. }
  case: t St H => [|b t] St H; first by have := H a; rewrite /= eqxx.
  have Ma : all (leT a) u := order_path_min cav_leT_trans Su.
  have Mb : all (leT b) t := order_path_min cav_leT_trans St.
  have Hba : f b <= f a.
  { have : a \in filter (cls a) (b :: t) by rewrite -H /= eqxx mem_head.
    rewrite mem_filter => /andP [_]. rewrite in_cons => /orP [/eqP -> //|Ht].
    exact: (allP Mb). }
  have Hab : f a <= f b.
  { have : b \in filter (cls b) (a :: u) by rewrite H /= eqxx mem_head.
    rewrite mem_filter => /andP [_]. rewrite in_cons => /orP [/eqP -> //|Hu].
    exact: (allP Ma). }
  have Eab : f b == f a by rewrite eqn_leq Hab Hba.
  have Hhead := H a. rewrite /= eqxx Eab in Hhead. case: Hhead => Eh Et.
  subst b. congr cons. apply: IH.
  - exact: path_sorted Su.
  - exact: path_sorted St.
  - move=> x. have := H x. rewrite /=. by case: (f a == f x) => // [[]].
Qed.

Lemma cav_sort_unique (u s : seq T) : sorted leT u -> (forall x, filter (cls x) u = filter (cls x) s) -> u = sort leT s.
Proof.
  move=> Su H. apply: cav_sorted_class_uniq => //.
  - exact: (sort_sorted cav_leT_total).
  - move=> x. by rewrite cav_sort_filter_class H.
Qed.

End SortUniq.

Section Chain.
Variables (T : Type) (leR : T -> T -> bool) (leL : T -> T -> I.Bool).
Hypothesis HR : forall a b, CtBoolRel (leR a b) (leL a b).
Notation RL := (fun a b : T => Lean.eq (leL a b) I.Bool_true).

Inductive CavTrue : SProp := cav_true_intro.

Definition cav_chain_head (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) : RL x y :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons a (I.List_cons b _) => RL a b | _ => CavTrue end) with
  | I.List_IsChain_nil => cav_true_intro
  | I.List_IsChain_singleton _ => cav_true_intro
  | I.List_IsChain_cons_cons a b l h _ => h
  end.

Definition cav_chain_tail (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) :
    I.List_IsChain T RL (I.List_cons T y l) :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons _ (I.List_cons b l') => I.List_IsChain T RL (I.List_cons T b l') | _ => CavTrue end) with
  | I.List_IsChain_nil => cav_true_intro
  | I.List_IsChain_singleton _ => cav_true_intro
  | I.List_IsChain_cons_cons a b l _ t => t
  end.

Fixpoint cav_path_backward (x : T) (s : seq T) : I.List_IsChain T RL (I.List_cons T x (cl_map cid s)) -> StrictlyInhabited (path leR x s) :=
  match s as s0 return I.List_IsChain T RL (I.List_cons T x (cl_map cid s0)) -> StrictlyInhabited (path leR x s0) with
  | [::] => fun _ => strictly_inhabits (Logic.eq_refl true)
  | y :: s' => fun H =>
      match cav_path_backward y s' (cav_chain_tail x y _ H) with
      | strictly_inhabits Hp =>
          strictly_inhabits (introT andP (conj (sprop_to_prop _ _ (ct_bool_truth _ _ (HR x y)) (cav_chain_head x y _ H)) Hp))
      end
  end.

Lemma cav_sorted_backward s : I.List_IsChain T RL (cl_map cid s) -> StrictlyInhabited (sorted leR s).
Proof.
  destruct s as [|x s].
  - intros _. exact (strictly_inhabits (Logic.eq_refl true)).
  - exact (cav_path_backward x s).
Qed.

End Chain.

Section Sort.
Variables (T : eqType) (f : T -> nat) (fL : T -> Lean.Nat).
Hypothesis Hf : forall x, SubNatRel (f x) (fL x).
Notation leL := (fun j j' : T => I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat (fL j) (fL j')) (I.Nat_decLe (fL j) (fL j'))).
Notation clsL x := (fun y : T => I.Decidable_decide (Lean.eq (fL y) (fL x)) (I.instDecidableEqNat (fL y) (fL x))).

Lemma cav_sort_rel s sL : ClListRel cid s sL ->
  ClListRel cid (sort (fun j j' => f j <= f j') s) (I.List_mergeSort T sL leL).
Proof.
  intro Hs.
  pose m := I.List_mergeSort T sL leL. pose u := cl_unmap cid m.
  have Hu : ClListRel cid u m := cav_unmap_rel T m.
  have Su : sorted (fun a b => f a <= f b) u :=
    interpret_strict _
      (cav_sorted_backward T (fun a b => f a <= f b) leL (fun a b => ct_decide_le _ _ _ _ (Hf a) (Hf b)) u
         (match Hu in Lean.eq _ z
                return I.List_IsChain T (fun a b => Lean.eq (leL a b) I.Bool_true) z ->
                       I.List_IsChain T (fun a b => Lean.eq (leL a b) I.Bool_true) (cl_map cid u) with
          | Lean.eq_refl => fun h => h
          end (I.Prosa_Validation_ClassicJitterArrivalBoundsInterface_mergeSort_isChain T fL sL))).
  have Fu : forall x, filter (fun y => f y == f x) u = filter (fun y => f y == f x) s.
  { intro x. apply: cav_cl_map_inj.
    have Hp : forall y, CtBoolRel (f y == f x) (clsL x y) := fun y => ct_decide_eq_nat _ _ _ _ (Hf y) (Hf x).
    refine (Logic.eq_trans (cl_filter cid (fun y => f y == f x) (clsL x) Hp u)
              (Logic.eq_trans _ (Logic.eq_sym (cl_filter cid (fun y => f y == f x) (clsL x) Hp s)))).
    refine (Logic.eq_trans (f_equal (I.List_filter T (clsL x)) (Logic.eq_sym (cl_list_logic _ _ _ Hu)))
              (Logic.eq_trans _ (f_equal (I.List_filter T (clsL x)) (cl_list_logic _ _ _ Hs)))).
    exact (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterArrivalBoundsInterface_mergeSort_filter_class T fL x sL)). }
  have E := cav_sort_unique T f u s Su Fu.
  apply: coq_eq_to_imported_eq. rewrite -E. exact (Logic.eq_sym (cl_list_logic _ _ _ Hu)).
Qed.

End Sort.

Lemma cav_getD (T : Type) (s : seq T) sL (Hs : ClListRel cid s sL) (x0 : T) nR nL (Hn : SubNatRel nR nL) :
  Logic.eq (I.List_getD T sL nL x0) (nth x0 s nR).
Proof.
  rewrite (cl_list_logic _ _ _ Hs) (cl_nat_logic _ _ Hn). exact (Logic.eq_sym (cl_nth cid x0 s nR)).
Qed.

Lemma cav_pred_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ct_sub nL (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Hn. apply: coq_eq_to_imported_eq. rewrite -subn1.
  exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1))).
Qed.

Section JtarrDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cav_JT_is_job_of_tsk (job_task : Job -> Task) tsk j :
  CtBoolRel (TaskArrivalWithJitter.is_job_of_tsk job_task tsk j) (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_is_job_of_tsk Task dT Job dJ job_task tsk j).
Proof. exact (cav_TA_is_job_of_task Task Job job_task tsk j). Qed.

Lemma cav_JT_actual_arrivals_of_task_between jaR jaL (Hja : CavParRel Job jaR jaL)
    jjR jjL (Hjj : CavParRel Job jjR jjL) (job_task : Job -> Task) aR aL (Ha : CavArrRel Job aR aL) tsk
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  ClListRel cid (TaskArrivalWithJitter.actual_arrivals_of_task_between jaR jjR job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_actual_arrivals_of_task_between Task dT Job dJ jaL jjL job_task aL tsk t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans (cl_filter cid _ (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_is_job_of_tsk Task dT Job dJ job_task tsk)
                            (cav_JT_is_job_of_tsk job_task tsk) _) _).
  exact (f_equal (I.List_filter Job (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_is_job_of_tsk Task dT Job dJ job_task tsk))
           (Logic.eq_sym (cl_list_logic _ _ _ (cav_AJ_actual_arrivals_between Job jaR jaL Hja jjR jjL Hjj aR aL Ha _ _ H1 _ _ H2)))).
Qed.

Lemma cav_JT_num_actual_arrivals_of_task jaR jaL (Hja : CavParRel Job jaR jaL)
    jjR jjL (Hjj : CavParRel Job jjR jjL) (job_task : Job -> Task) aR aL (Ha : CavArrRel Job aR aL) tsk
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (TaskArrivalWithJitter.num_actual_arrivals_of_task jaR jjR job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_num_actual_arrivals_of_task Task dT Job dJ jaL jjL job_task aL tsk t1L t2L).
Proof.
  have H := cav_JT_actual_arrivals_of_task_between jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2.
  change (SubNatRel (size (TaskArrivalWithJitter.actual_arrivals_of_task_between jaR jjR job_task aR tsk t1R t2R))
    (I.List_length Job (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_actual_arrivals_of_task_between Task dT Job dJ jaL jjL job_task aL tsk t1L t2L))).
  exact (match H in Lean.eq _ z
               return SubNatRel (size (TaskArrivalWithJitter.actual_arrivals_of_task_between jaR jjR job_task aR tsk t1R t2R)) (I.List_length Job z) with
         | Lean.eq_refl => cl_size cid _
         end).
Qed.

Lemma cav_sorted_rel jaR jaL (Hja : CavParRel Job jaR jaL) jjR jjL (Hjj : CavParRel Job jjR jjL) (job_task : Job -> Task)
    aR aL (Ha : CavArrRel Job aR aL) tsk t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  ClListRel cid (sort (fun j j' => jaR j <= jaR j') (TaskArrivalWithJitter.actual_arrivals_of_task_between jaR jjR job_task aR tsk t1R t2R))
    (I.List_mergeSort Job (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_actual_arrivals_of_task_between Task dT Job dJ jaL jjL job_task aL tsk t1L t2L)
       (fun j j' => I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat (jaL j) (jaL j')) (I.Nat_decLe (jaL j) (jaL j')))).
Proof.
  exact (cav_sort_rel Job jaR jaL Hja _ _
           (cav_JT_actual_arrivals_of_task_between jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2)).
Qed.

End JtarrDefs.

Section JjobDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cav_JJ_job_jitter_leq_task_jitter tjR tjL (Htj : CavParRel Task tjR tjL)
    jjR jjL (Hjj : CavParRel Job jjR jjL) (job_task : Job -> Task) j :
  CtBoolRel (JobWithJitter.job_jitter_leq_task_jitter tjR jjR job_task j)
    (I.Prosa_Classic_Model_Arrival_Jitter_Job_JobWithJitter_job_jitter_leq_task_jitter Task dT tjL Job dJ jjL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hjj j) (Htj (job_task j))). Qed.

End JjobDefs.

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
(** * Statements *)

Definition src_sporadic_arrival_bound_no_jobs (Task Job : eqType) : Prop :=
  forall task_period task_jitter : Task -> Time.time, ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_no_jobs Task task_period task_jitter Job)).
Definition tgt_sporadic_arrival_bound_no_jobs (Task Job : eqType) : SProp :=
  forall task_period task_jitter : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_no_jobs Task (ct_decidable_eq Task) task_period task_jitter Job (ct_decidable_eq Job))).

Theorem ArrivalBounds_sporadic_arrival_bound_no_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_no_jobs Task Job) (tgt_sporadic_arrival_bound_no_jobs Task Job).
Proof.
  unfold src_sporadic_arrival_bound_no_jobs, tgt_sporadic_arrival_bound_no_jobs.
  apply: cav_forall_par => tpR tpL Htp. apply: cav_forall_par => tjR tjL Htj.
  apply: cav_forall_par => aR aL Ha. apply: cav_forall_par => jjR jjL Hjj. apply: ct_forall_identity => job_task.
  apply: cav_forall_arr => arrR arrL Harr.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := cav_JT_num_actual_arrivals_of_task Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ Hn (sub_nat_rel_canonical 0)).
  exact (sub_nat_le_correspondence _ _ _ _ Hn (dm_div_ceil_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ H2 (Htj tsk)) H1) (Htp tsk))).
Qed.
Definition src_sporadic_arrival_bound_more_than_one_point (Task Job : eqType) : Prop :=
   ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_more_than_one_point Task  Job)).
Definition tgt_sporadic_arrival_bound_more_than_one_point (Task Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_more_than_one_point Task (ct_decidable_eq Task)  Job (ct_decidable_eq Job))).

Theorem ArrivalBounds_sporadic_arrival_bound_more_than_one_point_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_more_than_one_point Task Job) (tgt_sporadic_arrival_bound_more_than_one_point Task Job).
Proof.
  unfold src_sporadic_arrival_bound_more_than_one_point, tgt_sporadic_arrival_bound_more_than_one_point.
  apply: cav_forall_par => aR aL Ha. apply: cav_forall_par => jjR jjL Hjj. apply: ct_forall_identity => job_task.
  apply: cav_forall_arr => arrR arrL Harr.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := cav_JT_num_actual_arrivals_of_task Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hn).
  exact (sub_nat_lt_correspondence _ _ _ _ H1 H2).
Qed.
Definition src_sporadic_arrival_bound_one_job (Task Job : eqType) : Prop :=
  forall task_period task_jitter : Task -> Time.time, ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_one_job Task task_period task_jitter Job)).
Definition tgt_sporadic_arrival_bound_one_job (Task Job : eqType) : SProp :=
  forall task_period task_jitter : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_one_job Task (ct_decidable_eq Task) task_period task_jitter Job (ct_decidable_eq Job))).

Theorem ArrivalBounds_sporadic_arrival_bound_one_job_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_one_job Task Job) (tgt_sporadic_arrival_bound_one_job Task Job).
Proof.
  unfold src_sporadic_arrival_bound_one_job, tgt_sporadic_arrival_bound_one_job.
  apply: cav_forall_par => tpR tpL Htp. apply: cav_forall_par => tjR tjL Htj.
  apply: cav_forall_par => aR aL Ha. apply: cav_forall_par => jjR jjL Hjj. apply: ct_forall_identity => job_task.
  apply: cav_forall_arr => arrR arrL Harr.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := cav_JT_num_actual_arrivals_of_task Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp tsk)).
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ Hn (sub_nat_rel_canonical 1)).
  exact (sub_nat_le_correspondence _ _ _ _ Hn (dm_div_ceil_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ H2 (Htj tsk)) H1) (Htp tsk))).
Qed.
Definition src_sporadic_arrival_bound_properties_of_nth (Task Job : eqType) : Prop :=
   ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_properties_of_nth Task  Job)).
Definition tgt_sporadic_arrival_bound_properties_of_nth (Task Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_properties_of_nth Task (ct_decidable_eq Task)  Job (ct_decidable_eq Job))).

Theorem ArrivalBounds_sporadic_arrival_bound_properties_of_nth_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_properties_of_nth Task Job) (tgt_sporadic_arrival_bound_properties_of_nth Task Job).
Proof.
  unfold src_sporadic_arrival_bound_properties_of_nth, tgt_sporadic_arrival_bound_properties_of_nth.
  apply: cav_forall_par => aR aL Ha. apply: cav_forall_par => jjR jjL Hjj. apply: ct_forall_identity => job_task.
  apply: cav_forall_arr => arrR arrL Harr.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := cav_JT_num_actual_arrivals_of_task Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  apply: ct_forall_identity => elem.
  have Hs := cav_sorted_rel Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  apply: ct_forall_nat => iR iL Hi.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hi Hn).
  rewrite (cav_getD _ _ _ Hs elem _ _ Hi).
  set x := nth elem _ iR.
  have Hx := cav_AJ_actual_arrival Job aR aL Ha jjR jjL Hjj x.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Hx) (ct_decide_lt _ _ _ _ Hx H2))).
  apply: ct_and; first exact (ct_eq_rel Task (job_task x) tsk).
  exact (cav_arrives_in Job arrR arrL Harr x).
Qed.
Definition src_sporadic_arrival_bound_distance_between_first_and_last (Task Job : eqType) : Prop :=
  forall task_period : Task -> Time.time, ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_distance_between_first_and_last Task task_period Job)).
Definition tgt_sporadic_arrival_bound_distance_between_first_and_last (Task Job : eqType) : SProp :=
  forall task_period : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_distance_between_first_and_last Task (ct_decidable_eq Task) task_period Job (ct_decidable_eq Job))).

Theorem ArrivalBounds_sporadic_arrival_bound_distance_between_first_and_last_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_distance_between_first_and_last Task Job) (tgt_sporadic_arrival_bound_distance_between_first_and_last Task Job).
Proof.
  unfold src_sporadic_arrival_bound_distance_between_first_and_last, tgt_sporadic_arrival_bound_distance_between_first_and_last.
  apply: cav_forall_par => tpR tpL Htp.
  apply: cav_forall_par => aR aL Ha. apply: cav_forall_par => jjR jjL Hjj. apply: ct_forall_identity => job_task.
  apply: cav_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (cav_consistent Job aR aL Ha arrR arrL Harr).
  apply: ct_imp; first exact (cav_is_a_set Job arrR arrL Harr).
  apply: ct_imp; first exact (cav_TA_sporadic_task_model Task Job tpR tpL Htp aR aL Ha job_task arrR arrL Harr).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := cav_JT_num_actual_arrivals_of_task Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical 2) Hn).
  apply: ct_forall_identity => elem.
  have Hs := cav_sorted_rel Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  rewrite (cav_getD _ _ _ Hs elem _ _ (sub_nat_rel_canonical 0)) (cav_getD _ _ _ Hs elem _ _ (cav_pred_rel _ _ Hn)).
  exact (sub_nat_le_correspondence _ _ _ _
           (sub_add_correspondence _ _ _ _ (Ha _) (sub_mul_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1)) (Htp tsk))) (Ha _)).
Qed.
Definition src_sporadic_arrival_bound_last_job_too_far (Task Job : eqType) : Prop :=
  forall task_period task_jitter : Task -> Time.time, ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_last_job_too_far Task task_period task_jitter Job)).
Definition tgt_sporadic_arrival_bound_last_job_too_far (Task Job : eqType) : SProp :=
  forall task_period task_jitter : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_last_job_too_far Task (ct_decidable_eq Task) task_period task_jitter Job (ct_decidable_eq Job))).

Theorem ArrivalBounds_sporadic_arrival_bound_last_job_too_far_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_last_job_too_far Task Job) (tgt_sporadic_arrival_bound_last_job_too_far Task Job).
Proof.
  unfold src_sporadic_arrival_bound_last_job_too_far, tgt_sporadic_arrival_bound_last_job_too_far.
  apply: cav_forall_par => tpR tpL Htp. apply: cav_forall_par => tjR tjL Htj.
  apply: cav_forall_par => aR aL Ha. apply: cav_forall_par => jjR jjL Hjj. apply: ct_forall_identity => job_task.
  apply: cav_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (cav_consistent Job aR aL Ha arrR arrL Harr).
  apply: ct_imp; first exact (cav_is_a_set Job arrR arrL Harr).
  apply: ct_imp; first exact (cav_TA_sporadic_task_model Task Job tpR tpL Htp aR aL Ha job_task arrR arrL Harr).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := cav_JT_num_actual_arrivals_of_task Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp tsk)).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical 2) Hn).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (dm_div_ceil_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ H2 (Htj tsk)) H1) (Htp tsk)) Hn).
  apply: ct_forall_identity => elem.
  have Hs := cav_sorted_rel Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  rewrite (cav_getD _ _ _ Hs elem _ _ (sub_nat_rel_canonical 0)) (cav_getD _ _ _ Hs elem _ _ (cav_pred_rel _ _ Hn)).
  exact (sub_nat_le_correspondence _ _ _ _
           (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Ha _) H2) (Htj tsk)) H1) (Ha _)).
Qed.
Definition src_sporadic_arrival_bound_last_arrives_too_late (Task Job : eqType) : Prop :=
  forall task_period task_jitter : Task -> Time.time, ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_last_arrives_too_late Task task_period task_jitter Job)).
Definition tgt_sporadic_arrival_bound_last_arrives_too_late (Task Job : eqType) : SProp :=
  forall task_period task_jitter : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_last_arrives_too_late Task (ct_decidable_eq Task) task_period task_jitter Job (ct_decidable_eq Job))).

Theorem ArrivalBounds_sporadic_arrival_bound_last_arrives_too_late_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_last_arrives_too_late Task Job) (tgt_sporadic_arrival_bound_last_arrives_too_late Task Job).
Proof.
  unfold src_sporadic_arrival_bound_last_arrives_too_late, tgt_sporadic_arrival_bound_last_arrives_too_late.
  apply: cav_forall_par => tpR tpL Htp. apply: cav_forall_par => tjR tjL Htj.
  apply: cav_forall_par => aR aL Ha. apply: cav_forall_par => jjR jjL Hjj. apply: ct_forall_identity => job_task.
  apply: cav_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (cav_consistent Job aR aL Ha arrR arrL Harr).
  apply: ct_imp; first exact (cav_is_a_set Job arrR arrL Harr).
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cav_arrives_in Job arrR arrL Harr j).
    exact (ct_bool_truth _ _ (cav_JJ_job_jitter_leq_task_jitter Task Job tjR tjL Htj jjR jjL Hjj job_task j)). }
  apply: ct_imp; first exact (cav_TA_sporadic_task_model Task Job tpR tpL Htp aR aL Ha job_task arrR arrL Harr).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := cav_JT_num_actual_arrivals_of_task Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp tsk)).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical 2) Hn).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (dm_div_ceil_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ H2 (Htj tsk)) H1) (Htp tsk)) Hn).
  apply: ct_forall_identity => elem.
  have Hs := cav_sorted_rel Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  rewrite (cav_getD _ _ _ Hs elem _ _ (cav_pred_rel _ _ Hn)).
  exact (sub_nat_le_correspondence _ _ _ _ H2 (Ha _)).
Qed.
Definition src_sporadic_arrival_bound_case_3_contradiction (Task Job : eqType) : Prop :=
  forall task_period task_jitter : Task -> Time.time, ltac:(type_of_term (@ArrivalBounds.sporadic_arrival_bound_case_3_contradiction Task task_period task_jitter Job)).
Definition tgt_sporadic_arrival_bound_case_3_contradiction (Task Job : eqType) : SProp :=
  forall task_period task_jitter : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalBounds_ArrivalBounds_sporadic_arrival_bound_case_3_contradiction Task (ct_decidable_eq Task) task_period task_jitter Job (ct_decidable_eq Job))).

Theorem ArrivalBounds_sporadic_arrival_bound_case_3_contradiction_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_arrival_bound_case_3_contradiction Task Job) (tgt_sporadic_arrival_bound_case_3_contradiction Task Job).
Proof.
  unfold src_sporadic_arrival_bound_case_3_contradiction, tgt_sporadic_arrival_bound_case_3_contradiction.
  apply: cav_forall_par => tpR tpL Htp. apply: cav_forall_par => tjR tjL Htj.
  apply: cav_forall_par => aR aL Ha. apply: cav_forall_par => jjR jjL Hjj. apply: ct_forall_identity => job_task.
  apply: cav_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (cav_consistent Job aR aL Ha arrR arrL Harr).
  apply: ct_imp; first exact (cav_is_a_set Job arrR arrL Harr).
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cav_arrives_in Job arrR arrL Harr j).
    exact (ct_bool_truth _ _ (cav_JJ_job_jitter_leq_task_jitter Task Job tjR tjL Htj jjR jjL Hjj job_task j)). }
  apply: ct_imp; first exact (cav_TA_sporadic_task_model Task Job tpR tpL Htp aR aL Ha job_task arrR arrL Harr).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := cav_JT_num_actual_arrivals_of_task Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp tsk)).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical 2) Hn).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (dm_div_ceil_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ H2 (Htj tsk)) H1) (Htp tsk)) Hn).
  apply: ct_forall_identity => elem.
  exact cav_false_rel.
Qed.
Definition src_sporadic_task_arrival_bound_at_least_two_jobs (Task Job : eqType) : Prop :=
  forall task_period task_jitter : Task -> Time.time, ltac:(type_of_term (@ArrivalBounds.sporadic_task_arrival_bound_at_least_two_jobs Task task_period task_jitter Job)).
Definition tgt_sporadic_task_arrival_bound_at_least_two_jobs (Task Job : eqType) : SProp :=
  forall task_period task_jitter : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalBounds_ArrivalBounds_sporadic_task_arrival_bound_at_least_two_jobs Task (ct_decidable_eq Task) task_period task_jitter Job (ct_decidable_eq Job))).

Theorem ArrivalBounds_sporadic_task_arrival_bound_at_least_two_jobs_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_task_arrival_bound_at_least_two_jobs Task Job) (tgt_sporadic_task_arrival_bound_at_least_two_jobs Task Job).
Proof.
  unfold src_sporadic_task_arrival_bound_at_least_two_jobs, tgt_sporadic_task_arrival_bound_at_least_two_jobs.
  apply: cav_forall_par => tpR tpL Htp. apply: cav_forall_par => tjR tjL Htj.
  apply: cav_forall_par => aR aL Ha. apply: cav_forall_par => jjR jjL Hjj. apply: ct_forall_identity => job_task.
  apply: cav_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (cav_consistent Job aR aL Ha arrR arrL Harr).
  apply: ct_imp; first exact (cav_is_a_set Job arrR arrL Harr).
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cav_arrives_in Job arrR arrL Harr j).
    exact (ct_bool_truth _ _ (cav_JJ_job_jitter_leq_task_jitter Task Job tjR tjL Htj jjR jjL Hjj job_task j)). }
  apply: ct_imp; first exact (cav_TA_sporadic_task_model Task Job tpR tpL Htp aR aL Ha job_task arrR arrL Harr).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := cav_JT_num_actual_arrivals_of_task Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp tsk)).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical 2) Hn).
  exact (sub_nat_le_correspondence _ _ _ _ Hn (dm_div_ceil_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ H2 (Htj tsk)) H1) (Htp tsk))).
Qed.
Definition src_sporadic_task_with_jitter_arrival_bound (Task Job : eqType) : Prop :=
  forall task_period task_jitter : Task -> Time.time, ltac:(type_of_term (@ArrivalBounds.sporadic_task_with_jitter_arrival_bound Task task_period task_jitter Job)).
Definition tgt_sporadic_task_with_jitter_arrival_bound (Task Job : eqType) : SProp :=
  forall task_period task_jitter : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalBounds_ArrivalBounds_sporadic_task_with_jitter_arrival_bound Task (ct_decidable_eq Task) task_period task_jitter Job (ct_decidable_eq Job))).

Theorem ArrivalBounds_sporadic_task_with_jitter_arrival_bound_correspondence (Task Job : eqType) :
  PropSPropRel (src_sporadic_task_with_jitter_arrival_bound Task Job) (tgt_sporadic_task_with_jitter_arrival_bound Task Job).
Proof.
  unfold src_sporadic_task_with_jitter_arrival_bound, tgt_sporadic_task_with_jitter_arrival_bound.
  apply: cav_forall_par => tpR tpL Htp. apply: cav_forall_par => tjR tjL Htj.
  apply: cav_forall_par => aR aL Ha. apply: cav_forall_par => jjR jjL Hjj. apply: ct_forall_identity => job_task.
  apply: cav_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (cav_consistent Job aR aL Ha arrR arrL Harr).
  apply: ct_imp; first exact (cav_is_a_set Job arrR arrL Harr).
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_imp; first exact (cav_arrives_in Job arrR arrL Harr j).
    exact (ct_bool_truth _ _ (cav_JJ_job_jitter_leq_task_jitter Task Job tjR tjL Htj jjR jjL Hjj job_task j)). }
  apply: ct_imp; first exact (cav_TA_sporadic_task_model Task Job tpR tpL Htp aR aL Ha job_task arrR arrL Harr).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_identity => tsk.
  have Hn := cav_JT_num_actual_arrivals_of_task Task Job aR aL Ha jjR jjL Hjj job_task arrR arrL Harr tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Htp tsk)).
  exact (sub_nat_le_correspondence _ _ _ _ Hn (dm_div_ceil_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ H2 (Htj tsk)) H1) (Htp tsk))).
Qed.
