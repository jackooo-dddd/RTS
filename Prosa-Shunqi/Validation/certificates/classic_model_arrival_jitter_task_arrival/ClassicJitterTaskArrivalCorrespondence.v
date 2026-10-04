From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.task_arrival classic.model.arrival.jitter.arrival_sequence classic.model.arrival.jitter.task_arrival.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicJitterTaskArrival.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicJitterTaskArrivalBase ClassicJitterTaskArrivalList.

Module I := ImportedClassicJitterTaskArrival.
Local Open Scope nat_scope.

(** Certificates for [classic/model/arrival/jitter/task_arrival.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job/task
    parameters [X -> time] pointwise through [SubNatRel]; job sequences elementwise; arrival sequences pointwise on
    related times; all with two-way totals.  The imported [ArrivalSequence], [TaskArrival] and
    [ArrivalSequenceWithJitter] definitions are related as in the accepted classic certificates (re-bound below).

    Computation: as in the accepted classic task_arrival certificate — [\cat_(t1 <= t < t2) F t] through
    [bigCat_range'], MathComp's stable [sort] against [List.mergeSort] through the exported kernel-checked
    [mergeSort_isChain] / [mergeSort_filter_class] (restated under [ClassicJitterTaskArrivalInterface]), [nth] against
    [List.getD], [n.-1] against [n - 1].

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used).  For the lemmas whose Rocq and Lean binder lists put [task_period : Task -> time] before the job
    type, the job type is fixed as an [eqType] with its canonical Lean instance and [task_period] stays universally
    quantified on both sides (as in the accepted classic task_arrival certificate). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cjt_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cjt_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cjt_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cjt_false_rel). Qed.

Lemma cjt_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cjt_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cjt_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cjt_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cjt_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Definition CjtParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cjt_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CjtParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cjt_forall_cover _ _ (CjtParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cjt_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cjt_natl s') end.

Definition cjt_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cjt_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cjt_one) (cjt_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cjt_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cjt_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cjt_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cjt_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cjt_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cjt_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cjt_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cjt_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cjt_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cjt_cl_append. reflexivity.
Qed.

Lemma cjt_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CjtFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cjt_bigcat_rel (A : Type) fR fL (Hf : CjtFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterTaskArrivalInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cjt_iota_range (nR - mR) 0) cjt_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cjt_cl_map_ext _ _ Hpt) (cjt_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cjt_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cjt_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CjtArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cjt_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cjt_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cjt_arr_canonical aR : CjtArrRel aR (cjt_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cjt_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cjt_arr_surjective aL : CjtArrRel (cjt_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cjt_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CjtArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cjt_forall_cover _ _ CjtArrRel cjt_arr_to_target cjt_arr_to_source cjt_arr_canonical cjt_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cjt_jobs_arrived_between aR aL (Ha : CjtArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cjt_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cjt_arrives_in aR aL (Ha : CjtArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cjt_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cjt_consistent pR pL (Hp : CjtParRel Job pR pL) aR aL (Ha : CjtArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cjt_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cjt_is_a_set aR aL (Ha : CjtArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cjt_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cjt_jobs_arrived_before aR aL (Ha : CjtArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job dJ aL tL).
Proof. exact (cjt_jobs_arrived_between Job aR aL Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma cjt_arrives_at aR aL (Ha : CjtArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cjt_mem Job j _ _ (Ha tR tL Ht))). Qed.

End ArrivalDefs2.

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cjt_TA_sporadic_task_model tpR tpL (Htp : CjtParRel Task tpR tpL)
    jaR jaL (Hja : CjtParRel Job jaR jaL) (job_task : Job -> Task) aR aL (Ha : CjtArrRel Job aR aL) :
  PropSPropRel (TaskArrival.sporadic_task_model tpR jaR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model Task dT tpL Job dJ jaL job_task aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'.
  apply: ct_imp; first exact (cjt_ne Job j j').
  apply: ct_imp; first exact (cjt_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cjt_arrives_in Job aR aL Ha j').
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j')).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htp (job_task j))) (Hja j')).
Qed.

Lemma cjt_TA_is_job_of_task (job_task : Job -> Task) tsk j :
  CtBoolRel (TaskArrival.is_job_of_task job_task tsk j)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_is_job_of_task Task Job dT dJ job_task tsk j).
Proof. exact (ct_decide_eq Task (job_task j) tsk). Qed.

End TaskArrivalDefs.

(** The imported [ArrivalSequenceWithJitter] definitions (as in the accepted classic jitter arrival_sequence certificate). *)
Section JitterArrDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cjt_AJ_actual_arrival pR pL (Hp : CjtParRel Job pR pL) qR qL (Hq : CjtParRel Job qR qL) j :
  SubNatRel (ArrivalSequenceWithJitter.actual_arrival pR qR j) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Hp j) (Hq j)). Qed.

Lemma cjt_AJ_actual_arrivals_between pR pL (Hp : CjtParRel Job pR pL) qR qL (Hq : CjtParRel Job qR qL)
    aR aL (Ha : CjtArrRel Job aR aL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_between pR qR aR t1R t2R) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_between Job dJ pL qL aL t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cjt_jobs_arrived_before Job aR aL Ha t2R t2L H2).
  have F := cl_filter cid _
              (fun j => I.Bool_and
                 (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j))
                    (I.Nat_decLe t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j)))
                 (I.Decidable_decide (I.LT_lt_inst1 Lean.Nat I.instLTNat (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)
                    (I.Nat_decLt (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)))
              (fun j => ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (cjt_AJ_actual_arrival pR pL Hp qR qL Hq j))
                                          (ct_decide_lt _ _ _ _ (cjt_AJ_actual_arrival pR pL Hp qR qL Hq j) H2))
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

Lemma cjt_leT_trans : transitive leT.
Proof. move=> y x z. exact: leq_trans. Qed.

Lemma cjt_leT_total : total leT.
Proof. move=> a b. exact: leq_total. Qed.

Lemma cjt_class_sorted x : forall l : seq T, all (cls x) l -> sorted leT l.
Proof.
  case => [|a l] //= /andP [Ha Hl]. elim: l a Ha Hl => [|b l IH] a Ha //= /andP [Hb Hl].
  rewrite (eqP Ha) (eqP Hb) leqnn /=. exact: IH.
Qed.

Lemma cjt_sort_filter_class s x : filter (cls x) (sort leT s) = filter (cls x) s.
Proof.
  rewrite (filter_sort cjt_leT_total cjt_leT_trans).
  apply: (sorted_sort cjt_leT_trans). apply: cjt_class_sorted. exact: filter_all.
Qed.

Lemma cjt_sorted_class_uniq : forall u t : seq T, sorted leT u -> sorted leT t ->
  (forall x, filter (cls x) u = filter (cls x) t) -> u = t.
Proof.
  elim => [|a u IH] t Su St H.
  { case: t St H => [//|b t] St H. by have := H b; rewrite /= eqxx. }
  case: t St H => [|b t] St H; first by have := H a; rewrite /= eqxx.
  have Ma : all (leT a) u := order_path_min cjt_leT_trans Su.
  have Mb : all (leT b) t := order_path_min cjt_leT_trans St.
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

Lemma cjt_sort_unique (u s : seq T) : sorted leT u -> (forall x, filter (cls x) u = filter (cls x) s) -> u = sort leT s.
Proof.
  move=> Su H. apply: cjt_sorted_class_uniq => //.
  - exact: (sort_sorted cjt_leT_total).
  - move=> x. by rewrite cjt_sort_filter_class H.
Qed.

End SortUniq.

Section Chain.
Variables (T : Type) (leR : T -> T -> bool) (leL : T -> T -> I.Bool).
Hypothesis HR : forall a b, CtBoolRel (leR a b) (leL a b).
Notation RL := (fun a b : T => Lean.eq (leL a b) I.Bool_true).

Inductive CjtTrue : SProp := cjt_true_intro.

Definition cjt_chain_head (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) : RL x y :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons a (I.List_cons b _) => RL a b | _ => CjtTrue end) with
  | I.List_IsChain_nil => cjt_true_intro
  | I.List_IsChain_singleton _ => cjt_true_intro
  | I.List_IsChain_cons_cons a b l h _ => h
  end.

Definition cjt_chain_tail (x y : T) (l : I.List T) (H : I.List_IsChain T RL (I.List_cons T x (I.List_cons T y l))) :
    I.List_IsChain T RL (I.List_cons T y l) :=
  match H in I.List_IsChain _ _ L
    return (match L with I.List_cons _ (I.List_cons b l') => I.List_IsChain T RL (I.List_cons T b l') | _ => CjtTrue end) with
  | I.List_IsChain_nil => cjt_true_intro
  | I.List_IsChain_singleton _ => cjt_true_intro
  | I.List_IsChain_cons_cons a b l _ t => t
  end.

Fixpoint cjt_path_backward (x : T) (s : seq T) : I.List_IsChain T RL (I.List_cons T x (cl_map cid s)) -> StrictlyInhabited (path leR x s) :=
  match s as s0 return I.List_IsChain T RL (I.List_cons T x (cl_map cid s0)) -> StrictlyInhabited (path leR x s0) with
  | [::] => fun _ => strictly_inhabits (Logic.eq_refl true)
  | y :: s' => fun H =>
      match cjt_path_backward y s' (cjt_chain_tail x y _ H) with
      | strictly_inhabits Hp =>
          strictly_inhabits (introT andP (conj (sprop_to_prop _ _ (ct_bool_truth _ _ (HR x y)) (cjt_chain_head x y _ H)) Hp))
      end
  end.

Lemma cjt_sorted_backward s : I.List_IsChain T RL (cl_map cid s) -> StrictlyInhabited (sorted leR s).
Proof.
  destruct s as [|x s].
  - intros _. exact (strictly_inhabits (Logic.eq_refl true)).
  - exact (cjt_path_backward x s).
Qed.

End Chain.

Section Sort.
Variables (T : eqType) (f : T -> nat) (fL : T -> Lean.Nat).
Hypothesis Hf : forall x, SubNatRel (f x) (fL x).
Notation leL := (fun j j' : T => I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat (fL j) (fL j')) (I.Nat_decLe (fL j) (fL j'))).
Notation clsL x := (fun y : T => I.Decidable_decide (Lean.eq (fL y) (fL x)) (I.instDecidableEqNat (fL y) (fL x))).

Lemma cjt_sort_rel s sL : ClListRel cid s sL ->
  ClListRel cid (sort (fun j j' => f j <= f j') s) (I.List_mergeSort T sL leL).
Proof.
  intro Hs.
  pose m := I.List_mergeSort T sL leL. pose u := cl_unmap cid m.
  have Hu : ClListRel cid u m := cjt_unmap_rel T m.
  have Su : sorted (fun a b => f a <= f b) u :=
    interpret_strict _
      (cjt_sorted_backward T (fun a b => f a <= f b) leL (fun a b => ct_decide_le _ _ _ _ (Hf a) (Hf b)) u
         (match Hu in Lean.eq _ z
                return I.List_IsChain T (fun a b => Lean.eq (leL a b) I.Bool_true) z ->
                       I.List_IsChain T (fun a b => Lean.eq (leL a b) I.Bool_true) (cl_map cid u) with
          | Lean.eq_refl => fun h => h
          end (I.Prosa_Validation_ClassicJitterTaskArrivalInterface_mergeSort_isChain T fL sL))).
  have Fu : forall x, filter (fun y => f y == f x) u = filter (fun y => f y == f x) s.
  { intro x. apply: cjt_cl_map_inj.
    have Hp : forall y, CtBoolRel (f y == f x) (clsL x y) := fun y => ct_decide_eq_nat _ _ _ _ (Hf y) (Hf x).
    refine (Logic.eq_trans (cl_filter cid (fun y => f y == f x) (clsL x) Hp u)
              (Logic.eq_trans _ (Logic.eq_sym (cl_filter cid (fun y => f y == f x) (clsL x) Hp s)))).
    refine (Logic.eq_trans (f_equal (I.List_filter T (clsL x)) (Logic.eq_sym (cl_list_logic _ _ _ Hu)))
              (Logic.eq_trans _ (f_equal (I.List_filter T (clsL x)) (cl_list_logic _ _ _ Hs)))).
    exact (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterTaskArrivalInterface_mergeSort_filter_class T fL x sL)). }
  have E := cjt_sort_unique T f u s Su Fu.
  apply: coq_eq_to_imported_eq. rewrite -E. exact (Logic.eq_sym (cl_list_logic _ _ _ Hu)).
Qed.

End Sort.

Lemma cjt_getD (T : Type) (s : seq T) sL (Hs : ClListRel cid s sL) (x0 : T) nR nL (Hn : SubNatRel nR nL) :
  Logic.eq (I.List_getD T sL nL x0) (nth x0 s nR).
Proof.
  rewrite (cl_list_logic _ _ _ Hs) (cl_nat_logic _ _ Hn). exact (Logic.eq_sym (cl_nth cid x0 s nR)).
Qed.

Lemma cjt_pred_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ct_sub nL (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Hn. apply: coq_eq_to_imported_eq. rewrite -subn1.
  exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1))).
Qed.


(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Theorem TaskArrivalWithJitter_is_job_of_tsk_correspondence (job_task : Job -> Task) tsk j :
  CtBoolRel (TaskArrivalWithJitter.is_job_of_tsk job_task tsk j) (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_is_job_of_tsk Task dT Job dJ job_task tsk j).
Proof. exact (cjt_TA_is_job_of_task Task Job job_task tsk j). Qed.

Theorem TaskArrivalWithJitter_actual_arrivals_of_task_between_correspondence jaR jaL (Hja : CjtParRel Job jaR jaL)
    jjR jjL (Hjj : CjtParRel Job jjR jjL) (job_task : Job -> Task) aR aL (Ha : CjtArrRel Job aR aL) tsk
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  ClListRel cid (TaskArrivalWithJitter.actual_arrivals_of_task_between jaR jjR job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_actual_arrivals_of_task_between Task dT Job dJ jaL jjL job_task aL tsk t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  refine (Logic.eq_trans (cl_filter cid _ (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_is_job_of_tsk Task dT Job dJ job_task tsk)
                            (TaskArrivalWithJitter_is_job_of_tsk_correspondence job_task tsk) _) _).
  exact (f_equal (I.List_filter Job (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_is_job_of_tsk Task dT Job dJ job_task tsk))
           (Logic.eq_sym (cl_list_logic _ _ _ (cjt_AJ_actual_arrivals_between Job jaR jaL Hja jjR jjL Hjj aR aL Ha _ _ H1 _ _ H2)))).
Qed.

Theorem TaskArrivalWithJitter_num_actual_arrivals_of_task_correspondence jaR jaL (Hja : CjtParRel Job jaR jaL)
    jjR jjL (Hjj : CjtParRel Job jjR jjL) (job_task : Job -> Task) aR aL (Ha : CjtArrRel Job aR aL) tsk
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (TaskArrivalWithJitter.num_actual_arrivals_of_task jaR jjR job_task aR tsk t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_num_actual_arrivals_of_task Task dT Job dJ jaL jjL job_task aL tsk t1L t2L).
Proof.
  have H := TaskArrivalWithJitter_actual_arrivals_of_task_between_correspondence jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2.
  change (SubNatRel (size (TaskArrivalWithJitter.actual_arrivals_of_task_between jaR jjR job_task aR tsk t1R t2R))
    (I.List_length Job (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_actual_arrivals_of_task_between Task dT Job dJ jaL jjL job_task aL tsk t1L t2L))).
  exact (match H in Lean.eq _ z
               return SubNatRel (size (TaskArrivalWithJitter.actual_arrivals_of_task_between jaR jjR job_task aR tsk t1R t2R)) (I.List_length Job z) with
         | Lean.eq_refl => cl_size cid _
         end).
Qed.

Lemma cjt_sorted_rel jaR jaL (Hja : CjtParRel Job jaR jaL) jjR jjL (Hjj : CjtParRel Job jjR jjL) (job_task : Job -> Task)
    aR aL (Ha : CjtArrRel Job aR aL) tsk t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  ClListRel cid (sort (fun j j' => jaR j <= jaR j') (TaskArrivalWithJitter.actual_arrivals_of_task_between jaR jjR job_task aR tsk t1R t2R))
    (I.List_mergeSort Job (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_actual_arrivals_of_task_between Task dT Job dJ jaL jjL job_task aL tsk t1L t2L)
       (fun j j' => I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat (jaL j) (jaL j')) (I.Nat_decLe (jaL j) (jaL j')))).
Proof.
  exact (cjt_sort_rel Job jaR jaL Hja _ _
           (TaskArrivalWithJitter_actual_arrivals_of_task_between_correspondence jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2)).
Qed.
End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation num := TaskArrivalWithJitter_num_actual_arrivals_of_task_correspondence.
Notation AAJ := cjt_AJ_actual_arrival.

Definition src_sorted_arrivals_properties_of_nth (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@TaskArrivalWithJitter.sorted_arrivals_properties_of_nth Task Job)).
Definition tgt_sorted_arrivals_properties_of_nth (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_sorted_arrivals_properties_of_nth Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).

Theorem TaskArrivalWithJitter_sorted_arrivals_properties_of_nth_correspondence (Task Job : eqType) :
  PropSPropRel (src_sorted_arrivals_properties_of_nth Task Job) (tgt_sorted_arrivals_properties_of_nth Task Job).
Proof.
  unfold src_sorted_arrivals_properties_of_nth, tgt_sorted_arrivals_properties_of_nth.
  apply: cjt_forall_par => jaR jaL Hja. apply: cjt_forall_par => jjR jjL Hjj.
  apply: ct_forall_identity => job_task. apply: cjt_forall_arr => aR aL Ha.
  apply: ct_forall_identity => tsk. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_forall_identity => elem. apply: ct_forall_nat => iR iL Hi.
  have Hn := num Task Job jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hi Hn).
  rewrite (cjt_getD _ _ _ (cjt_sorted_rel Task Job jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2) elem _ _ Hi).
  set x := nth elem _ iR.
  have Hx := AAJ Job jaR jaL Hja jjR jjL Hjj x.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Hx) (ct_decide_lt _ _ _ _ Hx H2))).
  apply: ct_and; first exact (ct_eq_rel Task (job_task x) tsk).
  exact (cjt_arrives_in Job aR aL Ha x).
Qed.

Definition src_sorted_arrivals_current_differs_from_next (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@TaskArrivalWithJitter.sorted_arrivals_current_differs_from_next Task Job)).
Definition tgt_sorted_arrivals_current_differs_from_next (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_sorted_arrivals_current_differs_from_next Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).

Theorem TaskArrivalWithJitter_sorted_arrivals_current_differs_from_next_correspondence (Task Job : eqType) :
  PropSPropRel (src_sorted_arrivals_current_differs_from_next Task Job) (tgt_sorted_arrivals_current_differs_from_next Task Job).
Proof.
  unfold src_sorted_arrivals_current_differs_from_next, tgt_sorted_arrivals_current_differs_from_next.
  apply: cjt_forall_par => jaR jaL Hja. apply: cjt_forall_par => jjR jjL Hjj.
  apply: ct_forall_identity => job_task. apply: cjt_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cjt_consistent Job jaR jaL Hja aR aL Ha).
  apply: ct_imp; first exact (cjt_is_a_set Job aR aL Ha).
  apply: ct_forall_identity => tsk. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_forall_identity => elem. apply: ct_forall_nat => iR iL Hi.
  have Hn := num Task Job jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hi (cjt_pred_rel _ _ Hn)).
  have Hs := cjt_sorted_rel Task Job jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2.
  rewrite (cjt_getD _ _ _ Hs elem _ _ Hi) (cjt_getD _ _ _ Hs elem _ _ (cjt_succ_rel _ _ Hi)).
  exact (cjt_ne Job _ _).
Qed.

Definition src_sorted_arrivals_separated_by_period (Task Job : eqType) : Prop :=
  forall task_period : Task -> Time.time,
    ltac:(type_of_term (@TaskArrivalWithJitter.sorted_arrivals_separated_by_period Task task_period Job)).
Definition tgt_sorted_arrivals_separated_by_period (Task Job : eqType) : SProp :=
  forall task_period : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_sorted_arrivals_separated_by_period Task (ct_decidable_eq Task) task_period Job (ct_decidable_eq Job))).

Theorem TaskArrivalWithJitter_sorted_arrivals_separated_by_period_correspondence (Task Job : eqType) :
  PropSPropRel (src_sorted_arrivals_separated_by_period Task Job) (tgt_sorted_arrivals_separated_by_period Task Job).
Proof.
  unfold src_sorted_arrivals_separated_by_period, tgt_sorted_arrivals_separated_by_period.
  apply: cjt_forall_par => tpR tpL Htp.
  apply: cjt_forall_par => jaR jaL Hja. apply: cjt_forall_par => jjR jjL Hjj.
  apply: ct_forall_identity => job_task. apply: cjt_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cjt_consistent Job jaR jaL Hja aR aL Ha).
  apply: ct_imp; first exact (cjt_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (cjt_TA_sporadic_task_model Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_forall_identity => elem. apply: ct_forall_nat => iR iL Hi.
  have Hn := num Task Job jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hi (cjt_pred_rel _ _ Hn)).
  have Hs := cjt_sorted_rel Task Job jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2.
  rewrite (cjt_getD _ _ _ Hs elem _ _ Hi) (cjt_getD _ _ _ Hs elem _ _ (cjt_succ_rel _ _ Hi)).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja _) (Htp tsk)) (Hja _)).
Qed.

Definition src_sorted_arrivals_distance_from_first_job (Task Job : eqType) : Prop :=
  forall task_period : Task -> Time.time,
    ltac:(type_of_term (@TaskArrivalWithJitter.sorted_arrivals_distance_from_first_job Task task_period Job)).
Definition tgt_sorted_arrivals_distance_from_first_job (Task Job : eqType) : SProp :=
  forall task_period : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_sorted_arrivals_distance_from_first_job Task (ct_decidable_eq Task) task_period Job (ct_decidable_eq Job))).

Theorem TaskArrivalWithJitter_sorted_arrivals_distance_from_first_job_correspondence (Task Job : eqType) :
  PropSPropRel (src_sorted_arrivals_distance_from_first_job Task Job) (tgt_sorted_arrivals_distance_from_first_job Task Job).
Proof.
  unfold src_sorted_arrivals_distance_from_first_job, tgt_sorted_arrivals_distance_from_first_job.
  apply: cjt_forall_par => tpR tpL Htp.
  apply: cjt_forall_par => jaR jaL Hja. apply: cjt_forall_par => jjR jjL Hjj.
  apply: ct_forall_identity => job_task. apply: cjt_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cjt_consistent Job jaR jaL Hja aR aL Ha).
  apply: ct_imp; first exact (cjt_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (cjt_TA_sporadic_task_model Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_forall_identity => elem. apply: ct_forall_nat => iR iL Hi.
  have Hn := num Task Job jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hi Hn).
  have Hs := cjt_sorted_rel Task Job jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2.
  rewrite (cjt_getD _ _ _ Hs elem _ _ (sub_nat_rel_canonical 0)) (cjt_getD _ _ _ Hs elem _ _ Hi).
  exact (sub_nat_le_correspondence _ _ _ _
           (sub_add_correspondence _ _ _ _ (Hja _) (sub_mul_correspondence _ _ _ _ Hi (Htp tsk))) (Hja _)).
Qed.

Definition src_sorted_arrivals_distance_between_first_and_last (Task Job : eqType) : Prop :=
  forall task_period : Task -> Time.time,
    ltac:(type_of_term (@TaskArrivalWithJitter.sorted_arrivals_distance_between_first_and_last Task task_period Job)).
Definition tgt_sorted_arrivals_distance_between_first_and_last (Task Job : eqType) : SProp :=
  forall task_period : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Model_Arrival_Jitter_TaskArrival_TaskArrivalWithJitter_sorted_arrivals_distance_between_first_and_last Task (ct_decidable_eq Task) task_period Job (ct_decidable_eq Job))).

Theorem TaskArrivalWithJitter_sorted_arrivals_distance_between_first_and_last_correspondence (Task Job : eqType) :
  PropSPropRel (src_sorted_arrivals_distance_between_first_and_last Task Job)
    (tgt_sorted_arrivals_distance_between_first_and_last Task Job).
Proof.
  unfold src_sorted_arrivals_distance_between_first_and_last, tgt_sorted_arrivals_distance_between_first_and_last.
  apply: cjt_forall_par => tpR tpL Htp.
  apply: cjt_forall_par => jaR jaL Hja. apply: cjt_forall_par => jjR jjL Hjj.
  apply: ct_forall_identity => job_task. apply: cjt_forall_arr => aR aL Ha.
  apply: ct_imp; first exact (cjt_consistent Job jaR jaL Hja aR aL Ha).
  apply: ct_imp; first exact (cjt_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (cjt_TA_sporadic_task_model Task Job tpR tpL Htp jaR jaL Hja job_task aR aL Ha).
  apply: ct_forall_identity => tsk. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_forall_identity => elem.
  have Hn := num Task Job jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (sub_nat_rel_canonical 1) Hn).
  have Hs := cjt_sorted_rel Task Job jaR jaL Hja jjR jjL Hjj job_task aR aL Ha tsk _ _ H1 _ _ H2.
  have Hm1 := ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1).
  rewrite (cjt_getD _ _ _ Hs elem _ _ (sub_nat_rel_canonical 0)) (cjt_getD _ _ _ Hs elem _ _ (cjt_pred_rel _ _ Hn)).
  exact (sub_nat_le_correspondence _ _ _ _
           (sub_add_correspondence _ _ _ _ (Hja _) (sub_mul_correspondence _ _ _ _ Hm1 (Htp tsk))) (Hja _)).
Qed.
