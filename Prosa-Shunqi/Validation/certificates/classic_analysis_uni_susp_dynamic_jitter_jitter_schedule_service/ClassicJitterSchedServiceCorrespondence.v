From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.minmax classic.model.suspension classic.model.priority classic.model.arrival.basic.arrival_sequence classic.model.arrival.jitter.arrival_sequence classic.model.schedule.uni.schedule classic.model.schedule.uni.jitter.schedule classic.model.schedule.uni.transformation.construction classic.analysis.uni.susp.dynamic.jitter.jitter_schedule classic.model.schedule.uni.response_time classic.model.schedule.uni.jitter.valid_schedule classic.model.schedule.uni.jitter.platform classic.model.schedule.uni.susp.last_execution classic.model.schedule.uni.susp.suspension_intervals classic.model.schedule.uni.susp.schedule classic.model.schedule.uni.susp.valid_schedule classic.model.schedule.uni.susp.platform classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties classic.model.arrival.basic.task classic.model.arrival.basic.task_arrival classic.model.schedule.uni.workload classic.model.schedule.uni.service classic.model.arrival.jitter.arrival_sequence classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicJitterSchedService.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicJitterSchedServiceBase ClassicJitterSchedServiceList ClassicJitterSchedServiceOrd.



Module I := ImportedClassicJitterSchedService.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/uni/susp/dynamic/jitter/jitter_schedule_service.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the eqTypes'
    decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job parameters (costs, arrivals,
    response-time bounds) pointwise through [SubNatRel]; suspension functions pointwise on related times; FP policies
    pointwise on Booleans; arrival sequences pointwise on related times; uniprocessor schedules pointwise through the
    option map; all with two-way totals.  Every definition is related for arbitrary related inputs.  [seq_min] as in the
    accepted classic minmax certificate; the construction from prefixes as in the accepted classic uniprocessor
    construction certificate (re-bound below: the construction step [build_schedule] maps related schedules and instants
    to related choices); [schedule_prefix] through its kernel-checked Lean recursion equations; [if x == y] against the
    Lean [if x = y] on the canonical instance; [minn] against [Min.min]. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cjs_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cjs_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cjs_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cjs_false_rel). Qed.

Lemma cjs_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cjs_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cjs_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cjs_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cjs_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cjs_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cjs_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cjs_unmap_rel T l) PR PL).
Qed.

Definition CjsParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cjs_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CjsParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cjs_forall_cover _ _ (CjsParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cjs_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cjs_natl s') end.

Definition cjs_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cjs_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cjs_one) (cjs_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cjs_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cjs_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cjs_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cjs_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cjs_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cjs_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cjs_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cjs_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cjs_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cjs_cl_append. reflexivity.
Qed.

Lemma cjs_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CjsFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cjs_bigcat_rel (A : Type) fR fL (Hf : CjsFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterSchedServiceInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cjs_iota_range (nR - mR) 0) cjs_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cjs_cl_map_ext _ _ Hpt) (cjs_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cjs_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cjs_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CjsArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cjs_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cjs_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cjs_arr_canonical aR : CjsArrRel aR (cjs_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cjs_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cjs_arr_surjective aL : CjsArrRel (cjs_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cjs_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CjsArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cjs_forall_cover _ _ CjsArrRel cjs_arr_to_target cjs_arr_to_source cjs_arr_canonical cjs_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cjs_jobs_arrived_between aR aL (Ha : CjsArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cjs_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cjs_arrives_in aR aL (Ha : CjsArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cjs_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cjs_consistent pR pL (Hp : CjsParRel Job pR pL) aR aL (Ha : CjsArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cjs_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cjs_is_a_set aR aL (Ha : CjsArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cjs_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cjs_jobs_arrived_before aR aL (Ha : CjsArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job dJ aL tL).
Proof. exact (cjs_jobs_arrived_between Job aR aL Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma cjs_arrives_at aR aL (Ha : CjsArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cjs_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma cjs_has_arrived pR pL (Hp : CjsParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cjs_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cjs_snatl s') end.

Lemma cjs_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cjs_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cjs_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cjs_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cjs_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cjs_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cjs_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CjsFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cjs_fun_canonical FR FL (HF : CjsFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cjs_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cjs_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CjsFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cjs_nat_sub_canonical nR mR.
  rewrite cjs_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cjs_foldr_add FL FR (cjs_fun_canonical FR FL HF)).
  by rewrite cjs_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cjs_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cjs_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cjs_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cjs_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cjs_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CjsSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cjs_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cjs_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cjs_sched_canonical sR : CjsSchedRel sR (cjs_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cjs_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cjs_sched_surjective sL : CjsSchedRel (cjs_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cjs_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cjs_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CjsSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cjs_forall_cover _ _ CjsSchedRel cjs_sched_to_target cjs_sched_to_source cjs_sched_canonical cjs_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cjs_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CjsSchedRel Job sR (cjs_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CjsSchedRel Job (cjs_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cjs_sched_canonical Job) (cjs_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjsSchedRel Job sR sL.

Lemma cjs_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cjs_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cjs_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cjs_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cjs_US_scheduled_at j tR tL Ht)). Qed.

Lemma cjs_service_at_fun j : CjsFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cjs_US_service_at j kR kL Hk). Qed.

Lemma cjs_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cjs_ico _ _ _ _ _ _ H1 H2 (cjs_service_at_fun j)). Qed.

Lemma cjs_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cjs_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cjs_US_completed_by cR cL (Hc : CjsParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cjs_US_service j tR tL Ht)). Qed.

Lemma cjs_US_pending aR aL (Ha : CjsParRel Job aR aL) cR cL (Hc : CjsParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cjs_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cjs_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cjs_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CjsArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cjs_US_scheduled_at j tR tL Ht)).
  exact (cjs_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cjs_US_jobs_must_arrive_to_execute aR aL (Ha : CjsParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cjs_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cjs_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma cjs_US_completed_jobs_dont_execute cR cL (Hc : CjsParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cjs_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

Section SuspSusp.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSusp := (I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).

Definition CjsSuspRel (sR : Suspension.job_suspension Job) (sL : LSusp) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (sR j tR) (sL j tL).

Definition cjs_susp_to_target (sR : Suspension.job_suspension Job) : LSusp :=
  fun j tL => sub_nat_to_imported (sR j (sub_nat_to_rocq tL)).

Definition cjs_susp_to_source (sL : LSusp) : Suspension.job_suspension Job :=
  fun j tR => sub_nat_to_rocq (sL j (sub_nat_to_imported tR)).

Lemma cjs_susp_canonical sR : CjsSuspRel sR (cjs_susp_to_target sR).
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  unfold cjs_susp_to_target. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma cjs_susp_surjective sL : CjsSuspRel (cjs_susp_to_source sL) sL.
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma cjs_forall_susp (PR : Suspension.job_suspension Job -> Prop) (PL : LSusp -> SProp) :
  (forall sR sL, CjsSuspRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cjs_forall_cover _ _ CjsSuspRel cjs_susp_to_target cjs_susp_to_source cjs_susp_canonical cjs_susp_surjective PR PL). Qed.

End SuspSusp.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cjs_SU_job_suspension (Job : eqType) :
  And (forall sR : Suspension.job_suspension Job, CjsSuspRel Job sR (cjs_susp_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job (ct_decidable_eq Job), CjsSuspRel Job (cjs_susp_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cjs_susp_canonical Job) (cjs_susp_surjective Job)). Qed.

Lemma cjs_SU_total_suspension (Job : eqType) cR cL (Hc : CjsParRel Job cR cL) sR sL (Hs : CjsSuspRel Job sR sL) j :
  SubNatRel (Suspension.total_suspension cR sR j) (I.Prosa_Classic_Model_Suspension_Suspension_total_suspension Job (ct_decidable_eq Job) cL sL j).
Proof. exact (cjs_ico 0 _ (cR j) (cL j) (sR j) (sL j) (sub_nat_rel_canonical 0) (Hc j) (Hs j)). Qed.

(** The imported [ArrivalSequenceWithJitter] definitions (as in the accepted classic jitter arrival_sequence certificate). *)
Section JitterArrDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cjs_AJ_actual_arrival pR pL (Hp : CjsParRel Job pR pL) qR qL (Hq : CjsParRel Job qR qL) j :
  SubNatRel (ArrivalSequenceWithJitter.actual_arrival pR qR j) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Hp j) (Hq j)). Qed.

Lemma cjs_AJ_jitter_has_passed pR pL (Hp : CjsParRel Job pR pL) qR qL (Hq : CjsParRel Job qR qL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequenceWithJitter.jitter_has_passed pR qR j tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_jitter_has_passed Job dJ pL qL j tL).
Proof. exact (ct_decide_le _ _ _ _ (cjs_AJ_actual_arrival pR pL Hp qR qL Hq j) Ht). Qed.

Lemma cjs_AJ_actual_arrival_before pR pL (Hp : CjsParRel Job pR pL) qR qL (Hq : CjsParRel Job qR qL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequenceWithJitter.actual_arrival_before pR qR j tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival_before Job dJ pL qL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (cjs_AJ_actual_arrival pR pL Hp qR qL Hq j) Ht). Qed.

Lemma cjs_AJ_actual_arrivals_between pR pL (Hp : CjsParRel Job pR pL) qR qL (Hq : CjsParRel Job qR qL)
    aR aL (Ha : CjsArrRel Job aR aL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_between pR qR aR t1R t2R) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_between Job dJ pL qL aL t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cjs_jobs_arrived_before Job aR aL Ha t2R t2L H2).
  have F := cl_filter cid _
              (fun j => I.Bool_and
                 (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j))
                    (I.Nat_decLe t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j)))
                 (I.Decidable_decide (I.LT_lt_inst1 Lean.Nat I.instLTNat (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)
                    (I.Nat_decLt (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)))
              (fun j => ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (cjs_AJ_actual_arrival pR pL Hp qR qL Hq j))
                                          (ct_decide_lt _ _ _ _ (cjs_AJ_actual_arrival pR pL Hp qR qL Hq j) H2))
              (ArrivalSequence.jobs_arrived_before aR t2R).
  rewrite -E in F. exact F.
Qed.

Lemma cjs_AJ_actual_arrivals_up_to pR pL (Hp : CjsParRel Job pR pL) qR qL (Hq : CjsParRel Job qR qL)
    aR aL (Ha : CjsArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_up_to pR qR aR tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_up_to Job dJ pL qL aL tL).
Proof. exact (cjs_AJ_actual_arrivals_between pR pL Hp qR qL Hq aR aL Ha 0 _ (sub_nat_rel_canonical 0) tR.+1 _ (cjs_succ_rel tR tL Ht)). Qed.

End JitterArrDefs.

Section UjschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjsSchedRel Job sR sL.

Lemma cjs_UJ_pending aR aL (Ha : CjsParRel Job aR aL) cR cL (Hc : CjsParRel Job cR cL)
    jjR jjL (Hjj : CjsParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.pending aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_pending Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cjs_AJ_jitter_has_passed Job aR aL Ha jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cjs_US_completed_by Job sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

End UjschedDefs.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CjsRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cjs_rel_canonical (T : Type) (rR : T -> T -> bool) : CjsRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cjs_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CjsRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cjs_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CjsRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cjs_forall_cover _ _ (CjsRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cjs_rel_canonical T) (cjs_rel_surjective T) PR PL).
Qed.

Definition CjsJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CjsRelRel T (rR tR) (rL tL).

Lemma cjs_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CjsJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cjs_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CjsJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cjs_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CjsJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cjs_forall_cover _ _ (CjsJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cjs_jldp_canonical T) (cjs_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cjs_PR_FP_policy :
  And (forall rR : Priority.FP_policy Task, CjsRelRel Task rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_FP_policy Task dT, CjsRelRel Task (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cjs_rel_canonical Task) (cjs_rel_surjective Task)). Qed.

Lemma cjs_PR_JLFP_policy :
  And (forall rR : Priority.JLFP_policy Job, CjsRelRel Job rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLFP_policy Job dJ, CjsRelRel Job (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cjs_rel_canonical Job) (cjs_rel_surjective Job)). Qed.

Lemma cjs_PR_JLDP_policy :
  And (forall rR : Priority.JLDP_policy Job, CjsJldpRel Job rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLDP_policy Job dJ,
         CjsJldpRel Job (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL).
Proof. exact (And_intro _ _ (cjs_jldp_canonical Job) (cjs_jldp_surjective Job)). Qed.

Lemma cjs_PR_FP_to_JLFP (job_task : Job -> Task) rR rL (Hr : CjsRelRel Task rR rL) :
  CjsRelRel Job (Priority.FP_to_JLFP job_task rR)
    (I.Prosa_Classic_Model_Priority_Priority_FP_to_JLFP Task Job dT dJ job_task rL).
Proof. intros a b. exact (Hr (job_task a) (job_task b)). Qed.

Lemma cjs_PR_FP_to_JLDP (job_task : Job -> Task) rR rL (Hr : CjsRelRel Task rR rL) :
  CjsJldpRel Job (Priority.FP_to_JLDP job_task rR)
    (I.Prosa_Classic_Model_Priority_Priority_FP_to_JLDP Task Job dT dJ job_task rL).
Proof. intros tR tL _ a b. exact (Hr (job_task a) (job_task b)). Qed.

Lemma cjs_reflexive (T : Type) rR rL (Hr : CjsRelRel T rR rL) :
  PropSPropRel (reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_reflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (Hr x x)). Qed.

Lemma cjs_transitive (T : Type) rR rL (Hr : CjsRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma cjs_PR_FP_is_reflexive rR rL (Hr : CjsRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_reflexive Task dT rL).
Proof. exact (cjs_reflexive Task rR rL Hr). Qed.

Lemma cjs_PR_FP_is_transitive rR rL (Hr : CjsRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_transitive Task dT rL).
Proof. exact (cjs_transitive Task rR rL Hr). Qed.

Lemma cjs_PR_FP_is_total_over_task_set rR rL (Hr : CjsRelRel Task rR rL) ts tsL (Hts : ClListRel cid ts tsL) :
  PropSPropRel (Priority.FP_is_total_over_task_set rR ts)
    (I.Prosa_Classic_Model_Priority_Priority_FP_is_total_over_task_set Task dT rL tsL).
Proof.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: ct_imp; first exact (cjs_mem Task x1 ts tsL Hts).
  apply: ct_imp; first exact (cjs_mem Task x2 ts tsL Hts).
  exact (ct_or _ _ _ _ (ct_bool_truth _ _ (Hr x1 x2)) (ct_bool_truth _ _ (Hr x2 x1))).
Qed.

End PriodefsDefs.

(* ------------------------------------------------------------------ *)
(** * [seq_min] (as in the accepted classic minmax certificate) *)

Lemma cjs_opt_eq {A} (o1 o2 : option A) : PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := f_equal cl_unopt (imported_eq_to_coq_eq _ _ E).
    by rewrite !cl_unopt_opt in E'.
Qed.

Section MinmaxArg.
Variables (T1 : eqType) (T2R : eqType) (T2L : Type) (d2 : I.DecidableEq T2L).
Variables (relR : T2R -> T2R -> bool) (relL : T2L -> T2L -> I.Bool) (FR : T1 -> T2R) (FL : T1 -> T2L).
Hypothesis Hcomp : forall x y, CtBoolRel (relR (FR x) (FR y)) (relL (FL x) (FL y)).
Notation d1 := (ct_decidable_eq T1).

Lemma cjs_argmin_step x l :
  Logic.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (I.List_cons T1 x l))
    (I.Prosa_Classic_Util_Minmax_seq_argmin_match_1 T1 (fun _ => I.Option T1)
       (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL l)
       (fun y => I.ite (I.Option T1) (Lean.eq (relL (FL x) (FL y)) I.Bool_true) (I.instDecidableEqBool (relL (FL x) (FL y)) I.Bool_true)
                   (I.Option_some T1 x) (I.Option_some T1 y))
       (fun _ => I.Option_some T1 x)).
Proof. reflexivity. Qed.

Lemma cjs_argmin_rel : forall l,
  Logic.eq (cl_opt (seq_argmin relR FR l)) (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (cl_map cid l)).
Proof.
  elim => [|x l IH] //=. rewrite cjs_argmin_step -IH.
  case: (seq_argmin relR FR l) => [y|] //=.
  rewrite (ct_bool_rel_logic _ _ (Hcomp x y)). by case: (relR (FR x) (FR y)).
Qed.

Lemma cjs_argmin_eq l L (H : ClListRel cid l L) o :
  PropSPropRel (Logic.eq (seq_argmin relR FR l) o)
    (Lean.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL L) (cl_opt o)).
Proof. destruct H. rewrite -cjs_argmin_rel. exact (cjs_opt_eq _ _). Qed.

End MinmaxArg.

Lemma cjs_seq_min (T : eqType) relR relL (Hrel : forall a b, CtBoolRel (relR a b) (relL a b)) l :
  Logic.eq (cl_opt (seq_min relR l)) (I.Prosa_Classic_Util_Minmax_seq_min T (ct_decidable_eq T) relL (cl_map cid l)).
Proof. exact (cjs_argmin_rel T T T (ct_decidable_eq T) relR relL (@Datatypes.id T) (I.id T) (fun x y => Hrel _ _) l). Qed.

(* ------------------------------------------------------------------ *)
(** * Options *)

Lemma cjs_opt_rel_eq (A : Type) (o1 o2 : option A) l1 l2 :
  Lean.eq (cl_opt o1) l1 -> Lean.eq (cl_opt o2) l2 -> PropSPropRel (Logic.eq o1 o2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. destruct H1. destruct H2. apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cjs_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Definition cjs_lsym {A : Type} {x y : A} (E : Lean.eq x y) : Lean.eq y x :=
  match E in Lean.eq _ z return Lean.eq z x with Lean.eq_refl => @Lean.eq_refl _ _ end.

Lemma cjs_src_transport {A : Type} (P : A -> SProp) (x y : A) : Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

Lemma cjs_nat_input (nR : nat) (nL : Lean.Nat) : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

(* ------------------------------------------------------------------ *)
(** * Construction from prefixes, specialised at related inputs

    As in the accepted v0.6 [implementation/facts/generic_schedule.v] certificate: the construction function
    [build_schedule : schedule Job -> time -> option Job] is a higher-order input; the certificates below are stated for
    any source function and any Lean function that agree (through the option map) on related schedules and related
    instants ([Hbuild]), and for related base schedules ([Hbase]); the predicate [P] of the last statement is related
    pointwise through the option map ([HP]).  Inside the statements every quantified schedule, instant and job is covered
    in both directions. *)

Section UconsConstruction.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Variable buildR : UniprocessorSchedule.schedule Job -> nat -> option Job.
Variable buildL : LSched -> Lean.Nat -> I.Option Job.
Hypothesis Hbuild : forall sR sL, CjsSchedRel Job sR sL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (buildR sR tR)) (buildL sL tL).
Variables (baseR : UniprocessorSchedule.schedule Job) (baseL : LSched).
Hypothesis Hbase : CjsSchedRel Job baseR baseL.

Lemma cjs_nat_eqb tR tL t'R t'L : SubNatRel tR tL -> SubNatRel t'R t'L ->
  CtBoolRel (tR == t'R) (I.Decidable_decide (Lean.eq tL t'L) (I.instDecidableEqNat tL t'L)).
Proof. intros Ht Ht'. exact (ct_decide_eq_nat _ _ _ _ Ht Ht'). Qed.

Lemma cjs_UC_update_schedule prevR prevL (Hprev : CjsSchedRel Job prevR prevL) nR nL (Hn : SubNatRel nR nL) :
  CjsSchedRel Job (@ScheduleConstruction.update_schedule Job buildR prevR nR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule Job dJ buildL prevL nL).
Proof.
  intros tR tL Ht. unfold ScheduleConstruction.update_schedule, I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule. cbv beta.
  apply: coq_eq_to_imported_eq.
  rewrite (ct_bool_rel_logic _ _ (cjs_nat_eqb tR tL nR nL Ht Hn)).
  case: (tR == nR).
  - exact (imported_eq_to_coq_eq _ _ (Hbuild prevR prevL Hprev tR tL Ht)).
  - exact (imported_eq_to_coq_eq _ _ (Hprev tR tL Ht)).
Qed.

Lemma cjs_prefix_canonical (mR : nat) :
  CjsSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL (sub_nat_to_imported mR)).
Proof.
  induction mR as [|m IH].
  - refine (cjs_trs (cjs_lsym (I.Prosa_Validation_ClassicJitterSchedServiceInterface_production_schedule_prefix_zero Job dJ buildL baseL))
              (fun z => CjsSchedRel Job _ z) _).
    exact (cjs_UC_update_schedule baseR baseL Hbase 0 _ (sub_nat_rel_canonical 0)).
  - assert (Hm1 : SubNatRel m.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
                                 (sub_nat_to_imported m) (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)))).
    { exact (cjs_src_transport (fun x => SubNatRel x _) _ _ (addn1 m)
               (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical 1))). }
    refine (cjs_trs Hm1 (fun z => CjsSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR m.+1) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) _).
    refine (cjs_trs (cjs_lsym (I.Prosa_Validation_ClassicJitterSchedServiceInterface_production_schedule_prefix_succ Job dJ buildL baseL (sub_nat_to_imported m)))
              (fun z => CjsSchedRel Job _ z) _).
    exact (cjs_UC_update_schedule _ _ IH _ _ Hm1).
Qed.

Lemma cjs_UC_schedule_prefix mR mL (Hm : SubNatRel mR mL) :
  CjsSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL mL).
Proof. exact (cjs_trs Hm (fun z => CjsSchedRel Job _ (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) (cjs_prefix_canonical mR)). Qed.

Lemma cjs_UC_build_schedule_from_prefixes :
  CjsSchedRel Job (@ScheduleConstruction.build_schedule_from_prefixes Job buildR baseR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_build_schedule_from_prefixes Job dJ buildL baseL).
Proof. intros tR tL Ht. exact (cjs_UC_schedule_prefix tR tL Ht tR tL Ht). Qed.

End UconsConstruction.

Section UjplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjsSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (jjR : Job -> nat) (jjL : Job -> Lean.Nat).
Hypotheses (Ha : CjsParRel Job aR aL) (Hc : CjsParRel Job cR cL) (Hjj : CjsParRel Job jjR jjL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CjsArrRel Job arrR arrL.

Notation SA := (cjs_US_scheduled_at Job sR sL Hs).

End UjplatDefs.

(** * [\max] over ordinals against [maxFiltered] over [List.finRange] *)

Lemma cjs_foldr_max (f : Lean.Nat -> Lean.Nat) (g : nat -> nat)
    (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat I.Nat_max (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))
                        (I.List_map_inst3 Lean.Nat Lean.Nat f (co_natl s)))
                     (sub_nat_to_imported (foldr maxn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.Nat_max (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat I.Nat_max (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))
              (I.List_map_inst3 Lean.Nat Lean.Nat f (co_natl s))))
         (sub_nat_to_imported (maxn (g k) (foldr maxn 0 (map g s))))).
  rewrite IH Hf. exact (ct_max_canonical _ _).
Qed.

Lemma cjs_max_rel nR nL (Hn : SubNatRel nR nL) (QR : 'I_nR -> bool) (QL : Fin nL -> I.Bool) (HQ : CoOrdPredRel nR nL QR QL) :
  SubNatRel (\max_(i < nR | QR i) nat_of_ord i)
    (I.Prosa_Util_Sum_maxFiltered_inst1 (Fin nL) (I.List_finRange nL) QL (fun o => I.Fin_val nL o)).
Proof.
  have E := co_nat_logic _ _ Hn. subst nL. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterSchedServiceInterface_maxFiltered_finRange
             (sub_nat_to_imported nR) QL (fun o => I.Fin_val _ o))).
  rewrite big_mkcond (co_big_ord maxn 0 nR (fun i => if QR i then nat_of_ord i else 0) 0).
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (co_iota_range nR 0).
  have HF : forall o oL, CoOrdRel nR (sub_nat_to_imported nR) o oL ->
      Logic.eq (I.cond Lean.Nat (QL oL) (I.Fin_val _ oL) (sub_nat_to_imported 0))
               (sub_nat_to_imported (if QR o then nat_of_ord o else 0)).
  { intros o oL Ho. rewrite (ct_bool_rel_logic _ _ (HQ o oL Ho)). destruct (QR o).
    - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ Ho)).
    - reflexivity. }
  exact (cjs_foldr_max _ _ (co_fam_related nR sub_nat_to_imported (fun i => if QR i then nat_of_ord i else 0)
           (fun oL => I.cond Lean.Nat (QL oL) (I.Fin_val _ oL) (sub_nat_to_imported 0)) 0 HF) (iota 0 nR)).
Qed.

Lemma cjs_ite_rel bR bL (Hb : CtBoolRel bR bL) xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) :
  SubNatRel (if bR then xR else yR)
    (I.ite Lean.Nat (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) xL yL).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). destruct bR; [exact Hx | exact Hy]. Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cjs_LE_time_after_last_execution (Job : eqType) aR aL (Ha : CjsParRel Job aR aL)
    sR sL (Hs : CjsSchedRel Job sR sL) j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (LastExecution.time_after_last_execution aR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Susp_LastExecution_LastExecution_time_after_last_execution Job (ct_decidable_eq Job) aL sL j tL).
Proof.
  assert (HQ : CoOrdPredRel tR tL (fun o => UniprocessorSchedule.scheduled_at sR j o)
      (fun oL => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job (ct_decidable_eq Job) sL j (I.Fin_val tL oL))).
  { intros o oL Ho. exact (cjs_US_scheduled_at Job sR sL Hs j _ _ Ho). }
  exact (cjs_ite_rel _ _ (co_exists_rel tR tL Ht _ _ HQ) _ _
           (sub_add_correspondence _ _ _ _ (cjs_max_rel tR tL Ht _ _ HQ) (sub_nat_rel_canonical 1)) _ _ (Ha j)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Section SuspintDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjsSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CjsParRel Job aR aL) (Hc : CjsParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CjsSuspRel Job nR nL.

Lemma cjs_SI_suspension_duration j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (SuspensionIntervals.suspension_duration aR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspension_duration Job dJ aL nL sL j tL).
Proof. exact (Hn j _ _ (cjs_US_service Job sR sL Hs j _ _ ((cjs_LE_time_after_last_execution Job aR aL Ha sR sL Hs) j tR tL Ht))). Qed.

Lemma cjs_SI_suspended_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (SuspensionIntervals.suspended_at aR cR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspended_at Job dJ aL cL nL sL j tL).
Proof.
  have HT := (cjs_LE_time_after_last_execution Job aR aL Ha sR sL Hs) j tR tL Ht.
  exact (ct_bool_and _ _ _ _ (ct_bool_not _ _ (cjs_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht))
           (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ HT Ht)
              (ct_decide_lt _ _ _ _ Ht (sub_add_correspondence _ _ _ _ HT (cjs_SI_suspension_duration j tR tL Ht))))).
Qed.

Lemma cjs_SI_cumulative_suspension_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (SuspensionIntervals.cumulative_suspension_during aR cR nR sR j t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_cumulative_suspension_during Job dJ aL cL nL sL j t1L t2L).
Proof. exact (cjs_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (cjs_SI_suspended_at j kR kL Hk))). Qed.

Lemma cjs_SI_respects_self_suspensions :
  PropSPropRel (SuspensionIntervals.respects_self_suspensions aR cR nR sR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_respects_self_suspensions Job dJ aL cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cjs_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (cjs_SI_suspended_at j tR tL Ht)) cjs_false_rel).
Qed.

End SuspintDefs.

Section SuspschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjsSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CjsParRel Job aR aL) (Hc : CjsParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CjsSuspRel Job nR nL.

Lemma cjs_SS_backlogged j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithSuspensions.backlogged aR cR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Schedule_ScheduleWithSuspensions_backlogged Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _
           (ct_bool_and _ _ _ _ (cjs_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)
              (ct_bool_not _ _ (cjs_US_scheduled_at Job sR sL Hs j _ _ Ht)))
           (ct_bool_not _ _ (cjs_SI_suspended_at Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn j _ _ Ht))).
Qed.

End SuspschedDefs.

Section SuspplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjsSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CjsParRel Job aR aL) (Hc : CjsParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CjsSuspRel Job nR nL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CjsArrRel Job arrR arrL.

Notation SA := (cjs_US_scheduled_at Job sR sL Hs).

Lemma cjs_SP_work_conserving :
  PropSPropRel (PlatformWithSuspensions.work_conserving aR cR nR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Platform_PlatformWithSuspensions_work_conserving Job dJ aL cL nL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cjs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ ((cjs_SS_backlogged Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn) j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (SA j_other tR tL Ht)).
Qed.

Lemma cjs_SP_respects_JLDP_policy hR hL (Hh : CjsJldpRel Job hR hL) :
  PropSPropRel (PlatformWithSuspensions.respects_JLDP_policy aR cR nR arrR sR hR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Platform_PlatformWithSuspensions_respects_JLDP_policy Job dJ aL cL nL arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cjs_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ ((cjs_SS_backlogged Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn) j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh tR tL Ht j_hp j)).
Qed.

End SuspplatDefs.

Section UrtDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjsSchedRel Job sR sL.

Lemma cjs_RT_is_response_time_bound_of_job aR aL (Ha : CjsParRel Job aR aL) cR cL (Hc : CjsParRel Job cR cL)
    j rR rL (Hr : SubNatRel rR rL) :
  CtBoolRel (ResponseTime.is_response_time_bound_of_job aR cR sR j rR) (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_job Job dJ aL cL sL j rL).
Proof. exact (cjs_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr)). Qed.

End UrtDefs.

Lemma cjs_iff (P Q : Prop) (PL QL : SProp) :
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
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cjs_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicJitterSchedServiceInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicJitterSchedServiceInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cjs_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cjs_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cjs_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicJitterSchedServiceInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicJitterSchedServiceInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicJitterSchedServiceInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cjs_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cjs_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CjsPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma cjs_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CjsPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cjs_forall_cover _ _ (CjsPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

Section UwlDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cjs_WL_workload_of_jobs cR cL (Hc : CjsParRel Job cR cL) jobsR jobsL (Hj : ClListRel cid jobsR jobsL)
    pR pL (Hp : CjsPredRel Job pR pL) :
  SubNatRel (Workload.workload_of_jobs cR jobsR pR) (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_workload_of_jobs Job dJ cL jobsL pL).
Proof. exact (cjs_sum_filtered_rel Job cR cL Hc pR pL Hp _ _ Hj). Qed.

End UwlDefs.

Section TaskDefsP.
Variables (Task : eqType).
Notation dT := (ct_decidable_eq Task).
Notation c0 := (sub_nat_rel_canonical 0).

Lemma cjs_TK_constrained_deadline_model pR pL dR dL
    (Hp : CjsParRel Task pR pL) (Hd : CjsParRel Task dR dL) ts tsL (Hts : ClListRel cid ts tsL) :
  PropSPropRel (SporadicTaskset.constrained_deadline_model pR dR ts)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_constrained_deadline_model Task dT pL dL tsL).
Proof.
  apply: ct_forall_identity => tsk.
  exact (ct_imp _ _ _ _ (cjs_mem Task tsk ts tsL Hts) (sub_nat_le_correspondence _ _ _ _ (Hd tsk) (Hp tsk))).
Qed.

End TaskDefsP.

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cjs_TA_sporadic_task_model tpR tpL (Htp : CjsParRel Task tpR tpL)
    jaR jaL (Hja : CjsParRel Job jaR jaL) (job_task : Job -> Task) aR aL (Ha : CjsArrRel Job aR aL) :
  PropSPropRel (TaskArrival.sporadic_task_model tpR jaR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model Task dT tpL Job dJ jaL job_task aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'.
  apply: ct_imp; first exact (cjs_ne Job j j').
  apply: ct_imp; first exact (cjs_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cjs_arrives_in Job aR aL Ha j').
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j')).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htp (job_task j))) (Hja j')).
Qed.

End TaskArrivalDefs.

(* ------------------------------------------------------------------ *)
(** * Auxiliary relations *)

(** [minn] against the core [Min.min] on [Nat] (as in the accepted classic global workload_bound certificate). *)
Lemma cjs_min_canonical (a b : nat) :
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

Lemma cjs_min_rel aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel (minn aR bR) ((I.Min_min_inst1 Lean.Nat I.instMinNat) aL bL).
Proof.
  intros Ha Hb. rewrite -(imported_eq_to_coq_eq _ _ Ha) -(imported_eq_to_coq_eq _ _ Hb).
  apply: coq_eq_to_imported_eq. exact (Logic.eq_sym (cjs_min_canonical aR bR)).
Qed.

(** A Rocq Boolean equality test against the Lean [if x = y] on the canonical [DecidableEq] instance. *)
Lemma cjs_ite_eq (J : eqType) (A : Type) (x y : J) (a b : A) :
  Logic.eq (I.ite A (Lean.eq x y) (ct_decidable_eq J x y) a b) (if x == y then a else b).
Proof. rewrite /ct_decidable_eq. by case: (@eqP J x y). Qed.

(** A Boolean [if] against the Lean [if b = true]. *)
Lemma cjs_ite_bool (A : Type) bR bL (Hb : CtBoolRel bR bL) (a b : A) :
  Logic.eq (I.ite A (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) a b) (if bR then a else b).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). clear Hb. by case: bR. Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JSDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat).
Hypothesis Hja : CjsParRel Job jaR jaL.
Variable job_task : Job -> Task.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CjsArrRel Job aR aL.
Variables (hpR : Task -> Task -> bool) (hpL : Task -> Task -> I.Bool).
Hypothesis Hhp : CjsRelRel Task hpR hpL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CjsParRel Job cR cL.
Variables (suR : Suspension.job_suspension Job) (suL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hsu : CjsSuspRel Job suR suL.
Variable j : Job.
Variables (RR : Job -> nat) (RL : Job -> Lean.Nat).
Hypothesis HR : CjsParRel Job RR RL.

Lemma cjs_JS_inflated_job_cost :
  CjsParRel Job (@JitterScheduleConstruction.inflated_job_cost Job cR suR j) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_inflated_job_cost Job dJ cL suL j).
Proof.
  intro x. apply: coq_eq_to_imported_eq. rewrite /JitterScheduleConstruction.inflated_job_cost.
  unfold I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_inflated_job_cost. rewrite cjs_ite_eq.
  case: (x == j).
  - exact (imported_eq_to_coq_eq _ _ (sub_add_correspondence _ _ _ _ (Hc x) (cjs_SU_total_suspension Job cR cL Hc suR suL Hsu x))).
  - exact (imported_eq_to_coq_eq _ _ (Hc x)).
Qed.

Lemma cjs_JS_job_jitter :
  CjsParRel Job (@JitterScheduleConstruction.job_jitter Task Job jaR job_task hpR cR j RR) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_job_jitter Task dT Job dJ jaL job_task hpL cL j RL).
Proof.
  intro x. apply: coq_eq_to_imported_eq. rewrite /JitterScheduleConstruction.job_jitter.
  unfold I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_job_jitter.
  rewrite (cjs_ite_bool _ _ _ (ct_bool_and _ _ _ _ (Hhp (job_task x) (job_task j)) (ct_bool_not _ _ (ct_decide_eq Task (job_task x) (job_task j))))).
  case: (hpR (job_task x) (job_task j) && (job_task x != job_task j)).
  - exact (imported_eq_to_coq_eq _ _ (cjs_min_rel _ _ _ _ (ct_sub_rel _ _ _ _ (Hja j) (Hja x)) (ct_sub_rel _ _ _ _ (HR x) (Hc x)))).
  - reflexivity.
Qed.

Notation IC := cjs_JS_inflated_job_cost.
Notation JJ := cjs_JS_job_jitter.

Lemma cjs_JS_pending_jobs_other_than_j sR sL (Hs : CjsSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (@JitterScheduleConstruction.pending_jobs_other_than_j Task Job jaR job_task aR hpR cR suR j RR sR tR)
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_pending_jobs_other_than_j Task dT Job dJ jaL job_task aL hpL cL suL j RL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cjs_AJ_actual_arrivals_up_to Job jaR jaL Hja _ _ JJ aR aL Ha tR tL Ht).
  have F := cl_filter cid _
    (fun j_other => I.Bool_and
       (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_pending Job dJ jaL
          (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_inflated_job_cost Job dJ cL suL j) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_job_jitter Task dT Job dJ jaL job_task hpL cL j RL) sL j_other tL)
       (I.Bool_not (I.Decidable_decide (Lean.eq j_other j) (dJ j_other j))))
    (fun j_other => ct_bool_and _ _ _ _ (cjs_UJ_pending Job sR sL Hs jaR jaL Hja _ _ IC _ _ JJ j_other tR tL Ht)
                     (ct_bool_not _ _ (ct_decide_eq Job j_other j)))
    (ArrivalSequenceWithJitter.actual_arrivals_up_to jaR (@JitterScheduleConstruction.job_jitter Task Job jaR job_task hpR cR j RR) aR tR).
  rewrite -E in F. exact F.
Qed.

Lemma cjs_JS_highest_priority_job_other_than_j sR sL (Hs : CjsSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  Lean.eq (cl_opt (@JitterScheduleConstruction.highest_priority_job_other_than_j Task Job jaR job_task aR hpR cR suR j RR sR tR))
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_highest_priority_job_other_than_j Task dT Job dJ jaL job_task aL hpL cL suL j RL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite /JitterScheduleConstruction.highest_priority_job_other_than_j (cjs_seq_min Job _ _ (cjs_PR_FP_to_JLFP Task Job job_task hpR hpL Hhp)).
  rewrite -(cl_list_logic _ _ _ (cjs_JS_pending_jobs_other_than_j sR sL Hs tR tL Ht)).
  reflexivity.
Qed.

Lemma cjs_JS_build_schedule sR sL (Hs : CjsSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  Lean.eq (cl_opt (@JitterScheduleConstruction.build_schedule Task Job jaR job_task aR hpR cR suR j RR sR tR))
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_build_schedule Task dT Job dJ jaL job_task aL hpL cL suL j RL sL tL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite /JitterScheduleConstruction.build_schedule. unfold I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_build_schedule.
  rewrite (cjs_ite_bool _ _ _ (cjs_UJ_pending Job sR sL Hs jaR jaL Hja _ _ IC _ _ JJ j tR tL Ht)).
  rewrite -(imported_eq_to_coq_eq _ _ (cjs_JS_highest_priority_job_other_than_j sR sL Hs tR tL Ht)).
  case: (UniprocessorScheduleWithJitter.pending jaR (@JitterScheduleConstruction.inflated_job_cost Job cR suR j) (@JitterScheduleConstruction.job_jitter Task Job jaR job_task hpR cR j RR) sR j tR).
  - case: (@JitterScheduleConstruction.highest_priority_job_other_than_j Task Job jaR job_task aR hpR cR suR j RR sR tR) => [jhp|] /=; last reflexivity.
    rewrite (cjs_ite_bool _ _ _ (ct_bool_not _ _ (cjs_PR_FP_to_JLFP Task Job job_task hpR hpL Hhp jhp j))).
    by case: (Priority.FP_to_JLFP job_task hpR jhp j).
  - reflexivity.
Qed.

Lemma cjs_empty : CjsSchedRel Job (fun _ => None) (fun _ => I.Option_none Job).
Proof. intros tR tL Ht. exact (@Lean.eq_refl _ _). Qed.

Lemma cjs_JS_sched_jitter :
  CjsSchedRel Job (@JitterScheduleConstruction.sched_jitter Task Job jaR job_task aR hpR cR suR j RR)
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_sched_jitter Task dT Job dJ jaL job_task aL hpL cL suL j RL).
Proof. exact (cjs_UC_build_schedule_from_prefixes Job _ _ cjs_JS_build_schedule _ _ cjs_empty). Qed.

End JSDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cjs_VS_valid_suspension_aware_schedule (Job : eqType) aR aL (Ha : CjsParRel Job aR aL)
    arrR arrL (Harr : CjsArrRel Job arrR arrL) hR hL (Hh : CjsJldpRel Job hR hL) nR nL (Hn : CjsSuspRel Job nR nL)
    cR cL (Hc : CjsParRel Job cR cL) sR sL (Hs : CjsSchedRel Job sR sL) :
  PropSPropRel (ValidSuspensionAwareSchedule.valid_suspension_aware_schedule aR arrR hR nR cR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Susp_ValidSchedule_ValidSuspensionAwareSchedule_valid_suspension_aware_schedule Job (ct_decidable_eq Job) aL arrL hL nL cL sL).
Proof.
  apply: ct_and; first exact (cjs_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_and; first exact (cjs_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_and; first exact (cjs_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_and; first exact (cjs_SP_work_conserving Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn arrR arrL Harr).
  apply: ct_and; first exact (cjs_SP_respects_JLDP_policy Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn arrR arrL Harr hR hL Hh).
  exact (cjs_SI_respects_self_suspensions Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn).
Qed.

(** Pointwise forms of the constructed cost and jitter functions (for the relation search). *)
Lemma cjs_ijc_pt (Job : eqType) cR cL (Hc : CjsParRel Job cR cL) suR suL (Hsu : CjsSuspRel Job suR suL) j x :
  SubNatRel (@JitterScheduleConstruction.inflated_job_cost Job cR suR j x) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_inflated_job_cost Job (ct_decidable_eq Job) cL suL j x).
Proof. exact (cjs_JS_inflated_job_cost Job cR cL Hc suR suL Hsu j x). Qed.

Lemma cjs_jj_pt (Task Job : eqType) jaR jaL (Hja : CjsParRel Job jaR jaL) (job_task : Job -> Task) hpR hpL (Hhp : CjsRelRel Task hpR hpL)
    cR cL (Hc : CjsParRel Job cR cL) j RR RL (HR : CjsParRel Job RR RL) x :
  SubNatRel (@JitterScheduleConstruction.job_jitter Task Job jaR job_task hpR cR j RR x)
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_job_jitter Task (ct_decidable_eq Task) Job (ct_decidable_eq Job) jaL job_task hpL cL j RL x).
Proof. exact (cjs_JS_job_jitter Task Job jaR jaL Hja job_task hpR hpL Hhp cR cL Hc j RR RL HR x). Qed.

Lemma cjs_SV_service_of_jobs (Job : eqType) sR sL (Hs : CjsSchedRel Job sR sL) jobsR jobsL (Hj : ClListRel cid jobsR jobsL)
    pR pL (Hp : CjsPredRel Job pR pL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.service_of_jobs sR jobsR pR t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs Job (ct_decidable_eq Job) sL jobsL pL t1L t2L).
Proof.
  exact (cjs_sum_filtered_rel Job (fun j => UniprocessorSchedule.service_during sR j t1R t2R)
           (fun j => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job (ct_decidable_eq Job) sL j t1L t2L)
           (fun j => cjs_US_service_during Job sR sL Hs j _ _ H1 _ _ H2) pR pL Hp _ _ Hj).
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
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CjsParRel _ f g |- _ => exact (H x) end
  | |- CtBoolRel (?f ?x ?y) (?g ?x ?y) => match goal with H : CjsRelRel _ f g |- _ => exact (H x y) end
  | |- CtBoolRel (?f ?t ?x ?y) (?g ?u ?x ?y) => match goal with H : CjsJldpRel _ f g |- _ => eapply H end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | ArrivalSequence.arrival_sequence _ => apply: (cjs_forall_arr _); intros ? ? ?
  | UniprocessorSchedule.schedule _ => apply: (cjs_forall_sched _); intros ? ? ?
  | nat -> option _ => apply: (cjs_forall_sched _); intros ? ? ?
  | Priority.FP_policy _ => apply: (cjs_forall_rel _); intros ? ? ?
  | seq _ => apply: (cjs_forall_list _); intros ? ? ?
  | Suspension.job_suspension _ => apply: (cjs_forall_susp _); intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: cjs_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp; crel
  | lazymatch goal with
    | |- forall _, _ => intro; crel
    | |- CjsSchedRel _ (JitterScheduleConstruction.sched_jitter _ _ _ _ _ _ _ _) _ => eapply cjs_JS_sched_jitter; crel
    | |- CjsParRel _ (ArrivalSequenceWithJitter.actual_arrival _ _) _ => intro; eapply cjs_AJ_actual_arrival; crel
    | |- CjsParRel _ (JitterScheduleConstruction.inflated_job_cost _ _ _) _ => eapply cjs_JS_inflated_job_cost; crel
    | |- CjsParRel _ (JitterScheduleConstruction.job_jitter _ _ _ _ _ _) _ => eapply cjs_JS_job_jitter; crel
    | |- CjsJldpRel _ (Priority.FP_to_JLDP _ _) _ => eapply cjs_PR_FP_to_JLDP; crel
    | |- CjsPredRel _ _ _ => intro; cbv beta; crel
    | |- Lean.eq (cl_opt (JitterScheduleConstruction.build_schedule _ _ _ _ _ _ _ _ _ _)) _ => eapply cjs_JS_build_schedule; crel
    | |- Lean.eq (cl_opt (?s _)) _ => first [ match goal with H : CjsSchedRel _ s _ |- _ => eapply H; crel end | eapply cjs_JS_sched_jitter; crel ]
    | |- CjsParRel _ (fun _ => _) _ => intro; cbv beta; crel
    | |- SubNatRel ?a _ => first [ progress (rewrite /JitterScheduleService.workload_of_other_hep_jobs_in_sched_susp /JitterScheduleService.workload_of_other_hep_jobs_in_sched_jitter /JitterScheduleService.service_of_other_hep_jobs_in_sched_susp /JitterScheduleService.service_of_other_hep_jobs_in_sched_jitter; unfold I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_workload_of_other_hep_jobs_in_sched_susp, I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_workload_of_other_hep_jobs_in_sched_jitter, I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_service_of_other_hep_jobs_in_sched_susp, I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_service_of_other_hep_jobs_in_sched_jitter); crel | crel_n a ]
    | |- CtBoolRel ?b _ => crel_b b
    | |- ClListRel _ ?l _ => crel_l l
    | |- PropSPropRel ?P _ => crel_p P
    end ]
with crel_n a :=
  lazymatch a with
  | addn _ _ => eapply sub_add_correspondence; crel
  | subn _ _ => eapply ct_sub_rel; crel
  | S _ => eapply cjs_succ_rel; crel
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
  | _ <-> _ => eapply cjs_iff; crel
  | _ <> _ => eapply cjs_ne
  | ~ _ => eapply ct_imp; [crel | exact cjs_false_rel]
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else crel_eq_defs
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_eq_defs := first [ eapply ct_eq_rel | eapply cjs_opt_rel_eq; crel ]
with crel_n_defs := first [ eapply ct_bool_to_nat; crel
    | eapply cjs_US_service; crel
    | eapply cjs_ijc_pt; crel
    | eapply cjs_jj_pt; crel
    | eapply cjs_US_service_during; crel
    | eapply cjs_WL_workload_of_jobs; crel
    | eapply cjs_SV_service_of_jobs; crel
    | eapply cjs_SI_cumulative_suspension_during; crel
    | eapply cjs_SI_suspension_duration; crel
    | eapply cjs_AJ_actual_arrival; crel
    | eapply cjs_US_service_at; crel ]
with crel_b_defs := first [ eapply cjs_US_scheduled_at; crel
    | eapply cjs_US_completed_by; crel
    | eapply cjs_has_arrived; crel
    | eapply cjs_SI_suspended_at; crel
    | eapply cjs_US_pending; crel
    | eapply cjs_UJ_pending; crel
    | eapply cjs_SS_backlogged; crel
    | eapply cjs_AJ_jitter_has_passed; crel
    | eapply cjs_AJ_actual_arrival_before; crel
    | eapply cjs_arrives_at; crel ]
with crel_l_defs := first [ eapply cjs_jobs_arrived_between; crel
    | eapply cjs_AJ_actual_arrivals_between; crel
    | eapply cjs_jobs_arrived_before; crel ]
with crel_p_defs := first [ eapply cjs_TK_constrained_deadline_model; crel
    | eapply cjs_false_rel; crel
    | eapply cjs_arrives_in; crel
    | eapply cjs_consistent; crel
    | eapply cjs_mem; crel
    | eapply cjs_US_jobs_come_from_arrival_sequence; crel
    | eapply cjs_US_jobs_must_arrive_to_execute; crel
    | eapply cjs_US_completed_jobs_dont_execute; crel
    | eapply cjs_SP_work_conserving; crel
    | eapply cjs_SP_respects_JLDP_policy; crel
    | eapply cjs_SI_respects_self_suspensions; crel
    | eapply cjs_PR_FP_is_reflexive; crel
    | eapply cjs_PR_FP_is_transitive; crel
    | eapply cjs_PR_FP_is_total_over_task_set; crel
    | eapply cjs_VS_valid_suspension_aware_schedule; crel
    | eapply cjs_RT_is_response_time_bound_of_job; crel
    | eapply cjs_TA_sporadic_task_model; crel
    | eapply cjs_is_a_set; crel
    | eapply cjs_uniq; crel ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem JitterScheduleService_workload_of_other_hep_jobs_in_sched_susp_correspondence (Task Job : eqType) cR cL (Hc : CjsParRel Job cR cL) (job_task : Job -> Task) arrR arrL (Harr : CjsArrRel Job arrR arrL) hR hL (Hh : CjsRelRel Task hR hL) j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (@JitterScheduleService.workload_of_other_hep_jobs_in_sched_susp Task Job cR job_task arrR hR j t1R t2R) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_workload_of_other_hep_jobs_in_sched_susp Task (ct_decidable_eq Task) Job (ct_decidable_eq Job) cL job_task arrL hL j t1L t2L).
Proof. crel. Qed.

Theorem JitterScheduleService_workload_of_other_hep_jobs_in_sched_jitter_correspondence (Task Job : eqType) jaR jaL (Hja : CjsParRel Job jaR jaL) cR cL (Hc : CjsParRel Job cR cL) (job_task : Job -> Task) arrR arrL (Harr : CjsArrRel Job arrR arrL) hR hL (Hh : CjsRelRel Task hR hL) suR suL (Hsu : CjsSuspRel Job suR suL) j RR RL (HR : CjsParRel Job RR RL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (@JitterScheduleService.workload_of_other_hep_jobs_in_sched_jitter Task Job jaR cR job_task arrR hR suR j RR t1R t2R) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_workload_of_other_hep_jobs_in_sched_jitter Task (ct_decidable_eq Task) Job (ct_decidable_eq Job) jaL cL job_task arrL hL suL j RL t1L t2L).
Proof. crel. Qed.

Theorem JitterScheduleService_service_of_other_hep_jobs_in_sched_susp_correspondence (Task Job : eqType) jaR jaL (Hja : CjsParRel Job jaR jaL) (job_task : Job -> Task) arrR arrL (Harr : CjsArrRel Job arrR arrL) hR hL (Hh : CjsRelRel Task hR hL) sR sL (Hs : CjsSchedRel Job sR sL) j RjR RjL (HRj : SubNatRel RjR RjL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (@JitterScheduleService.service_of_other_hep_jobs_in_sched_susp Task Job jaR job_task arrR hR sR j RjR t1R t2R) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_service_of_other_hep_jobs_in_sched_susp Task (ct_decidable_eq Task) Job (ct_decidable_eq Job) jaL job_task arrL hL sL j RjL t1L t2L).
Proof. crel. Qed.

Theorem JitterScheduleService_service_of_other_hep_jobs_in_sched_jitter_correspondence (Task Job : eqType) jaR jaL (Hja : CjsParRel Job jaR jaL) cR cL (Hc : CjsParRel Job cR cL) (job_task : Job -> Task) arrR arrL (Harr : CjsArrRel Job arrR arrL) hR hL (Hh : CjsRelRel Task hR hL) suR suL (Hsu : CjsSuspRel Job suR suL) j RjR RjL (HRj : SubNatRel RjR RjL) RR RL (HR : CjsParRel Job RR RL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (@JitterScheduleService.service_of_other_hep_jobs_in_sched_jitter Task Job jaR cR job_task arrR hR suR j RjR RR t1R t2R) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_service_of_other_hep_jobs_in_sched_jitter Task (ct_decidable_eq Task) Job (ct_decidable_eq Job) jaL cL job_task arrL hL suL j RjL RL t1L t2L).
Proof. crel. Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_jitter_reduction_service_equals_workload_in_jitter (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_service_equals_workload_in_jitter Task Job)).
Definition tgt_jitter_reduction_service_equals_workload_in_jitter (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_service_equals_workload_in_jitter Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_service_equals_workload_in_jitter_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_service_equals_workload_in_jitter Task Job) (tgt_jitter_reduction_service_equals_workload_in_jitter Task Job).
Proof. unfold src_jitter_reduction_service_equals_workload_in_jitter, tgt_jitter_reduction_service_equals_workload_in_jitter. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_service_in_sched_susp_le_workload (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_service_in_sched_susp_le_workload Task Job)).
Definition tgt_jitter_reduction_service_in_sched_susp_le_workload (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_service_in_sched_susp_le_workload Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_service_in_sched_susp_le_workload_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_service_in_sched_susp_le_workload Task Job) (tgt_jitter_reduction_service_in_sched_susp_le_workload Task Job).
Proof. unfold src_jitter_reduction_service_in_sched_susp_le_workload, tgt_jitter_reduction_service_in_sched_susp_le_workload. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_less_job_service_before_interval_case1 (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@JitterScheduleService.jitter_reduction_less_job_service_before_interval_case1 Task p0 p1 Job)).
Definition tgt_jitter_reduction_less_job_service_before_interval_case1 (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_less_job_service_before_interval_case1 Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_less_job_service_before_interval_case1_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_less_job_service_before_interval_case1 Task Job) (tgt_jitter_reduction_less_job_service_before_interval_case1 Task Job).
Proof. unfold src_jitter_reduction_less_job_service_before_interval_case1, tgt_jitter_reduction_less_job_service_before_interval_case1. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_less_job_service_before_interval_case2 (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_less_job_service_before_interval_case2 Task Job)).
Definition tgt_jitter_reduction_less_job_service_before_interval_case2 (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_less_job_service_before_interval_case2 Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_less_job_service_before_interval_case2_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_less_job_service_before_interval_case2 Task Job) (tgt_jitter_reduction_less_job_service_before_interval_case2 Task Job).
Proof. unfold src_jitter_reduction_less_job_service_before_interval_case2, tgt_jitter_reduction_less_job_service_before_interval_case2. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_less_job_service_before_interval_case3 (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_less_job_service_before_interval_case3 Task Job)).
Definition tgt_jitter_reduction_less_job_service_before_interval_case3 (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_less_job_service_before_interval_case3 Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_less_job_service_before_interval_case3_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_less_job_service_before_interval_case3 Task Job) (tgt_jitter_reduction_less_job_service_before_interval_case3 Task Job).
Proof. unfold src_jitter_reduction_less_job_service_before_interval_case3, tgt_jitter_reduction_less_job_service_before_interval_case3. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_less_job_service_before_interval_case4 (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_less_job_service_before_interval_case4 Task Job)).
Definition tgt_jitter_reduction_less_job_service_before_interval_case4 (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_less_job_service_before_interval_case4 Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_less_job_service_before_interval_case4_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_less_job_service_before_interval_case4 Task Job) (tgt_jitter_reduction_less_job_service_before_interval_case4 Task Job).
Proof. unfold src_jitter_reduction_less_job_service_before_interval_case4, tgt_jitter_reduction_less_job_service_before_interval_case4. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_jitter_equals_R_minus_cost (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_jitter_equals_R_minus_cost Task Job)).
Definition tgt_jitter_reduction_jitter_equals_R_minus_cost (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_jitter_equals_R_minus_cost Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_jitter_equals_R_minus_cost_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_jitter_equals_R_minus_cost Task Job) (tgt_jitter_reduction_jitter_equals_R_minus_cost Task Job).
Proof. unfold src_jitter_reduction_jitter_equals_R_minus_cost, tgt_jitter_reduction_jitter_equals_R_minus_cost. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_less_job_service_before_interval_case5 (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_less_job_service_before_interval_case5 Task Job)).
Definition tgt_jitter_reduction_less_job_service_before_interval_case5 (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_less_job_service_before_interval_case5 Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_less_job_service_before_interval_case5_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_less_job_service_before_interval_case5 Task Job) (tgt_jitter_reduction_less_job_service_before_interval_case5 Task Job).
Proof. unfold src_jitter_reduction_less_job_service_before_interval_case5, tgt_jitter_reduction_less_job_service_before_interval_case5. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_less_job_service_before_interval (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@JitterScheduleService.jitter_reduction_less_job_service_before_interval Task p0 p1 Job)).
Definition tgt_jitter_reduction_less_job_service_before_interval (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_less_job_service_before_interval Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_less_job_service_before_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_less_job_service_before_interval Task Job) (tgt_jitter_reduction_less_job_service_before_interval Task Job).
Proof. unfold src_jitter_reduction_less_job_service_before_interval, tgt_jitter_reduction_less_job_service_before_interval. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_less_service_before_the_interval (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@JitterScheduleService.jitter_reduction_less_service_before_the_interval Task p0 p1 Job)).
Definition tgt_jitter_reduction_less_service_before_the_interval (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_less_service_before_the_interval Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_less_service_before_the_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_less_service_before_the_interval Task Job) (tgt_jitter_reduction_less_service_before_the_interval Task Job).
Proof. unfold src_jitter_reduction_less_service_before_the_interval, tgt_jitter_reduction_less_service_before_the_interval. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_actual_arrival_before_end_of_interval (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_actual_arrival_before_end_of_interval Task Job)).
Definition tgt_jitter_reduction_actual_arrival_before_end_of_interval (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_actual_arrival_before_end_of_interval Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_actual_arrival_before_end_of_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_actual_arrival_before_end_of_interval Task Job) (tgt_jitter_reduction_actual_arrival_before_end_of_interval Task Job).
Proof. unfold src_jitter_reduction_actual_arrival_before_end_of_interval, tgt_jitter_reduction_actual_arrival_before_end_of_interval. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_workload_conservation_inside_interval (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_workload_conservation_inside_interval Task Job)).
Definition tgt_jitter_reduction_workload_conservation_inside_interval (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_workload_conservation_inside_interval Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_workload_conservation_inside_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_workload_conservation_inside_interval Task Job) (tgt_jitter_reduction_workload_conservation_inside_interval Task Job).
Proof. unfold src_jitter_reduction_workload_conservation_inside_interval, tgt_jitter_reduction_workload_conservation_inside_interval. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_convert_service_to_workload (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_convert_service_to_workload Task Job)).
Definition tgt_jitter_reduction_convert_service_to_workload (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_convert_service_to_workload Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_convert_service_to_workload_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_convert_service_to_workload Task Job) (tgt_jitter_reduction_convert_service_to_workload Task Job).
Proof. unfold src_jitter_reduction_convert_service_to_workload, tgt_jitter_reduction_convert_service_to_workload. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_compare_workload (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_compare_workload Task Job)).
Definition tgt_jitter_reduction_compare_workload (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_compare_workload Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_compare_workload_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_compare_workload Task Job) (tgt_jitter_reduction_compare_workload Task Job).
Proof. unfold src_jitter_reduction_compare_workload, tgt_jitter_reduction_compare_workload. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_compare_service (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@JitterScheduleService.jitter_reduction_compare_service Task p0 p1 Job)).
Definition tgt_jitter_reduction_compare_service (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_compare_service Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_compare_service_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_compare_service Task Job) (tgt_jitter_reduction_compare_service Task Job).
Proof. unfold src_jitter_reduction_compare_service, tgt_jitter_reduction_compare_service. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_convert_workload_to_service (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_convert_workload_to_service Task Job)).
Definition tgt_jitter_reduction_convert_workload_to_service (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_convert_workload_to_service Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_convert_workload_to_service_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_convert_workload_to_service Task Job) (tgt_jitter_reduction_convert_workload_to_service Task Job).
Proof. unfold src_jitter_reduction_convert_workload_to_service, tgt_jitter_reduction_convert_workload_to_service. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_inductive_step_case1 (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@JitterScheduleService.jitter_reduction_inductive_step_case1 Task p0 p1 Job)).
Definition tgt_jitter_reduction_inductive_step_case1 (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_inductive_step_case1 Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_inductive_step_case1_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_inductive_step_case1 Task Job) (tgt_jitter_reduction_inductive_step_case1 Task Job).
Proof. unfold src_jitter_reduction_inductive_step_case1, tgt_jitter_reduction_inductive_step_case1. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_inductive_step_case2 (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_inductive_step_case2 Task Job)).
Definition tgt_jitter_reduction_inductive_step_case2 (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_inductive_step_case2 Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_inductive_step_case2_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_inductive_step_case2 Task Job) (tgt_jitter_reduction_inductive_step_case2 Task Job).
Proof. unfold src_jitter_reduction_inductive_step_case2, tgt_jitter_reduction_inductive_step_case2. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_more_service_inside_the_interval (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@JitterScheduleService.jitter_reduction_more_service_inside_the_interval Task p0 p1 Job)).
Definition tgt_jitter_reduction_more_service_inside_the_interval (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_more_service_inside_the_interval Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_more_service_inside_the_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_more_service_inside_the_interval Task Job) (tgt_jitter_reduction_more_service_inside_the_interval Task Job).
Proof. unfold src_jitter_reduction_more_service_inside_the_interval, tgt_jitter_reduction_more_service_inside_the_interval. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_service_jitter (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_service_jitter Task Job)).
Definition tgt_jitter_reduction_service_jitter (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_service_jitter Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_service_jitter_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_service_jitter Task Job) (tgt_jitter_reduction_service_jitter Task Job).
Proof. unfold src_jitter_reduction_service_jitter, tgt_jitter_reduction_service_jitter. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_service_susp (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleService.jitter_reduction_service_susp Task Job)).
Definition tgt_jitter_reduction_service_susp (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_service_susp Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_service_susp_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_service_susp Task Job) (tgt_jitter_reduction_service_susp Task Job).
Proof. unfold src_jitter_reduction_service_susp, tgt_jitter_reduction_service_susp. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_less_service_for_job_j (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@JitterScheduleService.jitter_reduction_less_service_for_job_j Task p0 p1 Job)).
Definition tgt_jitter_reduction_less_service_for_job_j (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_less_service_for_job_j Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_less_service_for_job_j_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_less_service_for_job_j Task Job) (tgt_jitter_reduction_less_service_for_job_j Task Job).
Proof. unfold src_jitter_reduction_less_service_for_job_j, tgt_jitter_reduction_less_service_for_job_j. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jitter_reduction_job_j_completes_no_later (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@JitterScheduleService.jitter_reduction_job_j_completes_no_later Task p0 p1 Job)).
Definition tgt_jitter_reduction_job_j_completes_no_later (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleService_JitterScheduleService_jitter_reduction_job_j_completes_no_later Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem JitterScheduleService_jitter_reduction_job_j_completes_no_later_correspondence (Task Job : eqType) :
  PropSPropRel (src_jitter_reduction_job_j_completes_no_later Task Job) (tgt_jitter_reduction_job_j_completes_no_later Task Job).
Proof. unfold src_jitter_reduction_job_j_completes_no_later, tgt_jitter_reduction_job_j_completes_no_later. crel_spine. crel. Unshelve. all: crel. Qed.
