From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.minmax classic.model.suspension classic.model.priority classic.model.arrival.basic.arrival_sequence classic.model.arrival.jitter.arrival_sequence classic.model.schedule.uni.schedule classic.model.schedule.uni.jitter.schedule classic.model.schedule.uni.transformation.construction classic.analysis.uni.susp.dynamic.jitter.jitter_schedule classic.model.schedule.uni.response_time classic.model.schedule.uni.jitter.valid_schedule classic.model.schedule.uni.jitter.platform classic.model.schedule.uni.susp.last_execution classic.model.schedule.uni.susp.suspension_intervals classic.model.schedule.uni.susp.schedule classic.model.schedule.uni.susp.valid_schedule classic.model.schedule.uni.susp.platform classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicJitterSchedProps.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicJitterSchedPropsBase ClassicJitterSchedPropsList ClassicJitterSchedPropsOrd.



Module I := ImportedClassicJitterSchedProps.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/uni/susp/dynamic/jitter/jitter_schedule_properties.v] (ProsaBuddy classic, commit f692cb7).

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

Lemma cjq_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cjq_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cjq_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cjq_false_rel). Qed.

Lemma cjq_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cjq_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cjq_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cjq_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cjq_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cjq_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cjq_unmap_rel T l) PR PL).
Qed.

Definition CjqParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cjq_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CjqParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cjq_forall_cover _ _ (CjqParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cjq_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cjq_natl s') end.

Definition cjq_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cjq_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cjq_one) (cjq_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cjq_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cjq_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cjq_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cjq_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cjq_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cjq_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cjq_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cjq_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cjq_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cjq_cl_append. reflexivity.
Qed.

Lemma cjq_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CjqFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cjq_bigcat_rel (A : Type) fR fL (Hf : CjqFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterSchedPropsInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cjq_iota_range (nR - mR) 0) cjq_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cjq_cl_map_ext _ _ Hpt) (cjq_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cjq_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cjq_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CjqArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cjq_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cjq_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cjq_arr_canonical aR : CjqArrRel aR (cjq_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cjq_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cjq_arr_surjective aL : CjqArrRel (cjq_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cjq_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CjqArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cjq_forall_cover _ _ CjqArrRel cjq_arr_to_target cjq_arr_to_source cjq_arr_canonical cjq_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cjq_jobs_arrived_between aR aL (Ha : CjqArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cjq_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cjq_arrives_in aR aL (Ha : CjqArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cjq_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cjq_consistent pR pL (Hp : CjqParRel Job pR pL) aR aL (Ha : CjqArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cjq_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cjq_jobs_arrived_before aR aL (Ha : CjqArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job dJ aL tL).
Proof. exact (cjq_jobs_arrived_between Job aR aL Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma cjq_arrives_at aR aL (Ha : CjqArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cjq_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma cjq_has_arrived pR pL (Hp : CjqParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cjq_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cjq_snatl s') end.

Lemma cjq_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cjq_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cjq_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cjq_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cjq_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cjq_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cjq_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CjqFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cjq_fun_canonical FR FL (HF : CjqFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cjq_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cjq_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CjqFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cjq_nat_sub_canonical nR mR.
  rewrite cjq_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cjq_foldr_add FL FR (cjq_fun_canonical FR FL HF)).
  by rewrite cjq_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cjq_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cjq_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cjq_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cjq_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cjq_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CjqSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cjq_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cjq_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cjq_sched_canonical sR : CjqSchedRel sR (cjq_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cjq_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cjq_sched_surjective sL : CjqSchedRel (cjq_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cjq_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cjq_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CjqSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cjq_forall_cover _ _ CjqSchedRel cjq_sched_to_target cjq_sched_to_source cjq_sched_canonical cjq_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cjq_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CjqSchedRel Job sR (cjq_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CjqSchedRel Job (cjq_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cjq_sched_canonical Job) (cjq_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjqSchedRel Job sR sL.

Lemma cjq_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cjq_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cjq_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cjq_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cjq_US_scheduled_at j tR tL Ht)). Qed.

Lemma cjq_service_at_fun j : CjqFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cjq_US_service_at j kR kL Hk). Qed.

Lemma cjq_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cjq_ico _ _ _ _ _ _ H1 H2 (cjq_service_at_fun j)). Qed.

Lemma cjq_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cjq_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cjq_US_completed_by cR cL (Hc : CjqParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cjq_US_service j tR tL Ht)). Qed.

Lemma cjq_US_pending aR aL (Ha : CjqParRel Job aR aL) cR cL (Hc : CjqParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cjq_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cjq_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cjq_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CjqArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cjq_US_scheduled_at j tR tL Ht)).
  exact (cjq_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cjq_US_jobs_must_arrive_to_execute aR aL (Ha : CjqParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cjq_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cjq_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma cjq_US_completed_jobs_dont_execute cR cL (Hc : CjqParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cjq_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

Section SuspSusp.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSusp := (I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).

Definition CjqSuspRel (sR : Suspension.job_suspension Job) (sL : LSusp) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (sR j tR) (sL j tL).

Definition cjq_susp_to_target (sR : Suspension.job_suspension Job) : LSusp :=
  fun j tL => sub_nat_to_imported (sR j (sub_nat_to_rocq tL)).

Definition cjq_susp_to_source (sL : LSusp) : Suspension.job_suspension Job :=
  fun j tR => sub_nat_to_rocq (sL j (sub_nat_to_imported tR)).

Lemma cjq_susp_canonical sR : CjqSuspRel sR (cjq_susp_to_target sR).
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  unfold cjq_susp_to_target. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma cjq_susp_surjective sL : CjqSuspRel (cjq_susp_to_source sL) sL.
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma cjq_forall_susp (PR : Suspension.job_suspension Job -> Prop) (PL : LSusp -> SProp) :
  (forall sR sL, CjqSuspRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cjq_forall_cover _ _ CjqSuspRel cjq_susp_to_target cjq_susp_to_source cjq_susp_canonical cjq_susp_surjective PR PL). Qed.

End SuspSusp.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cjq_SU_job_suspension (Job : eqType) :
  And (forall sR : Suspension.job_suspension Job, CjqSuspRel Job sR (cjq_susp_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job (ct_decidable_eq Job), CjqSuspRel Job (cjq_susp_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cjq_susp_canonical Job) (cjq_susp_surjective Job)). Qed.

Lemma cjq_SU_total_suspension (Job : eqType) cR cL (Hc : CjqParRel Job cR cL) sR sL (Hs : CjqSuspRel Job sR sL) j :
  SubNatRel (Suspension.total_suspension cR sR j) (I.Prosa_Classic_Model_Suspension_Suspension_total_suspension Job (ct_decidable_eq Job) cL sL j).
Proof. exact (cjq_ico 0 _ (cR j) (cL j) (sR j) (sL j) (sub_nat_rel_canonical 0) (Hc j) (Hs j)). Qed.

(** The imported [ArrivalSequenceWithJitter] definitions (as in the accepted classic jitter arrival_sequence certificate). *)
Section JitterArrDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cjq_AJ_actual_arrival pR pL (Hp : CjqParRel Job pR pL) qR qL (Hq : CjqParRel Job qR qL) j :
  SubNatRel (ArrivalSequenceWithJitter.actual_arrival pR qR j) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Hp j) (Hq j)). Qed.

Lemma cjq_AJ_jitter_has_passed pR pL (Hp : CjqParRel Job pR pL) qR qL (Hq : CjqParRel Job qR qL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequenceWithJitter.jitter_has_passed pR qR j tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_jitter_has_passed Job dJ pL qL j tL).
Proof. exact (ct_decide_le _ _ _ _ (cjq_AJ_actual_arrival pR pL Hp qR qL Hq j) Ht). Qed.

Lemma cjq_AJ_actual_arrivals_between pR pL (Hp : CjqParRel Job pR pL) qR qL (Hq : CjqParRel Job qR qL)
    aR aL (Ha : CjqArrRel Job aR aL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_between pR qR aR t1R t2R) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_between Job dJ pL qL aL t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cjq_jobs_arrived_before Job aR aL Ha t2R t2L H2).
  have F := cl_filter cid _
              (fun j => I.Bool_and
                 (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j))
                    (I.Nat_decLe t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j)))
                 (I.Decidable_decide (I.LT_lt_inst1 Lean.Nat I.instLTNat (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)
                    (I.Nat_decLt (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)))
              (fun j => ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (cjq_AJ_actual_arrival pR pL Hp qR qL Hq j))
                                          (ct_decide_lt _ _ _ _ (cjq_AJ_actual_arrival pR pL Hp qR qL Hq j) H2))
              (ArrivalSequence.jobs_arrived_before aR t2R).
  rewrite -E in F. exact F.
Qed.

Lemma cjq_AJ_actual_arrivals_up_to pR pL (Hp : CjqParRel Job pR pL) qR qL (Hq : CjqParRel Job qR qL)
    aR aL (Ha : CjqArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_up_to pR qR aR tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_up_to Job dJ pL qL aL tL).
Proof. exact (cjq_AJ_actual_arrivals_between pR pL Hp qR qL Hq aR aL Ha 0 _ (sub_nat_rel_canonical 0) tR.+1 _ (cjq_succ_rel tR tL Ht)). Qed.

End JitterArrDefs.

Section UjschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjqSchedRel Job sR sL.

Lemma cjq_UJ_pending aR aL (Ha : CjqParRel Job aR aL) cR cL (Hc : CjqParRel Job cR cL)
    jjR jjL (Hjj : CjqParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.pending aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_pending Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cjq_AJ_jitter_has_passed Job aR aL Ha jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cjq_US_completed_by Job sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

Lemma cjq_UJ_backlogged aR aL (Ha : CjqParRel Job aR aL) cR cL (Hc : CjqParRel Job cR cL)
    jjR jjL (Hjj : CjqParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.backlogged aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_backlogged Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cjq_UJ_pending aR aL Ha cR cL Hc jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cjq_US_scheduled_at Job sR sL Hs j tR tL Ht))).
Qed.

Lemma cjq_UJ_jobs_execute_after_jitter aR aL (Ha : CjqParRel Job aR aL) jjR jjL (Hjj : CjqParRel Job jjR jjL) :
  PropSPropRel (UniprocessorScheduleWithJitter.jobs_execute_after_jitter aR jjR sR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_jobs_execute_after_jitter Job dJ aL jjL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cjq_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (cjq_AJ_jitter_has_passed Job aR aL Ha jjR jjL Hjj j tR tL Ht)).
Qed.

End UjschedDefs.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CjqRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cjq_rel_canonical (T : Type) (rR : T -> T -> bool) : CjqRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cjq_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CjqRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cjq_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CjqRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cjq_forall_cover _ _ (CjqRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cjq_rel_canonical T) (cjq_rel_surjective T) PR PL).
Qed.

Definition CjqJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CjqRelRel T (rR tR) (rL tL).

Lemma cjq_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CjqJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cjq_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CjqJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cjq_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CjqJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cjq_forall_cover _ _ (CjqJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cjq_jldp_canonical T) (cjq_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cjq_PR_FP_policy :
  And (forall rR : Priority.FP_policy Task, CjqRelRel Task rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_FP_policy Task dT, CjqRelRel Task (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cjq_rel_canonical Task) (cjq_rel_surjective Task)). Qed.

Lemma cjq_PR_JLFP_policy :
  And (forall rR : Priority.JLFP_policy Job, CjqRelRel Job rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLFP_policy Job dJ, CjqRelRel Job (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cjq_rel_canonical Job) (cjq_rel_surjective Job)). Qed.

Lemma cjq_PR_JLDP_policy :
  And (forall rR : Priority.JLDP_policy Job, CjqJldpRel Job rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLDP_policy Job dJ,
         CjqJldpRel Job (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL).
Proof. exact (And_intro _ _ (cjq_jldp_canonical Job) (cjq_jldp_surjective Job)). Qed.

Lemma cjq_PR_FP_to_JLFP (job_task : Job -> Task) rR rL (Hr : CjqRelRel Task rR rL) :
  CjqRelRel Job (Priority.FP_to_JLFP job_task rR)
    (I.Prosa_Classic_Model_Priority_Priority_FP_to_JLFP Task Job dT dJ job_task rL).
Proof. intros a b. exact (Hr (job_task a) (job_task b)). Qed.

Lemma cjq_PR_FP_to_JLDP (job_task : Job -> Task) rR rL (Hr : CjqRelRel Task rR rL) :
  CjqJldpRel Job (Priority.FP_to_JLDP job_task rR)
    (I.Prosa_Classic_Model_Priority_Priority_FP_to_JLDP Task Job dT dJ job_task rL).
Proof. intros tR tL _ a b. exact (Hr (job_task a) (job_task b)). Qed.

Lemma cjq_reflexive (T : Type) rR rL (Hr : CjqRelRel T rR rL) :
  PropSPropRel (reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_reflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (Hr x x)). Qed.

Lemma cjq_transitive (T : Type) rR rL (Hr : CjqRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma cjq_PR_FP_is_reflexive rR rL (Hr : CjqRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_reflexive Task dT rL).
Proof. exact (cjq_reflexive Task rR rL Hr). Qed.

Lemma cjq_PR_FP_is_transitive rR rL (Hr : CjqRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_transitive Task dT rL).
Proof. exact (cjq_transitive Task rR rL Hr). Qed.

Lemma cjq_PR_FP_is_total_over_task_set rR rL (Hr : CjqRelRel Task rR rL) ts tsL (Hts : ClListRel cid ts tsL) :
  PropSPropRel (Priority.FP_is_total_over_task_set rR ts)
    (I.Prosa_Classic_Model_Priority_Priority_FP_is_total_over_task_set Task dT rL tsL).
Proof.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: ct_imp; first exact (cjq_mem Task x1 ts tsL Hts).
  apply: ct_imp; first exact (cjq_mem Task x2 ts tsL Hts).
  exact (ct_or _ _ _ _ (ct_bool_truth _ _ (Hr x1 x2)) (ct_bool_truth _ _ (Hr x2 x1))).
Qed.

End PriodefsDefs.

(* ------------------------------------------------------------------ *)
(** * [seq_min] (as in the accepted classic minmax certificate) *)

Lemma cjq_opt_eq {A} (o1 o2 : option A) : PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
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

Lemma cjq_argmin_step x l :
  Logic.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (I.List_cons T1 x l))
    (I.Prosa_Classic_Util_Minmax_seq_argmin_match_1 T1 (fun _ => I.Option T1)
       (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL l)
       (fun y => I.ite (I.Option T1) (Lean.eq (relL (FL x) (FL y)) I.Bool_true) (I.instDecidableEqBool (relL (FL x) (FL y)) I.Bool_true)
                   (I.Option_some T1 x) (I.Option_some T1 y))
       (fun _ => I.Option_some T1 x)).
Proof. reflexivity. Qed.

Lemma cjq_argmin_rel : forall l,
  Logic.eq (cl_opt (seq_argmin relR FR l)) (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (cl_map cid l)).
Proof.
  elim => [|x l IH] //=. rewrite cjq_argmin_step -IH.
  case: (seq_argmin relR FR l) => [y|] //=.
  rewrite (ct_bool_rel_logic _ _ (Hcomp x y)). by case: (relR (FR x) (FR y)).
Qed.

Lemma cjq_argmin_eq l L (H : ClListRel cid l L) o :
  PropSPropRel (Logic.eq (seq_argmin relR FR l) o)
    (Lean.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL L) (cl_opt o)).
Proof. destruct H. rewrite -cjq_argmin_rel. exact (cjq_opt_eq _ _). Qed.

End MinmaxArg.

Lemma cjq_seq_min (T : eqType) relR relL (Hrel : forall a b, CtBoolRel (relR a b) (relL a b)) l :
  Logic.eq (cl_opt (seq_min relR l)) (I.Prosa_Classic_Util_Minmax_seq_min T (ct_decidable_eq T) relL (cl_map cid l)).
Proof. exact (cjq_argmin_rel T T T (ct_decidable_eq T) relR relL (@Datatypes.id T) (I.id T) (fun x y => Hrel _ _) l). Qed.

(* ------------------------------------------------------------------ *)
(** * Options *)

Lemma cjq_opt_rel_eq (A : Type) (o1 o2 : option A) l1 l2 :
  Lean.eq (cl_opt o1) l1 -> Lean.eq (cl_opt o2) l2 -> PropSPropRel (Logic.eq o1 o2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. destruct H1. destruct H2. apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cjq_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Definition cjq_lsym {A : Type} {x y : A} (E : Lean.eq x y) : Lean.eq y x :=
  match E in Lean.eq _ z return Lean.eq z x with Lean.eq_refl => @Lean.eq_refl _ _ end.

Lemma cjq_src_transport {A : Type} (P : A -> SProp) (x y : A) : Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

Lemma cjq_nat_input (nR : nat) (nL : Lean.Nat) : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
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
Hypothesis Hbuild : forall sR sL, CjqSchedRel Job sR sL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (buildR sR tR)) (buildL sL tL).
Variables (baseR : UniprocessorSchedule.schedule Job) (baseL : LSched).
Hypothesis Hbase : CjqSchedRel Job baseR baseL.

Lemma cjq_nat_eqb tR tL t'R t'L : SubNatRel tR tL -> SubNatRel t'R t'L ->
  CtBoolRel (tR == t'R) (I.Decidable_decide (Lean.eq tL t'L) (I.instDecidableEqNat tL t'L)).
Proof. intros Ht Ht'. exact (ct_decide_eq_nat _ _ _ _ Ht Ht'). Qed.

Lemma cjq_UC_update_schedule prevR prevL (Hprev : CjqSchedRel Job prevR prevL) nR nL (Hn : SubNatRel nR nL) :
  CjqSchedRel Job (@ScheduleConstruction.update_schedule Job buildR prevR nR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule Job dJ buildL prevL nL).
Proof.
  intros tR tL Ht. unfold ScheduleConstruction.update_schedule, I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule. cbv beta.
  apply: coq_eq_to_imported_eq.
  rewrite (ct_bool_rel_logic _ _ (cjq_nat_eqb tR tL nR nL Ht Hn)).
  case: (tR == nR).
  - exact (imported_eq_to_coq_eq _ _ (Hbuild prevR prevL Hprev tR tL Ht)).
  - exact (imported_eq_to_coq_eq _ _ (Hprev tR tL Ht)).
Qed.

Lemma cjq_prefix_canonical (mR : nat) :
  CjqSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL (sub_nat_to_imported mR)).
Proof.
  induction mR as [|m IH].
  - refine (cjq_trs (cjq_lsym (I.Prosa_Validation_ClassicJitterSchedPropsInterface_production_schedule_prefix_zero Job dJ buildL baseL))
              (fun z => CjqSchedRel Job _ z) _).
    exact (cjq_UC_update_schedule baseR baseL Hbase 0 _ (sub_nat_rel_canonical 0)).
  - assert (Hm1 : SubNatRel m.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
                                 (sub_nat_to_imported m) (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)))).
    { exact (cjq_src_transport (fun x => SubNatRel x _) _ _ (addn1 m)
               (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical 1))). }
    refine (cjq_trs Hm1 (fun z => CjqSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR m.+1) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) _).
    refine (cjq_trs (cjq_lsym (I.Prosa_Validation_ClassicJitterSchedPropsInterface_production_schedule_prefix_succ Job dJ buildL baseL (sub_nat_to_imported m)))
              (fun z => CjqSchedRel Job _ z) _).
    exact (cjq_UC_update_schedule _ _ IH _ _ Hm1).
Qed.

Lemma cjq_UC_schedule_prefix mR mL (Hm : SubNatRel mR mL) :
  CjqSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL mL).
Proof. exact (cjq_trs Hm (fun z => CjqSchedRel Job _ (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) (cjq_prefix_canonical mR)). Qed.

Lemma cjq_UC_build_schedule_from_prefixes :
  CjqSchedRel Job (@ScheduleConstruction.build_schedule_from_prefixes Job buildR baseR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_build_schedule_from_prefixes Job dJ buildL baseL).
Proof. intros tR tL Ht. exact (cjq_UC_schedule_prefix tR tL Ht tR tL Ht). Qed.

End UconsConstruction.

Section UjplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjqSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (jjR : Job -> nat) (jjL : Job -> Lean.Nat).
Hypotheses (Ha : CjqParRel Job aR aL) (Hc : CjqParRel Job cR cL) (Hjj : CjqParRel Job jjR jjL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CjqArrRel Job arrR arrL.

Notation SA := (cjq_US_scheduled_at Job sR sL Hs).

Lemma cjq_UJP_work_conserving :
  PropSPropRel (Platform.work_conserving aR cR jjR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Platform_Platform_work_conserving Job dJ aL cL jjL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cjq_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ ((cjq_UJ_backlogged Job sR sL Hs aR aL Ha cR cL Hc jjR jjL Hjj) j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (SA j_other tR tL Ht)).
Qed.

Lemma cjq_UJP_respects_FP_policy (job_task : Job -> Task) hR hL (Hh : CjqRelRel Task hR hL) :
  PropSPropRel (Platform.respects_FP_policy aR cR jjR job_task arrR sR hR)
    (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Platform_Platform_respects_FP_policy Task dT Job dJ aL cL jjL job_task arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cjq_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ ((cjq_UJ_backlogged Job sR sL Hs aR aL Ha cR cL Hc jjR jjL Hjj) j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh (job_task j_hp) (job_task j))).
Qed.

Lemma cjq_UJP_respects_JLDP_policy hR hL (Hh : CjqJldpRel Job hR hL) :
  PropSPropRel (Platform.respects_JLDP_policy aR cR jjR arrR sR hR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Platform_Platform_respects_JLDP_policy Job dJ aL cL jjL arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cjq_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ ((cjq_UJ_backlogged Job sR sL Hs aR aL Ha cR cL Hc jjR jjL Hjj) j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh tR tL Ht j_hp j)).
Qed.

End UjplatDefs.

(** * [\max] over ordinals against [maxFiltered] over [List.finRange] *)

Lemma cjq_foldr_max (f : Lean.Nat -> Lean.Nat) (g : nat -> nat)
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

Lemma cjq_max_rel nR nL (Hn : SubNatRel nR nL) (QR : 'I_nR -> bool) (QL : Fin nL -> I.Bool) (HQ : CoOrdPredRel nR nL QR QL) :
  SubNatRel (\max_(i < nR | QR i) nat_of_ord i)
    (I.Prosa_Util_Sum_maxFiltered_inst1 (Fin nL) (I.List_finRange nL) QL (fun o => I.Fin_val nL o)).
Proof.
  have E := co_nat_logic _ _ Hn. subst nL. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicJitterSchedPropsInterface_maxFiltered_finRange
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
  exact (cjq_foldr_max _ _ (co_fam_related nR sub_nat_to_imported (fun i => if QR i then nat_of_ord i else 0)
           (fun oL => I.cond Lean.Nat (QL oL) (I.Fin_val _ oL) (sub_nat_to_imported 0)) 0 HF) (iota 0 nR)).
Qed.

Lemma cjq_ite_rel bR bL (Hb : CtBoolRel bR bL) xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) :
  SubNatRel (if bR then xR else yR)
    (I.ite Lean.Nat (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) xL yL).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). destruct bR; [exact Hx | exact Hy]. Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cjq_LE_time_after_last_execution (Job : eqType) aR aL (Ha : CjqParRel Job aR aL)
    sR sL (Hs : CjqSchedRel Job sR sL) j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (LastExecution.time_after_last_execution aR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Susp_LastExecution_LastExecution_time_after_last_execution Job (ct_decidable_eq Job) aL sL j tL).
Proof.
  assert (HQ : CoOrdPredRel tR tL (fun o => UniprocessorSchedule.scheduled_at sR j o)
      (fun oL => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job (ct_decidable_eq Job) sL j (I.Fin_val tL oL))).
  { intros o oL Ho. exact (cjq_US_scheduled_at Job sR sL Hs j _ _ Ho). }
  exact (cjq_ite_rel _ _ (co_exists_rel tR tL Ht _ _ HQ) _ _
           (sub_add_correspondence _ _ _ _ (cjq_max_rel tR tL Ht _ _ HQ) (sub_nat_rel_canonical 1)) _ _ (Ha j)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Section SuspintDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjqSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CjqParRel Job aR aL) (Hc : CjqParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CjqSuspRel Job nR nL.

Lemma cjq_SI_suspension_duration j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (SuspensionIntervals.suspension_duration aR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspension_duration Job dJ aL nL sL j tL).
Proof. exact (Hn j _ _ (cjq_US_service Job sR sL Hs j _ _ ((cjq_LE_time_after_last_execution Job aR aL Ha sR sL Hs) j tR tL Ht))). Qed.

Lemma cjq_SI_suspended_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (SuspensionIntervals.suspended_at aR cR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspended_at Job dJ aL cL nL sL j tL).
Proof.
  have HT := (cjq_LE_time_after_last_execution Job aR aL Ha sR sL Hs) j tR tL Ht.
  exact (ct_bool_and _ _ _ _ (ct_bool_not _ _ (cjq_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht))
           (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ HT Ht)
              (ct_decide_lt _ _ _ _ Ht (sub_add_correspondence _ _ _ _ HT (cjq_SI_suspension_duration j tR tL Ht))))).
Qed.

Lemma cjq_SI_respects_self_suspensions :
  PropSPropRel (SuspensionIntervals.respects_self_suspensions aR cR nR sR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_respects_self_suspensions Job dJ aL cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cjq_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (cjq_SI_suspended_at j tR tL Ht)) cjq_false_rel).
Qed.

End SuspintDefs.

Section SuspschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjqSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CjqParRel Job aR aL) (Hc : CjqParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CjqSuspRel Job nR nL.

Lemma cjq_SS_backlogged j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithSuspensions.backlogged aR cR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Schedule_ScheduleWithSuspensions_backlogged Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _
           (ct_bool_and _ _ _ _ (cjq_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)
              (ct_bool_not _ _ (cjq_US_scheduled_at Job sR sL Hs j _ _ Ht)))
           (ct_bool_not _ _ (cjq_SI_suspended_at Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn j _ _ Ht))).
Qed.

End SuspschedDefs.

Section SuspplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjqSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CjqParRel Job aR aL) (Hc : CjqParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CjqSuspRel Job nR nL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CjqArrRel Job arrR arrL.

Notation SA := (cjq_US_scheduled_at Job sR sL Hs).

Lemma cjq_SP_work_conserving :
  PropSPropRel (PlatformWithSuspensions.work_conserving aR cR nR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Platform_PlatformWithSuspensions_work_conserving Job dJ aL cL nL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cjq_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ ((cjq_SS_backlogged Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn) j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (SA j_other tR tL Ht)).
Qed.

Lemma cjq_SP_respects_JLDP_policy hR hL (Hh : CjqJldpRel Job hR hL) :
  PropSPropRel (PlatformWithSuspensions.respects_JLDP_policy aR cR nR arrR sR hR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Platform_PlatformWithSuspensions_respects_JLDP_policy Job dJ aL cL nL arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cjq_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ ((cjq_SS_backlogged Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn) j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh tR tL Ht j_hp j)).
Qed.

End SuspplatDefs.

Section UrtDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CjqSchedRel Job sR sL.

End UrtDefs.

Lemma cjq_iff (P Q : Prop) (PL QL : SProp) :
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
(** * Auxiliary relations *)

(** [minn] against the core [Min.min] on [Nat] (as in the accepted classic global workload_bound certificate). *)
Lemma cjq_min_canonical (a b : nat) :
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

Lemma cjq_min_rel aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel (minn aR bR) ((I.Min_min_inst1 Lean.Nat I.instMinNat) aL bL).
Proof.
  intros Ha Hb. rewrite -(imported_eq_to_coq_eq _ _ Ha) -(imported_eq_to_coq_eq _ _ Hb).
  apply: coq_eq_to_imported_eq. exact (Logic.eq_sym (cjq_min_canonical aR bR)).
Qed.

(** A Rocq Boolean equality test against the Lean [if x = y] on the canonical [DecidableEq] instance. *)
Lemma cjq_ite_eq (J : eqType) (A : Type) (x y : J) (a b : A) :
  Logic.eq (I.ite A (Lean.eq x y) (ct_decidable_eq J x y) a b) (if x == y then a else b).
Proof. rewrite /ct_decidable_eq. by case: (@eqP J x y). Qed.

(** A Boolean [if] against the Lean [if b = true]. *)
Lemma cjq_ite_bool (A : Type) bR bL (Hb : CtBoolRel bR bL) (a b : A) :
  Logic.eq (I.ite A (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) a b) (if bR then a else b).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). clear Hb. by case: bR. Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JSDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat).
Hypothesis Hja : CjqParRel Job jaR jaL.
Variable job_task : Job -> Task.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CjqArrRel Job aR aL.
Variables (hpR : Task -> Task -> bool) (hpL : Task -> Task -> I.Bool).
Hypothesis Hhp : CjqRelRel Task hpR hpL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CjqParRel Job cR cL.
Variables (suR : Suspension.job_suspension Job) (suL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hsu : CjqSuspRel Job suR suL.
Variable j : Job.
Variables (RR : Job -> nat) (RL : Job -> Lean.Nat).
Hypothesis HR : CjqParRel Job RR RL.

Lemma cjq_JS_inflated_job_cost :
  CjqParRel Job (@JitterScheduleConstruction.inflated_job_cost Job cR suR j) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_inflated_job_cost Job dJ cL suL j).
Proof.
  intro x. apply: coq_eq_to_imported_eq. rewrite /JitterScheduleConstruction.inflated_job_cost.
  unfold I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_inflated_job_cost. rewrite cjq_ite_eq.
  case: (x == j).
  - exact (imported_eq_to_coq_eq _ _ (sub_add_correspondence _ _ _ _ (Hc x) (cjq_SU_total_suspension Job cR cL Hc suR suL Hsu x))).
  - exact (imported_eq_to_coq_eq _ _ (Hc x)).
Qed.

Lemma cjq_JS_job_jitter :
  CjqParRel Job (@JitterScheduleConstruction.job_jitter Task Job jaR job_task hpR cR j RR) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_job_jitter Task dT Job dJ jaL job_task hpL cL j RL).
Proof.
  intro x. apply: coq_eq_to_imported_eq. rewrite /JitterScheduleConstruction.job_jitter.
  unfold I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_job_jitter.
  rewrite (cjq_ite_bool _ _ _ (ct_bool_and _ _ _ _ (Hhp (job_task x) (job_task j)) (ct_bool_not _ _ (ct_decide_eq Task (job_task x) (job_task j))))).
  case: (hpR (job_task x) (job_task j) && (job_task x != job_task j)).
  - exact (imported_eq_to_coq_eq _ _ (cjq_min_rel _ _ _ _ (ct_sub_rel _ _ _ _ (Hja j) (Hja x)) (ct_sub_rel _ _ _ _ (HR x) (Hc x)))).
  - reflexivity.
Qed.

Notation IC := cjq_JS_inflated_job_cost.
Notation JJ := cjq_JS_job_jitter.

Lemma cjq_JS_pending_jobs_other_than_j sR sL (Hs : CjqSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (@JitterScheduleConstruction.pending_jobs_other_than_j Task Job jaR job_task aR hpR cR suR j RR sR tR)
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_pending_jobs_other_than_j Task dT Job dJ jaL job_task aL hpL cL suL j RL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cjq_AJ_actual_arrivals_up_to Job jaR jaL Hja _ _ JJ aR aL Ha tR tL Ht).
  have F := cl_filter cid _
    (fun j_other => I.Bool_and
       (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_pending Job dJ jaL
          (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_inflated_job_cost Job dJ cL suL j) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_job_jitter Task dT Job dJ jaL job_task hpL cL j RL) sL j_other tL)
       (I.Bool_not (I.Decidable_decide (Lean.eq j_other j) (dJ j_other j))))
    (fun j_other => ct_bool_and _ _ _ _ (cjq_UJ_pending Job sR sL Hs jaR jaL Hja _ _ IC _ _ JJ j_other tR tL Ht)
                     (ct_bool_not _ _ (ct_decide_eq Job j_other j)))
    (ArrivalSequenceWithJitter.actual_arrivals_up_to jaR (@JitterScheduleConstruction.job_jitter Task Job jaR job_task hpR cR j RR) aR tR).
  rewrite -E in F. exact F.
Qed.

Lemma cjq_JS_highest_priority_job_other_than_j sR sL (Hs : CjqSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  Lean.eq (cl_opt (@JitterScheduleConstruction.highest_priority_job_other_than_j Task Job jaR job_task aR hpR cR suR j RR sR tR))
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_highest_priority_job_other_than_j Task dT Job dJ jaL job_task aL hpL cL suL j RL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite /JitterScheduleConstruction.highest_priority_job_other_than_j (cjq_seq_min Job _ _ (cjq_PR_FP_to_JLFP Task Job job_task hpR hpL Hhp)).
  rewrite -(cl_list_logic _ _ _ (cjq_JS_pending_jobs_other_than_j sR sL Hs tR tL Ht)).
  reflexivity.
Qed.

Lemma cjq_JS_build_schedule sR sL (Hs : CjqSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  Lean.eq (cl_opt (@JitterScheduleConstruction.build_schedule Task Job jaR job_task aR hpR cR suR j RR sR tR))
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_build_schedule Task dT Job dJ jaL job_task aL hpL cL suL j RL sL tL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite /JitterScheduleConstruction.build_schedule. unfold I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_build_schedule.
  rewrite (cjq_ite_bool _ _ _ (cjq_UJ_pending Job sR sL Hs jaR jaL Hja _ _ IC _ _ JJ j tR tL Ht)).
  rewrite -(imported_eq_to_coq_eq _ _ (cjq_JS_highest_priority_job_other_than_j sR sL Hs tR tL Ht)).
  case: (UniprocessorScheduleWithJitter.pending jaR (@JitterScheduleConstruction.inflated_job_cost Job cR suR j) (@JitterScheduleConstruction.job_jitter Task Job jaR job_task hpR cR j RR) sR j tR).
  - case: (@JitterScheduleConstruction.highest_priority_job_other_than_j Task Job jaR job_task aR hpR cR suR j RR sR tR) => [jhp|] /=; last reflexivity.
    rewrite (cjq_ite_bool _ _ _ (ct_bool_not _ _ (cjq_PR_FP_to_JLFP Task Job job_task hpR hpL Hhp jhp j))).
    by case: (Priority.FP_to_JLFP job_task hpR jhp j).
  - reflexivity.
Qed.

Lemma cjq_empty : CjqSchedRel Job (fun _ => None) (fun _ => I.Option_none Job).
Proof. intros tR tL Ht. exact (@Lean.eq_refl _ _). Qed.

Lemma cjq_JS_sched_jitter :
  CjqSchedRel Job (@JitterScheduleConstruction.sched_jitter Task Job jaR job_task aR hpR cR suR j RR)
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_sched_jitter Task dT Job dJ jaL job_task aL hpL cL suL j RL).
Proof. exact (cjq_UC_build_schedule_from_prefixes Job _ _ cjq_JS_build_schedule _ _ cjq_empty). Qed.

End JSDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cjq_VJ_valid_jitter_aware_schedule (Task Job : eqType) aR aL (Ha : CjqParRel Job aR aL)
    (job_task : Job -> Task) arrR arrL (Harr : CjqArrRel Job arrR arrL) hR hL (Hh : CjqJldpRel Job hR hL)
    cR cL (Hc : CjqParRel Job cR cL) jjR jjL (Hjj : CjqParRel Job jjR jjL) sR sL (Hs : CjqSchedRel Job sR sL) :
  PropSPropRel (ValidJitterAwareSchedule.valid_jitter_aware_schedule aR arrR hR cR jjR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Jitter_ValidSchedule_ValidJitterAwareSchedule_valid_jitter_aware_schedule Job (ct_decidable_eq Job) aL arrL hL cL jjL sL).
Proof.
  apply: ct_and; first exact (cjq_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_and; first exact (cjq_UJ_jobs_execute_after_jitter Job sR sL Hs aR aL Ha jjR jjL Hjj).
  apply: ct_and; first exact (cjq_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_and; first exact (cjq_UJP_work_conserving Job sR sL Hs aR aL cR cL jjR jjL Ha Hc Hjj arrR arrL Harr).
  exact (cjq_UJP_respects_JLDP_policy Job sR sL Hs aR aL cR cL jjR jjL Ha Hc Hjj arrR arrL Harr hR hL Hh).
Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cjq_VS_valid_suspension_aware_schedule (Job : eqType) aR aL (Ha : CjqParRel Job aR aL)
    arrR arrL (Harr : CjqArrRel Job arrR arrL) hR hL (Hh : CjqJldpRel Job hR hL) nR nL (Hn : CjqSuspRel Job nR nL)
    cR cL (Hc : CjqParRel Job cR cL) sR sL (Hs : CjqSchedRel Job sR sL) :
  PropSPropRel (ValidSuspensionAwareSchedule.valid_suspension_aware_schedule aR arrR hR nR cR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Susp_ValidSchedule_ValidSuspensionAwareSchedule_valid_suspension_aware_schedule Job (ct_decidable_eq Job) aL arrL hL nL cL sL).
Proof.
  apply: ct_and; first exact (cjq_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_and; first exact (cjq_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_and; first exact (cjq_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_and; first exact (cjq_SP_work_conserving Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn arrR arrL Harr).
  apply: ct_and; first exact (cjq_SP_respects_JLDP_policy Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn arrR arrL Harr hR hL Hh).
  exact (cjq_SI_respects_self_suspensions Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn).
Qed.

(** Pointwise forms of the constructed cost and jitter functions (for the relation search). *)
Lemma cjq_ijc_pt (Job : eqType) cR cL (Hc : CjqParRel Job cR cL) suR suL (Hsu : CjqSuspRel Job suR suL) j x :
  SubNatRel (@JitterScheduleConstruction.inflated_job_cost Job cR suR j x) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_inflated_job_cost Job (ct_decidable_eq Job) cL suL j x).
Proof. exact (cjq_JS_inflated_job_cost Job cR cL Hc suR suL Hsu j x). Qed.

Lemma cjq_jj_pt (Task Job : eqType) jaR jaL (Hja : CjqParRel Job jaR jaL) (job_task : Job -> Task) hpR hpL (Hhp : CjqRelRel Task hpR hpL)
    cR cL (Hc : CjqParRel Job cR cL) j RR RL (HR : CjqParRel Job RR RL) x :
  SubNatRel (@JitterScheduleConstruction.job_jitter Task Job jaR job_task hpR cR j RR x)
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_job_jitter Task (ct_decidable_eq Task) Job (ct_decidable_eq Job) jaL job_task hpL cL j RL x).
Proof. exact (cjq_JS_job_jitter Task Job jaR jaL Hja job_task hpR hpL Hhp cR cL Hc j RR RL HR x). Qed.

(** [valid_jitter_aware_schedule] without the unused task-level inputs of the library lemma (for the relation search). *)
Lemma cjq_VJ_vjas (Job : eqType) aR aL (Ha : CjqParRel Job aR aL) arrR arrL (Harr : CjqArrRel Job arrR arrL)
    hR hL (Hh : CjqJldpRel Job hR hL) cR cL (Hc : CjqParRel Job cR cL) jjR jjL (Hjj : CjqParRel Job jjR jjL)
    sR sL (Hs : CjqSchedRel Job sR sL) :
  PropSPropRel (ValidJitterAwareSchedule.valid_jitter_aware_schedule aR arrR hR cR jjR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Jitter_ValidSchedule_ValidJitterAwareSchedule_valid_jitter_aware_schedule Job (ct_decidable_eq Job) aL arrL hL cL jjL sL).
Proof. exact (cjq_VJ_valid_jitter_aware_schedule unit Job aR aL Ha (fun _ => tt) arrR arrL Harr hR hL Hh cR cL Hc jjR jjL Hjj sR sL Hs). Qed.

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
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CjqParRel _ f g |- _ => exact (H x) end
  | |- CtBoolRel (?f ?x ?y) (?g ?x ?y) => match goal with H : CjqRelRel _ f g |- _ => exact (H x y) end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | ArrivalSequence.arrival_sequence _ => apply: (cjq_forall_arr _); intros ? ? ?
  | UniprocessorSchedule.schedule _ => apply: (cjq_forall_sched _); intros ? ? ?
  | nat -> option _ => apply: (cjq_forall_sched _); intros ? ? ?
  | Priority.FP_policy _ => apply: (cjq_forall_rel _); intros ? ? ?
  | seq _ => apply: (cjq_forall_list _); intros ? ? ?
  | Suspension.job_suspension _ => apply: (cjq_forall_susp _); intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: cjq_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp; crel
  | lazymatch goal with
    | |- forall _, _ => intro; crel
    | |- CjqSchedRel _ (JitterScheduleConstruction.sched_jitter _ _ _ _ _ _ _ _) _ => eapply cjq_JS_sched_jitter; crel
    | |- CjqParRel _ (ArrivalSequenceWithJitter.actual_arrival _ _) _ => intro; eapply cjq_AJ_actual_arrival; crel
    | |- CjqParRel _ (JitterScheduleConstruction.inflated_job_cost _ _ _) _ => eapply cjq_JS_inflated_job_cost; crel
    | |- CjqParRel _ (JitterScheduleConstruction.job_jitter _ _ _ _ _ _) _ => eapply cjq_JS_job_jitter; crel
    | |- CjqJldpRel _ (Priority.FP_to_JLDP _ _) _ => eapply cjq_PR_FP_to_JLDP; crel
    | |- Lean.eq (cl_opt (JitterScheduleConstruction.build_schedule _ _ _ _ _ _ _ _ _ _)) _ => eapply cjq_JS_build_schedule; crel
    | |- Lean.eq (cl_opt (?s _)) _ => first [ match goal with H : CjqSchedRel _ s _ |- _ => eapply H; crel end | eapply cjq_JS_sched_jitter; crel ]
    | |- SubNatRel ?a _ => crel_n a
    | |- CtBoolRel ?b _ => crel_b b
    | |- ClListRel _ ?l _ => crel_l l
    | |- PropSPropRel ?P _ => crel_p P
    end ]
with crel_n a :=
  lazymatch a with
  | addn _ _ => eapply sub_add_correspondence; crel
  | subn _ _ => eapply ct_sub_rel; crel
  | S _ => eapply cjq_succ_rel; crel
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
  | _ <-> _ => eapply cjq_iff; crel
  | _ <> _ => eapply cjq_ne
  | ~ _ => eapply ct_imp; [crel | exact cjq_false_rel]
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else crel_eq_defs
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_eq_defs := first [ eapply ct_eq_rel | eapply cjq_opt_rel_eq; crel ]
with crel_n_defs := first [ eapply cjq_US_service; crel
    | eapply cjq_ijc_pt; crel
    | eapply cjq_jj_pt; crel
    | eapply cjq_US_service_during; crel
    | eapply cjq_US_service_at; crel ]
with crel_b_defs := first [ eapply cjq_US_scheduled_at; crel
    | eapply cjq_US_completed_by; crel
    | eapply cjq_has_arrived; crel
    | eapply cjq_SI_suspended_at; crel
    | eapply cjq_US_pending; crel
    | eapply cjq_UJ_pending; crel
    | eapply cjq_UJ_backlogged; crel
    | eapply cjq_SS_backlogged; crel
    | eapply cjq_arrives_at; crel ]
with crel_l_defs := first [ fail ]
with crel_p_defs := first [ eapply cjq_arrives_in; crel
    | eapply cjq_consistent; crel
    | eapply cjq_mem; crel
    | eapply cjq_US_jobs_come_from_arrival_sequence; crel
    | eapply cjq_US_jobs_must_arrive_to_execute; crel
    | eapply cjq_US_completed_jobs_dont_execute; crel
    | eapply cjq_UJ_jobs_execute_after_jitter; crel
    | eapply cjq_UJP_work_conserving; crel
    | eapply cjq_UJP_respects_FP_policy; crel
    | eapply cjq_SP_work_conserving; crel
    | eapply cjq_SP_respects_JLDP_policy; crel
    | eapply cjq_SI_respects_self_suspensions; crel
    | eapply cjq_PR_FP_is_reflexive; crel
    | eapply cjq_PR_FP_is_transitive; crel
    | eapply cjq_PR_FP_is_total_over_task_set; crel
    | eapply cjq_VJ_vjas; crel
    | eapply cjq_VS_valid_suspension_aware_schedule; crel ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_sched_jitter_depends_only_on_service (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleProperties.sched_jitter_depends_only_on_service Task Job)).
Definition tgt_sched_jitter_depends_only_on_service (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleProperties_JitterScheduleProperties_sched_jitter_depends_only_on_service Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleProperties_sched_jitter_depends_only_on_service_correspondence (Task Job : eqType) :
  PropSPropRel (src_sched_jitter_depends_only_on_service Task Job) (tgt_sched_jitter_depends_only_on_service Task Job).
Proof. unfold src_sched_jitter_depends_only_on_service, tgt_sched_jitter_depends_only_on_service. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_jitter_uses_construction_function (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleProperties.sched_jitter_uses_construction_function Task Job)).
Definition tgt_sched_jitter_uses_construction_function (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleProperties_JitterScheduleProperties_sched_jitter_uses_construction_function Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleProperties_sched_jitter_uses_construction_function_correspondence (Task Job : eqType) :
  PropSPropRel (src_sched_jitter_uses_construction_function Task Job) (tgt_sched_jitter_uses_construction_function Task Job).
Proof. unfold src_sched_jitter_uses_construction_function, tgt_sched_jitter_uses_construction_function. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_jitter_jobs_come_from_arrival_sequence (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleProperties.sched_jitter_jobs_come_from_arrival_sequence Task Job)).
Definition tgt_sched_jitter_jobs_come_from_arrival_sequence (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleProperties_JitterScheduleProperties_sched_jitter_jobs_come_from_arrival_sequence Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleProperties_sched_jitter_jobs_come_from_arrival_sequence_correspondence (Task Job : eqType) :
  PropSPropRel (src_sched_jitter_jobs_come_from_arrival_sequence Task Job) (tgt_sched_jitter_jobs_come_from_arrival_sequence Task Job).
Proof. unfold src_sched_jitter_jobs_come_from_arrival_sequence, tgt_sched_jitter_jobs_come_from_arrival_sequence. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_jitter_jobs_execute_after_jitter (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleProperties.sched_jitter_jobs_execute_after_jitter Task Job)).
Definition tgt_sched_jitter_jobs_execute_after_jitter (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleProperties_JitterScheduleProperties_sched_jitter_jobs_execute_after_jitter Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleProperties_sched_jitter_jobs_execute_after_jitter_correspondence (Task Job : eqType) :
  PropSPropRel (src_sched_jitter_jobs_execute_after_jitter Task Job) (tgt_sched_jitter_jobs_execute_after_jitter Task Job).
Proof. unfold src_sched_jitter_jobs_execute_after_jitter, tgt_sched_jitter_jobs_execute_after_jitter. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_jitter_completed_jobs_dont_execute (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleProperties.sched_jitter_completed_jobs_dont_execute Task Job)).
Definition tgt_sched_jitter_completed_jobs_dont_execute (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleProperties_JitterScheduleProperties_sched_jitter_completed_jobs_dont_execute Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleProperties_sched_jitter_completed_jobs_dont_execute_correspondence (Task Job : eqType) :
  PropSPropRel (src_sched_jitter_completed_jobs_dont_execute Task Job) (tgt_sched_jitter_completed_jobs_dont_execute Task Job).
Proof. unfold src_sched_jitter_completed_jobs_dont_execute, tgt_sched_jitter_completed_jobs_dont_execute. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_jitter_work_conserving (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleProperties.sched_jitter_work_conserving Task Job)).
Definition tgt_sched_jitter_work_conserving (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleProperties_JitterScheduleProperties_sched_jitter_work_conserving Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleProperties_sched_jitter_work_conserving_correspondence (Task Job : eqType) :
  PropSPropRel (src_sched_jitter_work_conserving Task Job) (tgt_sched_jitter_work_conserving Task Job).
Proof. unfold src_sched_jitter_work_conserving, tgt_sched_jitter_work_conserving. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_jitter_respects_policy (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleProperties.sched_jitter_respects_policy Task Job)).
Definition tgt_sched_jitter_respects_policy (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleProperties_JitterScheduleProperties_sched_jitter_respects_policy Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleProperties_sched_jitter_respects_policy_correspondence (Task Job : eqType) :
  PropSPropRel (src_sched_jitter_respects_policy Task Job) (tgt_sched_jitter_respects_policy Task Job).
Proof. unfold src_sched_jitter_respects_policy, tgt_sched_jitter_respects_policy. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_jitter_is_valid (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleProperties.sched_jitter_is_valid Task Job)).
Definition tgt_sched_jitter_is_valid (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleProperties_JitterScheduleProperties_sched_jitter_is_valid Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleProperties_sched_jitter_is_valid_correspondence (Task Job : eqType) :
  PropSPropRel (src_sched_jitter_is_valid Task Job) (tgt_sched_jitter_is_valid Task Job).
Proof. unfold src_sched_jitter_is_valid, tgt_sched_jitter_is_valid. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_jitter_does_not_pick_j (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@JitterScheduleProperties.sched_jitter_does_not_pick_j Task Job)).
Definition tgt_sched_jitter_does_not_pick_j (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterScheduleProperties_JitterScheduleProperties_sched_jitter_does_not_pick_j Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem JitterScheduleProperties_sched_jitter_does_not_pick_j_correspondence (Task Job : eqType) :
  PropSPropRel (src_sched_jitter_does_not_pick_j Task Job) (tgt_sched_jitter_does_not_pick_j Task Job).
Proof. unfold src_sched_jitter_does_not_pick_j, tgt_sched_jitter_does_not_pick_j. crel_spine. crel. Unshelve. all: crel. Qed.
