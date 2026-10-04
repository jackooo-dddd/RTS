From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.minmax classic.model.suspension classic.model.priority classic.model.arrival.basic.arrival_sequence classic.model.arrival.jitter.arrival_sequence classic.model.schedule.uni.schedule classic.model.schedule.uni.jitter.schedule classic.model.schedule.uni.transformation.construction classic.analysis.uni.susp.dynamic.jitter.jitter_schedule classic.model.schedule.uni.response_time classic.model.schedule.uni.jitter.valid_schedule classic.model.schedule.uni.jitter.platform classic.model.schedule.uni.susp.last_execution classic.model.schedule.uni.susp.suspension_intervals classic.model.schedule.uni.susp.schedule classic.model.schedule.uni.susp.valid_schedule classic.model.schedule.uni.susp.platform classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_properties classic.model.arrival.basic.task classic.model.arrival.basic.task_arrival classic.model.schedule.uni.workload classic.model.schedule.uni.service classic.model.arrival.jitter.arrival_sequence classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service classic.model.schedule.uni.workload classic.model.schedule.uni.service classic.model.arrival.jitter.arrival_sequence classic.analysis.uni.susp.dynamic.jitter.jitter_schedule_service classic.util.pick classic.model.schedule.uni.schedulability classic.analysis.uni.susp.dynamic.jitter.rta_by_reduction.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicRtaByReduction.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicRtaByReductionBase ClassicRtaByReductionList ClassicRtaByReductionOrd.



Module I := ImportedClassicRtaByReduction.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/uni/susp/dynamic/jitter/rta_by_reduction.v] (ProsaBuddy classic, commit f692cb7).

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

Lemma crr_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma crr_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma crr_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) crr_false_rel). Qed.

Lemma crr_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma crr_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma crr_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma crr_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma crr_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma crr_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (crr_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => crr_unmap_rel T l) PR PL).
Qed.

Definition CrrParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma crr_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CrrParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (crr_forall_cover _ _ (CrrParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint crr_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (crr_natl s') end.

Definition crr_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma crr_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) crr_one) (crr_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) crr_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (crr_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma crr_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (crr_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (crr_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma crr_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma crr_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma crr_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma crr_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH crr_cl_append. reflexivity.
Qed.

Lemma crr_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CrrFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma crr_bigcat_rel (A : Type) fR fL (Hf : CrrFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicRtaByReductionInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (crr_iota_range (nR - mR) 0) crr_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (crr_cl_map_ext _ _ Hpt) (crr_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) crr_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite crr_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CrrArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition crr_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition crr_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma crr_arr_canonical aR : CrrArrRel aR (crr_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /crr_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma crr_arr_surjective aL : CrrArrRel (crr_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma crr_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CrrArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (crr_forall_cover _ _ CrrArrRel crr_arr_to_target crr_arr_to_source crr_arr_canonical crr_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma crr_jobs_arrived_between aR aL (Ha : CrrArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (crr_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma crr_arrives_in aR aL (Ha : CrrArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (crr_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma crr_consistent pR pL (Hp : CrrParRel Job pR pL) aR aL (Ha : CrrArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (crr_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma crr_is_a_set aR aL (Ha : CrrArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (crr_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma crr_jobs_arrived_before aR aL (Ha : CrrArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job dJ aL tL).
Proof. exact (crr_jobs_arrived_between Job aR aL Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma crr_arrives_at aR aL (Ha : CrrArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (crr_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma crr_has_arrived pR pL (Hp : CrrParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint crr_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (crr_snatl s') end.

Lemma crr_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (crr_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (crr_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma crr_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (crr_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (crr_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma crr_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CrrFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma crr_fun_canonical FR FL (HF : CrrFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma crr_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma crr_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CrrFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := crr_nat_sub_canonical nR mR.
  rewrite crr_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (crr_foldr_add FL FR (crr_fun_canonical FR FL HF)).
  by rewrite crr_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition crr_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition crr_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma crr_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma crr_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (crr_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CrrSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition crr_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition crr_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma crr_sched_canonical sR : CrrSchedRel sR (crr_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /crr_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma crr_sched_surjective sL : CrrSchedRel (crr_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /crr_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma crr_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CrrSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (crr_forall_cover _ _ CrrSchedRel crr_sched_to_target crr_sched_to_source crr_sched_canonical crr_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma crr_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CrrSchedRel Job sR (crr_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CrrSchedRel Job (crr_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (crr_sched_canonical Job) (crr_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CrrSchedRel Job sR sL.

Lemma crr_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (crr_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (crr_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma crr_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (crr_US_scheduled_at j tR tL Ht)). Qed.

Lemma crr_service_at_fun j : CrrFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (crr_US_service_at j kR kL Hk). Qed.

Lemma crr_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (crr_ico _ _ _ _ _ _ H1 H2 (crr_service_at_fun j)). Qed.

Lemma crr_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (crr_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma crr_US_completed_by cR cL (Hc : CrrParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (crr_US_service j tR tL Ht)). Qed.

Lemma crr_US_pending aR aL (Ha : CrrParRel Job aR aL) cR cL (Hc : CrrParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (crr_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (crr_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma crr_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CrrArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (crr_US_scheduled_at j tR tL Ht)).
  exact (crr_arrives_in Job arrR arrL Harr j).
Qed.

Lemma crr_US_jobs_must_arrive_to_execute aR aL (Ha : CrrParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (crr_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (crr_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma crr_US_completed_jobs_dont_execute cR cL (Hc : CrrParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (crr_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

Section SuspSusp.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSusp := (I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).

Definition CrrSuspRel (sR : Suspension.job_suspension Job) (sL : LSusp) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (sR j tR) (sL j tL).

Definition crr_susp_to_target (sR : Suspension.job_suspension Job) : LSusp :=
  fun j tL => sub_nat_to_imported (sR j (sub_nat_to_rocq tL)).

Definition crr_susp_to_source (sL : LSusp) : Suspension.job_suspension Job :=
  fun j tR => sub_nat_to_rocq (sL j (sub_nat_to_imported tR)).

Lemma crr_susp_canonical sR : CrrSuspRel sR (crr_susp_to_target sR).
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  unfold crr_susp_to_target. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma crr_susp_surjective sL : CrrSuspRel (crr_susp_to_source sL) sL.
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma crr_forall_susp (PR : Suspension.job_suspension Job -> Prop) (PL : LSusp -> SProp) :
  (forall sR sL, CrrSuspRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (crr_forall_cover _ _ CrrSuspRel crr_susp_to_target crr_susp_to_source crr_susp_canonical crr_susp_surjective PR PL). Qed.

End SuspSusp.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma crr_SU_job_suspension (Job : eqType) :
  And (forall sR : Suspension.job_suspension Job, CrrSuspRel Job sR (crr_susp_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job (ct_decidable_eq Job), CrrSuspRel Job (crr_susp_to_source Job sL) sL).
Proof. exact (And_intro _ _ (crr_susp_canonical Job) (crr_susp_surjective Job)). Qed.

Lemma crr_SU_total_suspension (Job : eqType) cR cL (Hc : CrrParRel Job cR cL) sR sL (Hs : CrrSuspRel Job sR sL) j :
  SubNatRel (Suspension.total_suspension cR sR j) (I.Prosa_Classic_Model_Suspension_Suspension_total_suspension Job (ct_decidable_eq Job) cL sL j).
Proof. exact (crr_ico 0 _ (cR j) (cL j) (sR j) (sL j) (sub_nat_rel_canonical 0) (Hc j) (Hs j)). Qed.

(** The imported [ArrivalSequenceWithJitter] definitions (as in the accepted classic jitter arrival_sequence certificate). *)
Section JitterArrDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma crr_AJ_actual_arrival pR pL (Hp : CrrParRel Job pR pL) qR qL (Hq : CrrParRel Job qR qL) j :
  SubNatRel (ArrivalSequenceWithJitter.actual_arrival pR qR j) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Hp j) (Hq j)). Qed.

Lemma crr_AJ_jitter_has_passed pR pL (Hp : CrrParRel Job pR pL) qR qL (Hq : CrrParRel Job qR qL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequenceWithJitter.jitter_has_passed pR qR j tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_jitter_has_passed Job dJ pL qL j tL).
Proof. exact (ct_decide_le _ _ _ _ (crr_AJ_actual_arrival pR pL Hp qR qL Hq j) Ht). Qed.

Lemma crr_AJ_actual_arrivals_between pR pL (Hp : CrrParRel Job pR pL) qR qL (Hq : CrrParRel Job qR qL)
    aR aL (Ha : CrrArrRel Job aR aL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_between pR qR aR t1R t2R) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_between Job dJ pL qL aL t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (crr_jobs_arrived_before Job aR aL Ha t2R t2L H2).
  have F := cl_filter cid _
              (fun j => I.Bool_and
                 (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j))
                    (I.Nat_decLe t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j)))
                 (I.Decidable_decide (I.LT_lt_inst1 Lean.Nat I.instLTNat (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)
                    (I.Nat_decLt (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)))
              (fun j => ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (crr_AJ_actual_arrival pR pL Hp qR qL Hq j))
                                          (ct_decide_lt _ _ _ _ (crr_AJ_actual_arrival pR pL Hp qR qL Hq j) H2))
              (ArrivalSequence.jobs_arrived_before aR t2R).
  rewrite -E in F. exact F.
Qed.

Lemma crr_AJ_actual_arrivals_up_to pR pL (Hp : CrrParRel Job pR pL) qR qL (Hq : CrrParRel Job qR qL)
    aR aL (Ha : CrrArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_up_to pR qR aR tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_up_to Job dJ pL qL aL tL).
Proof. exact (crr_AJ_actual_arrivals_between pR pL Hp qR qL Hq aR aL Ha 0 _ (sub_nat_rel_canonical 0) tR.+1 _ (crr_succ_rel tR tL Ht)). Qed.

End JitterArrDefs.

Section UjschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CrrSchedRel Job sR sL.

Lemma crr_UJ_pending aR aL (Ha : CrrParRel Job aR aL) cR cL (Hc : CrrParRel Job cR cL)
    jjR jjL (Hjj : CrrParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.pending aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_pending Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (crr_AJ_jitter_has_passed Job aR aL Ha jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (crr_US_completed_by Job sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

End UjschedDefs.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CrrRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma crr_rel_canonical (T : Type) (rR : T -> T -> bool) : CrrRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma crr_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CrrRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma crr_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CrrRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (crr_forall_cover _ _ (CrrRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (crr_rel_canonical T) (crr_rel_surjective T) PR PL).
Qed.

Definition CrrJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CrrRelRel T (rR tR) (rL tL).

Lemma crr_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CrrJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma crr_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CrrJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma crr_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CrrJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (crr_forall_cover _ _ (CrrJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (crr_jldp_canonical T) (crr_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma crr_PR_FP_policy :
  And (forall rR : Priority.FP_policy Task, CrrRelRel Task rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_FP_policy Task dT, CrrRelRel Task (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (crr_rel_canonical Task) (crr_rel_surjective Task)). Qed.

Lemma crr_PR_JLFP_policy :
  And (forall rR : Priority.JLFP_policy Job, CrrRelRel Job rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLFP_policy Job dJ, CrrRelRel Job (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (crr_rel_canonical Job) (crr_rel_surjective Job)). Qed.

Lemma crr_PR_JLDP_policy :
  And (forall rR : Priority.JLDP_policy Job, CrrJldpRel Job rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLDP_policy Job dJ,
         CrrJldpRel Job (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL).
Proof. exact (And_intro _ _ (crr_jldp_canonical Job) (crr_jldp_surjective Job)). Qed.

Lemma crr_PR_FP_to_JLFP (job_task : Job -> Task) rR rL (Hr : CrrRelRel Task rR rL) :
  CrrRelRel Job (Priority.FP_to_JLFP job_task rR)
    (I.Prosa_Classic_Model_Priority_Priority_FP_to_JLFP Task Job dT dJ job_task rL).
Proof. intros a b. exact (Hr (job_task a) (job_task b)). Qed.

Lemma crr_PR_FP_to_JLDP (job_task : Job -> Task) rR rL (Hr : CrrRelRel Task rR rL) :
  CrrJldpRel Job (Priority.FP_to_JLDP job_task rR)
    (I.Prosa_Classic_Model_Priority_Priority_FP_to_JLDP Task Job dT dJ job_task rL).
Proof. intros tR tL _ a b. exact (Hr (job_task a) (job_task b)). Qed.

Lemma crr_reflexive (T : Type) rR rL (Hr : CrrRelRel T rR rL) :
  PropSPropRel (reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_reflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (Hr x x)). Qed.

Lemma crr_transitive (T : Type) rR rL (Hr : CrrRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma crr_PR_FP_is_reflexive rR rL (Hr : CrrRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_reflexive Task dT rL).
Proof. exact (crr_reflexive Task rR rL Hr). Qed.

Lemma crr_PR_FP_is_transitive rR rL (Hr : CrrRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_transitive Task dT rL).
Proof. exact (crr_transitive Task rR rL Hr). Qed.

Lemma crr_PR_FP_is_total_over_task_set rR rL (Hr : CrrRelRel Task rR rL) ts tsL (Hts : ClListRel cid ts tsL) :
  PropSPropRel (Priority.FP_is_total_over_task_set rR ts)
    (I.Prosa_Classic_Model_Priority_Priority_FP_is_total_over_task_set Task dT rL tsL).
Proof.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: ct_imp; first exact (crr_mem Task x1 ts tsL Hts).
  apply: ct_imp; first exact (crr_mem Task x2 ts tsL Hts).
  exact (ct_or _ _ _ _ (ct_bool_truth _ _ (Hr x1 x2)) (ct_bool_truth _ _ (Hr x2 x1))).
Qed.

End PriodefsDefs.

(* ------------------------------------------------------------------ *)
(** * [seq_min] (as in the accepted classic minmax certificate) *)

Lemma crr_opt_eq {A} (o1 o2 : option A) : PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
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

Lemma crr_argmin_step x l :
  Logic.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (I.List_cons T1 x l))
    (I.Prosa_Classic_Util_Minmax_seq_argmin_match_1 T1 (fun _ => I.Option T1)
       (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL l)
       (fun y => I.ite (I.Option T1) (Lean.eq (relL (FL x) (FL y)) I.Bool_true) (I.instDecidableEqBool (relL (FL x) (FL y)) I.Bool_true)
                   (I.Option_some T1 x) (I.Option_some T1 y))
       (fun _ => I.Option_some T1 x)).
Proof. reflexivity. Qed.

Lemma crr_argmin_rel : forall l,
  Logic.eq (cl_opt (seq_argmin relR FR l)) (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (cl_map cid l)).
Proof.
  elim => [|x l IH] //=. rewrite crr_argmin_step -IH.
  case: (seq_argmin relR FR l) => [y|] //=.
  rewrite (ct_bool_rel_logic _ _ (Hcomp x y)). by case: (relR (FR x) (FR y)).
Qed.

Lemma crr_argmin_eq l L (H : ClListRel cid l L) o :
  PropSPropRel (Logic.eq (seq_argmin relR FR l) o)
    (Lean.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL L) (cl_opt o)).
Proof. destruct H. rewrite -crr_argmin_rel. exact (crr_opt_eq _ _). Qed.

End MinmaxArg.

Lemma crr_seq_min (T : eqType) relR relL (Hrel : forall a b, CtBoolRel (relR a b) (relL a b)) l :
  Logic.eq (cl_opt (seq_min relR l)) (I.Prosa_Classic_Util_Minmax_seq_min T (ct_decidable_eq T) relL (cl_map cid l)).
Proof. exact (crr_argmin_rel T T T (ct_decidable_eq T) relR relL (@Datatypes.id T) (I.id T) (fun x y => Hrel _ _) l). Qed.

(* ------------------------------------------------------------------ *)
(** * Options *)

Lemma crr_opt_rel_eq (A : Type) (o1 o2 : option A) l1 l2 :
  Lean.eq (cl_opt o1) l1 -> Lean.eq (cl_opt o2) l2 -> PropSPropRel (Logic.eq o1 o2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. destruct H1. destruct H2. apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (crr_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Definition crr_lsym {A : Type} {x y : A} (E : Lean.eq x y) : Lean.eq y x :=
  match E in Lean.eq _ z return Lean.eq z x with Lean.eq_refl => @Lean.eq_refl _ _ end.

Lemma crr_src_transport {A : Type} (P : A -> SProp) (x y : A) : Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

Lemma crr_nat_input (nR : nat) (nL : Lean.Nat) : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
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
Hypothesis Hbuild : forall sR sL, CrrSchedRel Job sR sL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (buildR sR tR)) (buildL sL tL).
Variables (baseR : UniprocessorSchedule.schedule Job) (baseL : LSched).
Hypothesis Hbase : CrrSchedRel Job baseR baseL.

Lemma crr_nat_eqb tR tL t'R t'L : SubNatRel tR tL -> SubNatRel t'R t'L ->
  CtBoolRel (tR == t'R) (I.Decidable_decide (Lean.eq tL t'L) (I.instDecidableEqNat tL t'L)).
Proof. intros Ht Ht'. exact (ct_decide_eq_nat _ _ _ _ Ht Ht'). Qed.

Lemma crr_UC_update_schedule prevR prevL (Hprev : CrrSchedRel Job prevR prevL) nR nL (Hn : SubNatRel nR nL) :
  CrrSchedRel Job (@ScheduleConstruction.update_schedule Job buildR prevR nR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule Job dJ buildL prevL nL).
Proof.
  intros tR tL Ht. unfold ScheduleConstruction.update_schedule, I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule. cbv beta.
  apply: coq_eq_to_imported_eq.
  rewrite (ct_bool_rel_logic _ _ (crr_nat_eqb tR tL nR nL Ht Hn)).
  case: (tR == nR).
  - exact (imported_eq_to_coq_eq _ _ (Hbuild prevR prevL Hprev tR tL Ht)).
  - exact (imported_eq_to_coq_eq _ _ (Hprev tR tL Ht)).
Qed.

Lemma crr_prefix_canonical (mR : nat) :
  CrrSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL (sub_nat_to_imported mR)).
Proof.
  induction mR as [|m IH].
  - refine (crr_trs (crr_lsym (I.Prosa_Validation_ClassicRtaByReductionInterface_production_schedule_prefix_zero Job dJ buildL baseL))
              (fun z => CrrSchedRel Job _ z) _).
    exact (crr_UC_update_schedule baseR baseL Hbase 0 _ (sub_nat_rel_canonical 0)).
  - assert (Hm1 : SubNatRel m.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
                                 (sub_nat_to_imported m) (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)))).
    { exact (crr_src_transport (fun x => SubNatRel x _) _ _ (addn1 m)
               (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical 1))). }
    refine (crr_trs Hm1 (fun z => CrrSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR m.+1) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) _).
    refine (crr_trs (crr_lsym (I.Prosa_Validation_ClassicRtaByReductionInterface_production_schedule_prefix_succ Job dJ buildL baseL (sub_nat_to_imported m)))
              (fun z => CrrSchedRel Job _ z) _).
    exact (crr_UC_update_schedule _ _ IH _ _ Hm1).
Qed.

Lemma crr_UC_schedule_prefix mR mL (Hm : SubNatRel mR mL) :
  CrrSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL mL).
Proof. exact (crr_trs Hm (fun z => CrrSchedRel Job _ (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) (crr_prefix_canonical mR)). Qed.

Lemma crr_UC_build_schedule_from_prefixes :
  CrrSchedRel Job (@ScheduleConstruction.build_schedule_from_prefixes Job buildR baseR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_build_schedule_from_prefixes Job dJ buildL baseL).
Proof. intros tR tL Ht. exact (crr_UC_schedule_prefix tR tL Ht tR tL Ht). Qed.

End UconsConstruction.

Section UjplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CrrSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (jjR : Job -> nat) (jjL : Job -> Lean.Nat).
Hypotheses (Ha : CrrParRel Job aR aL) (Hc : CrrParRel Job cR cL) (Hjj : CrrParRel Job jjR jjL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CrrArrRel Job arrR arrL.

Notation SA := (crr_US_scheduled_at Job sR sL Hs).

End UjplatDefs.

(** * [\max] over ordinals against [maxFiltered] over [List.finRange] *)

Lemma crr_foldr_max (f : Lean.Nat -> Lean.Nat) (g : nat -> nat)
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

Lemma crr_max_rel nR nL (Hn : SubNatRel nR nL) (QR : 'I_nR -> bool) (QL : Fin nL -> I.Bool) (HQ : CoOrdPredRel nR nL QR QL) :
  SubNatRel (\max_(i < nR | QR i) nat_of_ord i)
    (I.Prosa_Util_Sum_maxFiltered_inst1 (Fin nL) (I.List_finRange nL) QL (fun o => I.Fin_val nL o)).
Proof.
  have E := co_nat_logic _ _ Hn. subst nL. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicRtaByReductionInterface_maxFiltered_finRange
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
  exact (crr_foldr_max _ _ (co_fam_related nR sub_nat_to_imported (fun i => if QR i then nat_of_ord i else 0)
           (fun oL => I.cond Lean.Nat (QL oL) (I.Fin_val _ oL) (sub_nat_to_imported 0)) 0 HF) (iota 0 nR)).
Qed.

Lemma crr_ite_rel bR bL (Hb : CtBoolRel bR bL) xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) :
  SubNatRel (if bR then xR else yR)
    (I.ite Lean.Nat (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) xL yL).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). destruct bR; [exact Hx | exact Hy]. Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma crr_LE_time_after_last_execution (Job : eqType) aR aL (Ha : CrrParRel Job aR aL)
    sR sL (Hs : CrrSchedRel Job sR sL) j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (LastExecution.time_after_last_execution aR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Susp_LastExecution_LastExecution_time_after_last_execution Job (ct_decidable_eq Job) aL sL j tL).
Proof.
  assert (HQ : CoOrdPredRel tR tL (fun o => UniprocessorSchedule.scheduled_at sR j o)
      (fun oL => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job (ct_decidable_eq Job) sL j (I.Fin_val tL oL))).
  { intros o oL Ho. exact (crr_US_scheduled_at Job sR sL Hs j _ _ Ho). }
  exact (crr_ite_rel _ _ (co_exists_rel tR tL Ht _ _ HQ) _ _
           (sub_add_correspondence _ _ _ _ (crr_max_rel tR tL Ht _ _ HQ) (sub_nat_rel_canonical 1)) _ _ (Ha j)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Section SuspintDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CrrSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CrrParRel Job aR aL) (Hc : CrrParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CrrSuspRel Job nR nL.

Lemma crr_SI_suspension_duration j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (SuspensionIntervals.suspension_duration aR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspension_duration Job dJ aL nL sL j tL).
Proof. exact (Hn j _ _ (crr_US_service Job sR sL Hs j _ _ ((crr_LE_time_after_last_execution Job aR aL Ha sR sL Hs) j tR tL Ht))). Qed.

Lemma crr_SI_suspended_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (SuspensionIntervals.suspended_at aR cR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspended_at Job dJ aL cL nL sL j tL).
Proof.
  have HT := (crr_LE_time_after_last_execution Job aR aL Ha sR sL Hs) j tR tL Ht.
  exact (ct_bool_and _ _ _ _ (ct_bool_not _ _ (crr_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht))
           (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ HT Ht)
              (ct_decide_lt _ _ _ _ Ht (sub_add_correspondence _ _ _ _ HT (crr_SI_suspension_duration j tR tL Ht))))).
Qed.

Lemma crr_SI_respects_self_suspensions :
  PropSPropRel (SuspensionIntervals.respects_self_suspensions aR cR nR sR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_respects_self_suspensions Job dJ aL cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (crr_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (crr_SI_suspended_at j tR tL Ht)) crr_false_rel).
Qed.

End SuspintDefs.

Section SuspschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CrrSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CrrParRel Job aR aL) (Hc : CrrParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CrrSuspRel Job nR nL.

Lemma crr_SS_backlogged j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithSuspensions.backlogged aR cR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Schedule_ScheduleWithSuspensions_backlogged Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _
           (ct_bool_and _ _ _ _ (crr_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)
              (ct_bool_not _ _ (crr_US_scheduled_at Job sR sL Hs j _ _ Ht)))
           (ct_bool_not _ _ (crr_SI_suspended_at Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn j _ _ Ht))).
Qed.

End SuspschedDefs.

Section SuspplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CrrSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CrrParRel Job aR aL) (Hc : CrrParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CrrSuspRel Job nR nL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CrrArrRel Job arrR arrL.

Notation SA := (crr_US_scheduled_at Job sR sL Hs).

Lemma crr_SP_work_conserving :
  PropSPropRel (PlatformWithSuspensions.work_conserving aR cR nR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Platform_PlatformWithSuspensions_work_conserving Job dJ aL cL nL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (crr_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ ((crr_SS_backlogged Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn) j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (SA j_other tR tL Ht)).
Qed.

Lemma crr_SP_respects_JLDP_policy hR hL (Hh : CrrJldpRel Job hR hL) :
  PropSPropRel (PlatformWithSuspensions.respects_JLDP_policy aR cR nR arrR sR hR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Platform_PlatformWithSuspensions_respects_JLDP_policy Job dJ aL cL nL arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (crr_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ ((crr_SS_backlogged Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn) j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh tR tL Ht j_hp j)).
Qed.

End SuspplatDefs.

Section UrtDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CrrSchedRel Job sR sL.

Lemma crr_RT_is_response_time_bound_of_job aR aL (Ha : CrrParRel Job aR aL) cR cL (Hc : CrrParRel Job cR cL)
    j rR rL (Hr : SubNatRel rR rL) :
  CtBoolRel (ResponseTime.is_response_time_bound_of_job aR cR sR j rR) (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_job Job dJ aL cL sL j rL).
Proof. exact (crr_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr)). Qed.

Lemma crr_RT_is_response_time_bound_of_task aR aL (Ha : CrrParRel Job aR aL) cR cL (Hc : CrrParRel Job cR cL)
    (job_task : Job -> Task) arrR arrL (Harr : CrrArrRel Job arrR arrL) tsk rR rL (Hr : SubNatRel rR rL) :
  PropSPropRel (ResponseTime.is_response_time_bound_of_task aR cR job_task arrR sR tsk rR)
    (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_task Task dT Job dJ aL cL job_task arrL sL tsk rL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (crr_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (crr_RT_is_response_time_bound_of_job aR aL Ha cR cL Hc j rR rL Hr)).
Qed.

End UrtDefs.

Lemma crr_iff (P Q : Prop) (PL QL : SProp) :
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

Lemma crr_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicRtaByReductionInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicRtaByReductionInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma crr_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (crr_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma crr_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicRtaByReductionInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicRtaByReductionInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicRtaByReductionInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma crr_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (crr_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CrrPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma crr_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CrrPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (crr_forall_cover _ _ (CrrPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

Section UwlDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

End UwlDefs.

Section TaskDefsP.
Variables (Task : eqType).
Notation dT := (ct_decidable_eq Task).
Notation c0 := (sub_nat_rel_canonical 0).

Lemma crr_TK_constrained_deadline_model pR pL dR dL
    (Hp : CrrParRel Task pR pL) (Hd : CrrParRel Task dR dL) ts tsL (Hts : ClListRel cid ts tsL) :
  PropSPropRel (SporadicTaskset.constrained_deadline_model pR dR ts)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_constrained_deadline_model Task dT pL dL tsL).
Proof.
  apply: ct_forall_identity => tsk.
  exact (ct_imp _ _ _ _ (crr_mem Task tsk ts tsL Hts) (sub_nat_le_correspondence _ _ _ _ (Hd tsk) (Hp tsk))).
Qed.

End TaskDefsP.

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma crr_TA_sporadic_task_model tpR tpL (Htp : CrrParRel Task tpR tpL)
    jaR jaL (Hja : CrrParRel Job jaR jaL) (job_task : Job -> Task) aR aL (Ha : CrrArrRel Job aR aL) :
  PropSPropRel (TaskArrival.sporadic_task_model tpR jaR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model Task dT tpL Job dJ jaL job_task aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'.
  apply: ct_imp; first exact (crr_ne Job j j').
  apply: ct_imp; first exact (crr_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (crr_arrives_in Job aR aL Ha j').
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j')).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htp (job_task j))) (Hja j')).
Qed.

End TaskArrivalDefs.

(* ------------------------------------------------------------------ *)
(** * Booleans *)

Definition cp_b2l (b : bool) : I.Bool := if b then I.Bool_true else I.Bool_false.
Definition cp_l2b (b : I.Bool) : bool :=
  match b with I.Bool_true => Datatypes.true | I.Bool_false => Datatypes.false end.

Definition CpBoolRel (bR : bool) (bL : I.Bool) : SProp := Lean.eq (cp_b2l bR) bL.

Lemma cp_bool_rel_canonical (b : bool) : CpBoolRel b (cp_b2l b).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma cp_bool_rel_surjective (b : I.Bool) : CpBoolRel (cp_l2b b) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma cp_bool_rel_logic bR bL : CpBoolRel bR bL -> Logic.eq bL (cp_b2l bR).
Proof. intro H. exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ H)). Qed.

Lemma cp_bool_l2b_b2l (b : bool) : Logic.eq (cp_l2b (cp_b2l b)) b.
Proof. by case: b. Qed.

Lemma cp_bool_b2l_l2b (b : I.Bool) : Logic.eq (cp_b2l (cp_l2b b)) b.
Proof. by case: b. Qed.

Lemma cp_b2l_and (a b : bool) : Logic.eq (cp_b2l (a && b)) (I.Bool_and (cp_b2l a) (cp_b2l b)).
Proof. by case: a; case: b. Qed.

Lemma cp_b2l_or (a b : bool) : Logic.eq (cp_b2l (a || b)) (I.Bool_or (cp_b2l a) (cp_b2l b)).
Proof. by case: a; case: b. Qed.

Lemma cp_b2l_not (a : bool) : Logic.eq (cp_b2l (~~ a)) (I.Bool_not (cp_b2l a)).
Proof. by case: a. Qed.

Lemma cp_bool_truth bR bL :
  CpBoolRel bR bL -> PropSPropRel (is_true bR) (Lean.eq bL I.Bool_true).
Proof.
  intro H. have E := cp_bool_rel_logic _ _ H. subst bL.
  apply prop_sprop_rel_intro.
  - intro Ht. destruct bR; [exact (@Lean.eq_refl _ _) | discriminate Ht].
  - intro HL. apply strictly_inhabits. destruct bR; [reflexivity|].
    have E := imported_eq_to_coq_eq _ _ HL. discriminate E.
Qed.

(* ------------------------------------------------------------------ *)
(** * Natural numbers *)

Lemma cp_nat_logic nR nL : SubNatRel nR nL -> Logic.eq nL (sub_nat_to_imported nR).
Proof. intro H. exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ H)). Qed.

Lemma cp_nat_lt nR nL mR mL : SubNatRel nR nL -> SubNatRel mR mL ->
  PropSPropRel (is_true (ltn nR mR)) (I.LT_lt_inst1 Lean.Nat I.instLTNat nL mL).
Proof. intros Hn Hm. exact (sub_nat_lt_correspondence nR nL mR mL Hn Hm). Qed.

Lemma cp_nat_le nR nL mR mL : SubNatRel nR nL -> SubNatRel mR mL ->
  PropSPropRel (is_true (leq nR mR)) (I.LE_le_inst1 Lean.Nat I.instLENat nL mL).
Proof. intros Hn Hm. exact (sub_nat_le_correspondence nR nL mR mL Hn Hm). Qed.

(** Lean's [decide (a ≤ b)] against MathComp's [leq]. *)
Lemma cp_decide_le_related aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL ->
  CpBoolRel (leq aR bR)
    (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat aL bL) (I.Nat_decLe aL bL)).
Proof.
  intros Ha Hb. have Hle := cp_nat_le aR aL bR bL Ha Hb.
  destruct (I.Nat_decLe aL bL) as [h|h].
  - have Hf : Logic.eq (leq aR bR) false.
    { apply/negbTE/negP. move=> Hsrc.
      exact (match h (prop_to_sprop _ _ Hle Hsrc) return Logic.False with end). }
    rewrite Hf. exact (@Lean.eq_refl _ _).
  - have Hsrc : is_true (leq aR bR) := sprop_to_prop _ _ Hle h.
    rewrite Hsrc. exact (@Lean.eq_refl _ _).
Qed.

(* ------------------------------------------------------------------ *)
(** * Ordinals and [Fin] *)

Definition CpOrdRel (nR : nat) (nL : Lean.Nat) (oR : 'I_nR) (oL : Fin nL) : SProp :=
  SubNatRel (nat_of_ord oR) (I.Fin_val nL oL).

Definition cp_ord_to_fin (nR : nat) (nL : Lean.Nat) (Hn : SubNatRel nR nL) (oR : 'I_nR) : Fin nL :=
  Fin_mk nL (sub_nat_to_imported (nat_of_ord oR))
    (prop_to_sprop _ _ (cp_nat_lt (nat_of_ord oR) _ nR nL (sub_nat_rel_canonical _) Hn) (ltn_ord oR)).

Definition cp_fin_to_ord (nR : nat) (nL : Lean.Nat) (Hn : SubNatRel nR nL) (oL : Fin nL) : 'I_nR :=
  @Ordinal nR (sub_nat_to_rocq (I.Fin_val nL oL))
    (sprop_to_prop _ _
      (cp_nat_lt _ (I.Fin_val nL oL) nR nL (sub_nat_rel_surjective (I.Fin_val nL oL)) Hn)
      (I.Fin_isLt nL oL)).

Lemma cp_ord_rel_canonical nR nL (Hn : SubNatRel nR nL) (oR : 'I_nR) :
  CpOrdRel nR nL oR (cp_ord_to_fin nR nL Hn oR).
Proof. exact (sub_nat_rel_canonical _). Qed.

Lemma cp_ord_rel_surjective nR nL (Hn : SubNatRel nR nL) (oL : Fin nL) :
  CpOrdRel nR nL (cp_fin_to_ord nR nL Hn oL) oL.
Proof. exact (sub_nat_rel_surjective _). Qed.

(** The source family of a predicate on ['I_nR], read on all naturals. *)
Definition cp_ord_family (nR : nat) (Q : 'I_nR -> bool) (dflt : bool) (k : nat) : bool :=
  if insub k is Some o then Q o else dflt.

(** Its target counterpart, exactly as in the exported Lean equations. *)
Definition cp_target_family (nL : Lean.Nat) (q : Fin nL -> I.Bool) (dflt : I.Bool) (k : Lean.Nat) : I.Bool :=
  I.dite I.Bool (I.LT_lt_inst1 Lean.Nat I.instLTNat k nL) (I.Nat_decLt k nL)
    (fun h => q (Fin_mk nL k h)) (fun _ => dflt).

Lemma cp_family_related (nR : nat) (Q : 'I_nR -> bool) (q : Fin (sub_nat_to_imported nR) -> I.Bool)
    (HQ : forall oR oL, CpOrdRel nR (sub_nat_to_imported nR) oR oL -> CpBoolRel (Q oR) (q oL))
    (dflt : bool) :
  forall kR, Logic.eq (cp_target_family (sub_nat_to_imported nR) q (cp_b2l dflt) (sub_nat_to_imported kR))
                      (cp_b2l (cp_ord_family nR Q dflt kR)).
Proof.
  intro kR. unfold cp_target_family, cp_ord_family.
  have Hlt := cp_nat_lt kR _ nR _ (sub_nat_rel_canonical kR) (sub_nat_rel_canonical nR).
  destruct (I.Nat_decLt (sub_nat_to_imported kR) (sub_nat_to_imported nR)) as [h|h]; cbn.
  - have Hge : Logic.eq (ltn kR nR) false.
    { apply/negbTE/negP. move=> Hsrc.
      exact (match h (prop_to_sprop _ _ Hlt Hsrc) return Logic.False with end). }
    by rewrite (@insubF _ _ _ kR Hge).
  - have Hsrc : is_true (ltn kR nR) := sprop_to_prop _ _ Hlt h.
    rewrite (insubT (fun x => ltn x nR) Hsrc) /=.
    apply: cp_bool_rel_logic. apply: HQ. exact (sub_nat_rel_canonical kR).
Qed.

(* ------------------------------------------------------------------ *)
(** * Searches over [iota] and [List.range'] *)

Definition cp_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).
Definition cp_zero : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0).

Lemma cp_all_iota (fR : nat -> bool) (fL : Lean.Nat -> I.Bool)
    (Hf : forall kR, Logic.eq (fL (sub_nat_to_imported kR)) (cp_b2l (fR kR))) :
  forall nR sR, Logic.eq
    (I.List_all_inst1 Lean.Nat (I.List_range' (sub_nat_to_imported sR) (sub_nat_to_imported nR) cp_one) fL)
    (cp_b2l (all fR (iota sR nR))).
Proof.
  elim => [|n IH] sR; first reflexivity.
  change (Logic.eq (I.Bool_and (fL (sub_nat_to_imported sR))
      (I.List_all_inst1 Lean.Nat (I.List_range' (sub_nat_to_imported (S sR)) (sub_nat_to_imported n) cp_one) fL))
    (cp_b2l (fR sR && all fR (iota (S sR) n)))).
  by rewrite Hf IH cp_b2l_and.
Qed.

Lemma cp_find_iota (fR : nat -> bool) (fL : Lean.Nat -> I.Bool)
    (Hf : forall kR, Logic.eq (fL (sub_nat_to_imported kR)) (cp_b2l (fR kR))) :
  forall nR sR, Logic.eq
    (I.Option_getD_inst1 Lean.Nat
      (I.List_find__q_inst1 Lean.Nat fL (I.List_range' (sub_nat_to_imported sR) (sub_nat_to_imported nR) cp_one))
      cp_zero)
    (sub_nat_to_imported (odflt O (ohead (filter fR (iota sR nR))))).
Proof.
  elim => [|n IH] sR; first reflexivity.
  change (Logic.eq
    (I.Option_getD_inst1 Lean.Nat
      (I.List_find__q_inst1 Lean.Nat fL (I.List_cons_inst1 Lean.Nat (sub_nat_to_imported sR)
        (I.List_range' (sub_nat_to_imported (S sR)) (sub_nat_to_imported n) cp_one)))
      cp_zero)
    (sub_nat_to_imported (odflt O (ohead (filter fR (sR :: iota (S sR) n)))))).
  have E := Hf sR. cbn [filter].
  destruct (fR sR); cbn in E.
  - change (Logic.eq (I.Option_getD_inst1 Lean.Nat
      (match fL (sub_nat_to_imported sR) with
       | I.Bool_true => I.Option_some_inst1 Lean.Nat (sub_nat_to_imported sR)
       | I.Bool_false => I.List_find__q_inst1 Lean.Nat fL
           (I.List_range' (sub_nat_to_imported (S sR)) (sub_nat_to_imported n) cp_one)
       end) cp_zero) (sub_nat_to_imported sR)).
    by rewrite E.
  - change (Logic.eq (I.Option_getD_inst1 Lean.Nat
      (match fL (sub_nat_to_imported sR) with
       | I.Bool_true => I.Option_some_inst1 Lean.Nat (sub_nat_to_imported sR)
       | I.Bool_false => I.List_find__q_inst1 Lean.Nat fL
           (I.List_range' (sub_nat_to_imported (S sR)) (sub_nat_to_imported n) cp_one)
       end) cp_zero) (sub_nat_to_imported (odflt O (ohead (filter fR (iota (S sR) n)))))).
    by rewrite E IH.
Qed.

(* ------------------------------------------------------------------ *)
(** * Source-side rewrites of [pick] and [[forall j, _]] into [iota] searches *)

Lemma cp_forall_ord_iota (nR : nat) (Q : 'I_nR -> bool) :
  Logic.eq [forall j, Q j] (all (cp_ord_family nR Q true) (iota 0 nR)).
Proof.
  apply/idP/idP.
  - move/forallP => H. apply/allP => k. rewrite mem_iota add0n => /andP [_ Hk].
    by rewrite /cp_ord_family insubT.
  - move/allP => H. apply/forallP => j. have := H (nat_of_ord j).
    rewrite mem_iota add0n ltn_ord /= /cp_ord_family valK. by apply.
Qed.

Lemma cp_default0_pick (nR : nat) (Q : 'I_nR -> bool) :
  Logic.eq (default0 (pick Q)) (odflt O (ohead (filter (cp_ord_family nR Q false) (iota 0 nR)))).
Proof.
  have VE : Logic.eq (map (@nat_of_ord nR) (enum 'I_nR)) (iota 0 nR) := val_enum_ord nR.
  have K : forall x : 'I_nR, Logic.eq (insub (nat_of_ord x)) (Some x) := fun x => valK x.
  rewrite -VE.
  have E : forall l : seq 'I_nR,
      Logic.eq (filter (cp_ord_family nR Q false) (map (@nat_of_ord nR) l))
               (map (@nat_of_ord nR) (filter Q l)).
  { elim => [|x l IH] //=. rewrite /cp_ord_family K. by case: (Q x); rewrite /= IH. }
  rewrite E /pick.
  have F : Logic.eq (enum Q) (filter Q (enum 'I_nR)).
  { rewrite enumT /enum_mem. apply: eq_filter => x. by rewrite inE. }
  rewrite F. by case: (filter Q (enum 'I_nR)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Options of ordinals *)

Inductive CpTrue : SProp := cp_true_intro.
Inductive CpFalse : SProp := .

Definition CpOptOrdRel (nR : nat) (nL : Lean.Nat) (xR : option 'I_nR) (xL : I.Option_inst1 (Fin nL)) : SProp :=
  match xR, xL with
  | None, I.Option_none_inst1 => CpTrue
  | Some oR, I.Option_some_inst1 oL => CpOrdRel nR nL oR oL
  | _, _ => CpFalse
  end.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Definition CpOrdPredRel nR nL (PR : 'I_nR -> bool) (PL : Fin nL -> I.Bool) : SProp :=
  forall oR oL, CpOrdRel nR nL oR oL -> CpBoolRel (PR oR) (PL oL).

Definition CpOrdRelRel nR nL (RR : 'I_nR -> 'I_nR -> bool) (RL : Fin nL -> Fin nL -> I.Bool) : SProp :=
  forall oR oL pR pL, CpOrdRel nR nL oR oL -> CpOrdRel nR nL pR pL -> CpBoolRel (RR oR pR) (RL oL pL).

Definition CpNatPredRel (pR : nat -> bool) (pL : Lean.Nat -> I.Bool) : SProp :=
  forall kR kL, SubNatRel kR kL -> CpBoolRel (pR kR) (pL kL).

Lemma cpk_default0 nR nL (Hn : SubNatRel nR nL)
    (xR : option 'I_nR) (xL : I.Option_inst1 (Fin nL)) :
  CpOptOrdRel nR nL xR xL ->
  SubNatRel (@default0 nR xR) (I.Prosa_Classic_Util_Pick_default0 nL xL).
Proof.
  destruct xR as [oR|], xL as [|oL]; cbn; intro H.
  - exact (match H with end).
  - exact H.
  - exact (sub_nat_rel_canonical O).
  - exact (match H with end).
Qed.

Lemma cpk_arg_pred_nat nR nL (Hn : SubNatRel nR nL) PR PL ordR ordL
    (iR : 'I_nR) (iL : Fin nL) :
  CpOrdPredRel nR nL PR PL -> CpOrdRelRel nR nL ordR ordL -> CpOrdRel nR nL iR iL ->
  CpBoolRel (arg_pred_nat nR PR ordR iR) (I.Prosa_Classic_Util_Pick_arg_pred_nat nL PL ordL iL).
Proof.
  have E := cp_nat_logic _ _ Hn. subst nL. intros HP Hord Hi.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  change (Logic.eq (I.Bool_and (PL iL) (I.List_all_inst1 (Fin (sub_nat_to_imported nR))
      (I.List_finRange (sub_nat_to_imported nR)) (fun j => I.Bool_or (I.Bool_not (PL j)) (ordL iL j))))
    (cp_b2l (PR iR && [forall j, PR j ==> ordR iR j]))).
  rewrite (imported_eq_to_coq_eq _ _
    (I.Prosa_Validation_ClassicRtaByReductionInterface_finRange_all (sub_nat_to_imported nR)
      (fun j => I.Bool_or (I.Bool_not (PL j)) (ordL iL j)))).
  rewrite cp_forall_ord_iota cp_b2l_and (cp_bool_rel_logic _ _ (HP iR iL Hi)).
  congr (I.Bool_and _ _).
  apply: (cp_all_iota (cp_ord_family nR (fun j => PR j ==> ordR iR j) true)
            (cp_target_family (sub_nat_to_imported nR)
               (fun j => I.Bool_or (I.Bool_not (PL j)) (ordL iL j)) I.Bool_true) _ nR O).
  move=> kR.
  apply: (cp_family_related nR (fun j => PR j ==> ordR iR j)
            (fun j => I.Bool_or (I.Bool_not (PL j)) (ordL iL j)) _ true kR).
  move=> oR oL Ho. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (cp_bool_rel_logic _ _ (HP oR oL Ho)) (cp_bool_rel_logic _ _ (Hord iR iL oR oL Hi Ho)).
  by rewrite /implb; case: (PR oR); case: (ordR iR oR).
Qed.

Lemma cpk_pred_min_nat nR nL (Hn : SubNatRel nR nL) PR PL :
  CpOrdPredRel nR nL PR PL ->
  CpOrdPredRel nR nL (fun o => pred_min_nat nR PR o) (I.Prosa_Classic_Util_Pick_pred_min_nat nL PL).
Proof.
  intros HP oR oL Ho.
  apply: (cpk_arg_pred_nat nR nL Hn PR PL _ _ oR oL HP _ Ho).
  move=> aR aL bR bL Ha Hb. exact (cp_decide_le_related _ _ _ _ Ha Hb).
Qed.

Lemma cpk_to_pred_ord nR nL pR pL :
  CpNatPredRel pR pL ->
  CpOrdPredRel nR nL (to_pred_ord nR pR) (I.Prosa_Classic_Util_Pick_to_pred_ord nL pL).
Proof. intros Hp oR oL Ho. exact (Hp _ _ Ho). Qed.

(** [default0 (pick Q)] against [default0 (find? q (finRange n))], through the
    exported interface equation [default0_find?]. *)
Lemma cp_pick_correspondence nR nL (Hn : SubNatRel nR nL) (Q : 'I_nR -> bool) (q : Fin nL -> I.Bool) :
  CpOrdPredRel nR nL Q q ->
  SubNatRel (default0 (pick Q))
    (I.Prosa_Classic_Util_Pick_default0 nL (I.List_find__q_inst1 (Fin nL) q (I.List_finRange nL))).
Proof.
  have E := cp_nat_logic _ _ Hn. subst nL. intro HQ.
  apply: coq_eq_to_imported_eq.
  rewrite (imported_eq_to_coq_eq _ _
    (I.Prosa_Validation_ClassicRtaByReductionInterface_default0_find__q (sub_nat_to_imported nR) q)).
  rewrite cp_default0_pick. apply: Logic.eq_sym.
  exact (cp_find_iota (cp_ord_family nR Q false) (cp_target_family (sub_nat_to_imported nR) q I.Bool_false)
           (cp_family_related nR Q q HQ false) nR O).
Qed.

Lemma cpk_pick_min nR nL (Hn : SubNatRel nR nL) pR pL :
  CpNatPredRel pR pL -> SubNatRel (pick_min nR pR) (I.Prosa_Classic_Util_Pick_pick_min nL pL).
Proof.
  intro Hp. exact (cp_pick_correspondence nR nL Hn _ _
    (cpk_pred_min_nat nR nL Hn _ _ (cpk_to_pred_ord nR nL pR pL Hp))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Auxiliary relations *)

(** [minn] against the core [Min.min] on [Nat] (as in the accepted classic global workload_bound certificate). *)
Lemma crr_min_canonical (a b : nat) :
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

Lemma crr_min_rel aR aL bR bL : SubNatRel aR aL -> SubNatRel bR bL -> SubNatRel (minn aR bR) ((I.Min_min_inst1 Lean.Nat I.instMinNat) aL bL).
Proof.
  intros Ha Hb. rewrite -(imported_eq_to_coq_eq _ _ Ha) -(imported_eq_to_coq_eq _ _ Hb).
  apply: coq_eq_to_imported_eq. exact (Logic.eq_sym (crr_min_canonical aR bR)).
Qed.

(** A Rocq Boolean equality test against the Lean [if x = y] on the canonical [DecidableEq] instance. *)
Lemma crr_ite_eq (J : eqType) (A : Type) (x y : J) (a b : A) :
  Logic.eq (I.ite A (Lean.eq x y) (ct_decidable_eq J x y) a b) (if x == y then a else b).
Proof. rewrite /ct_decidable_eq. by case: (@eqP J x y). Qed.

(** A Boolean [if] against the Lean [if b = true]. *)
Lemma crr_ite_bool (A : Type) bR bL (Hb : CtBoolRel bR bL) (a b : A) :
  Logic.eq (I.ite A (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) a b) (if bR then a else b).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). clear Hb. by case: bR. Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section JSDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat).
Hypothesis Hja : CrrParRel Job jaR jaL.
Variable job_task : Job -> Task.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CrrArrRel Job aR aL.
Variables (hpR : Task -> Task -> bool) (hpL : Task -> Task -> I.Bool).
Hypothesis Hhp : CrrRelRel Task hpR hpL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CrrParRel Job cR cL.
Variables (suR : Suspension.job_suspension Job) (suL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hsu : CrrSuspRel Job suR suL.
Variable j : Job.
Variables (RR : Job -> nat) (RL : Job -> Lean.Nat).
Hypothesis HR : CrrParRel Job RR RL.

Lemma crr_JS_inflated_job_cost :
  CrrParRel Job (@JitterScheduleConstruction.inflated_job_cost Job cR suR j) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_inflated_job_cost Job dJ cL suL j).
Proof.
  intro x. apply: coq_eq_to_imported_eq. rewrite /JitterScheduleConstruction.inflated_job_cost.
  unfold I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_inflated_job_cost. rewrite crr_ite_eq.
  case: (x == j).
  - exact (imported_eq_to_coq_eq _ _ (sub_add_correspondence _ _ _ _ (Hc x) (crr_SU_total_suspension Job cR cL Hc suR suL Hsu x))).
  - exact (imported_eq_to_coq_eq _ _ (Hc x)).
Qed.

Lemma crr_JS_job_jitter :
  CrrParRel Job (@JitterScheduleConstruction.job_jitter Task Job jaR job_task hpR cR j RR) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_job_jitter Task dT Job dJ jaL job_task hpL cL j RL).
Proof.
  intro x. apply: coq_eq_to_imported_eq. rewrite /JitterScheduleConstruction.job_jitter.
  unfold I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_job_jitter.
  rewrite (crr_ite_bool _ _ _ (ct_bool_and _ _ _ _ (Hhp (job_task x) (job_task j)) (ct_bool_not _ _ (ct_decide_eq Task (job_task x) (job_task j))))).
  case: (hpR (job_task x) (job_task j) && (job_task x != job_task j)).
  - exact (imported_eq_to_coq_eq _ _ (crr_min_rel _ _ _ _ (ct_sub_rel _ _ _ _ (Hja j) (Hja x)) (ct_sub_rel _ _ _ _ (HR x) (Hc x)))).
  - reflexivity.
Qed.

Notation IC := crr_JS_inflated_job_cost.
Notation JJ := crr_JS_job_jitter.

Lemma crr_JS_pending_jobs_other_than_j sR sL (Hs : CrrSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (@JitterScheduleConstruction.pending_jobs_other_than_j Task Job jaR job_task aR hpR cR suR j RR sR tR)
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_pending_jobs_other_than_j Task dT Job dJ jaL job_task aL hpL cL suL j RL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (crr_AJ_actual_arrivals_up_to Job jaR jaL Hja _ _ JJ aR aL Ha tR tL Ht).
  have F := cl_filter cid _
    (fun j_other => I.Bool_and
       (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_pending Job dJ jaL
          (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_inflated_job_cost Job dJ cL suL j) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_job_jitter Task dT Job dJ jaL job_task hpL cL j RL) sL j_other tL)
       (I.Bool_not (I.Decidable_decide (Lean.eq j_other j) (dJ j_other j))))
    (fun j_other => ct_bool_and _ _ _ _ (crr_UJ_pending Job sR sL Hs jaR jaL Hja _ _ IC _ _ JJ j_other tR tL Ht)
                     (ct_bool_not _ _ (ct_decide_eq Job j_other j)))
    (ArrivalSequenceWithJitter.actual_arrivals_up_to jaR (@JitterScheduleConstruction.job_jitter Task Job jaR job_task hpR cR j RR) aR tR).
  rewrite -E in F. exact F.
Qed.

Lemma crr_JS_highest_priority_job_other_than_j sR sL (Hs : CrrSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  Lean.eq (cl_opt (@JitterScheduleConstruction.highest_priority_job_other_than_j Task Job jaR job_task aR hpR cR suR j RR sR tR))
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_highest_priority_job_other_than_j Task dT Job dJ jaL job_task aL hpL cL suL j RL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite /JitterScheduleConstruction.highest_priority_job_other_than_j (crr_seq_min Job _ _ (crr_PR_FP_to_JLFP Task Job job_task hpR hpL Hhp)).
  rewrite -(cl_list_logic _ _ _ (crr_JS_pending_jobs_other_than_j sR sL Hs tR tL Ht)).
  reflexivity.
Qed.

Lemma crr_JS_build_schedule sR sL (Hs : CrrSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  Lean.eq (cl_opt (@JitterScheduleConstruction.build_schedule Task Job jaR job_task aR hpR cR suR j RR sR tR))
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_build_schedule Task dT Job dJ jaL job_task aL hpL cL suL j RL sL tL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite /JitterScheduleConstruction.build_schedule. unfold I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_build_schedule.
  rewrite (crr_ite_bool _ _ _ (crr_UJ_pending Job sR sL Hs jaR jaL Hja _ _ IC _ _ JJ j tR tL Ht)).
  rewrite -(imported_eq_to_coq_eq _ _ (crr_JS_highest_priority_job_other_than_j sR sL Hs tR tL Ht)).
  case: (UniprocessorScheduleWithJitter.pending jaR (@JitterScheduleConstruction.inflated_job_cost Job cR suR j) (@JitterScheduleConstruction.job_jitter Task Job jaR job_task hpR cR j RR) sR j tR).
  - case: (@JitterScheduleConstruction.highest_priority_job_other_than_j Task Job jaR job_task aR hpR cR suR j RR sR tR) => [jhp|] /=; last reflexivity.
    rewrite (crr_ite_bool _ _ _ (ct_bool_not _ _ (crr_PR_FP_to_JLFP Task Job job_task hpR hpL Hhp jhp j))).
    by case: (Priority.FP_to_JLFP job_task hpR jhp j).
  - reflexivity.
Qed.

Lemma crr_empty : CrrSchedRel Job (fun _ => None) (fun _ => I.Option_none Job).
Proof. intros tR tL Ht. exact (@Lean.eq_refl _ _). Qed.

Lemma crr_JS_sched_jitter :
  CrrSchedRel Job (@JitterScheduleConstruction.sched_jitter Task Job jaR job_task aR hpR cR suR j RR)
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_sched_jitter Task dT Job dJ jaL job_task aL hpL cL suL j RL).
Proof. exact (crr_UC_build_schedule_from_prefixes Job _ _ crr_JS_build_schedule _ _ crr_empty). Qed.

End JSDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma crr_VS_valid_suspension_aware_schedule (Job : eqType) aR aL (Ha : CrrParRel Job aR aL)
    arrR arrL (Harr : CrrArrRel Job arrR arrL) hR hL (Hh : CrrJldpRel Job hR hL) nR nL (Hn : CrrSuspRel Job nR nL)
    cR cL (Hc : CrrParRel Job cR cL) sR sL (Hs : CrrSchedRel Job sR sL) :
  PropSPropRel (ValidSuspensionAwareSchedule.valid_suspension_aware_schedule aR arrR hR nR cR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Susp_ValidSchedule_ValidSuspensionAwareSchedule_valid_suspension_aware_schedule Job (ct_decidable_eq Job) aL arrL hL nL cL sL).
Proof.
  apply: ct_and; first exact (crr_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_and; first exact (crr_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_and; first exact (crr_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_and; first exact (crr_SP_work_conserving Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn arrR arrL Harr).
  apply: ct_and; first exact (crr_SP_respects_JLDP_policy Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn arrR arrL Harr hR hL Hh).
  exact (crr_SI_respects_self_suspensions Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn).
Qed.

(** Pointwise forms of the constructed cost and jitter functions (for the relation search). *)
Lemma crr_ijc_pt (Job : eqType) cR cL (Hc : CrrParRel Job cR cL) suR suL (Hsu : CrrSuspRel Job suR suL) j x :
  SubNatRel (@JitterScheduleConstruction.inflated_job_cost Job cR suR j x) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_inflated_job_cost Job (ct_decidable_eq Job) cL suL j x).
Proof. exact (crr_JS_inflated_job_cost Job cR cL Hc suR suL Hsu j x). Qed.

Lemma crr_jj_pt (Task Job : eqType) jaR jaL (Hja : CrrParRel Job jaR jaL) (job_task : Job -> Task) hpR hpL (Hhp : CrrRelRel Task hpR hpL)
    cR cL (Hc : CrrParRel Job cR cL) j RR RL (HR : CrrParRel Job RR RL) x :
  SubNatRel (@JitterScheduleConstruction.job_jitter Task Job jaR job_task hpR cR j RR x)
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_JitterSchedule_JitterScheduleConstruction_job_jitter Task (ct_decidable_eq Task) Job (ct_decidable_eq Job) jaL job_task hpL cL j RL x).
Proof. exact (crr_JS_job_jitter Task Job jaR jaL Hja job_task hpR hpL Hhp cR cL Hc j RR RL HR x). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem RTAByReduction_actual_response_time_correspondence (Task Job : eqType) jaR jaL (Hja : CrrParRel Job jaR jaL) (job_task : Job -> Task)
    cR cL (Hc : CrrParRel Job cR cL) sR sL (Hs : CrrSchedRel Job sR sL) RR RL (HR : CrrParRel Task RR RL) j :
  SubNatRel (@RTAByReduction.actual_response_time Task Job jaR job_task cR sR RR j)
    (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_RtaByReduction_RTAByReduction_actual_response_time Task (ct_decidable_eq Task) Job (ct_decidable_eq Job) jaL job_task cL sL RL j).
Proof.
  unfold RTAByReduction.actual_response_time, I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_RtaByReduction_RTAByReduction_actual_response_time.
  refine (cpk_pick_min _ _ _ _ _ _).
  - exact (crr_succ_rel _ _ (HR (job_task j))).
  - exact (fun r rL Hr => crr_RT_is_response_time_bound_of_job Job sR sL Hs jaR jaL Hja cR cL Hc j r rL Hr).
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
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CrrParRel _ f g |- _ => exact (H x) end
  | |- CtBoolRel (?f ?x ?y) (?g ?x ?y) => match goal with H : CrrRelRel _ f g |- _ => exact (H x y) end
  | |- CtBoolRel (?f ?t ?x ?y) (?g ?u ?x ?y) => match goal with H : CrrJldpRel _ f g |- _ => eapply H end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | ArrivalSequence.arrival_sequence _ => apply: (crr_forall_arr _); intros ? ? ?
  | UniprocessorSchedule.schedule _ => apply: (crr_forall_sched _); intros ? ? ?
  | nat -> option _ => apply: (crr_forall_sched _); intros ? ? ?
  | Priority.FP_policy _ => apply: (crr_forall_rel _); intros ? ? ?
  | seq _ => apply: (crr_forall_list _); intros ? ? ?
  | Suspension.job_suspension _ => apply: (crr_forall_susp _); intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: crr_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp; crel
  | lazymatch goal with
    | |- forall _, _ => intro; crel
    | |- CrrSchedRel _ (JitterScheduleConstruction.sched_jitter _ _ _ _ _ _ _ _) _ => eapply crr_JS_sched_jitter; crel
    | |- CrrParRel _ (ArrivalSequenceWithJitter.actual_arrival _ _) _ => intro; eapply crr_AJ_actual_arrival; crel
    | |- CrrParRel _ (JitterScheduleConstruction.inflated_job_cost _ _ _) _ => eapply crr_JS_inflated_job_cost; crel
    | |- CrrParRel _ (JitterScheduleConstruction.job_jitter _ _ _ _ _ _) _ => eapply crr_JS_job_jitter; crel
    | |- CrrJldpRel _ (Priority.FP_to_JLDP _ _) _ => eapply crr_PR_FP_to_JLDP; crel
    | |- CrrPredRel _ _ _ => intro; cbv beta; crel
    | |- CrrParRel _ (RTAByReduction.actual_response_time _ _ _ _ _) _ => intro; eapply RTAByReduction_actual_response_time_correspondence; crel
    | |- Lean.eq (cl_opt (JitterScheduleConstruction.build_schedule _ _ _ _ _ _ _ _ _ _)) _ => eapply crr_JS_build_schedule; crel
    | |- Lean.eq (cl_opt (?s _)) _ => first [ match goal with H : CrrSchedRel _ s _ |- _ => eapply H; crel end | eapply crr_JS_sched_jitter; crel ]
    | |- SubNatRel ?a _ => crel_n a
    | |- CtBoolRel ?b _ => crel_b b
    | |- ClListRel _ ?l _ => crel_l l
    | |- PropSPropRel ?P _ => crel_p P
    end ]
with crel_n a :=
  lazymatch a with
  | addn _ _ => eapply sub_add_correspondence; crel
  | subn _ _ => eapply ct_sub_rel; crel
  | S _ => eapply crr_succ_rel; crel
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
  | _ <-> _ => eapply crr_iff; crel
  | _ <> _ => eapply crr_ne
  | ~ _ => eapply ct_imp; [crel | exact crr_false_rel]
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else crel_eq_defs
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_eq_defs := first [ eapply ct_eq_rel | eapply crr_opt_rel_eq; crel ]
with crel_n_defs := first [ eapply RTAByReduction_actual_response_time_correspondence; crel
    | eapply ct_bool_to_nat; crel
    | eapply crr_US_service; crel
    | eapply crr_ijc_pt; crel
    | eapply crr_jj_pt; crel
    | eapply crr_US_service_during; crel
    | eapply crr_SI_suspension_duration; crel
    | eapply crr_AJ_actual_arrival; crel
    | eapply crr_US_service_at; crel ]
with crel_b_defs := first [ eapply crr_RT_is_response_time_bound_of_job; crel
    | eapply crr_US_scheduled_at; crel
    | eapply crr_US_completed_by; crel
    | eapply crr_has_arrived; crel
    | eapply crr_SI_suspended_at; crel
    | eapply crr_US_pending; crel
    | eapply crr_UJ_pending; crel
    | eapply crr_SS_backlogged; crel
    | eapply crr_AJ_jitter_has_passed; crel
    | eapply crr_arrives_at; crel ]
with crel_l_defs := first [ eapply crr_jobs_arrived_between; crel
    | eapply crr_AJ_actual_arrivals_between; crel
    | eapply crr_jobs_arrived_before; crel ]
with crel_p_defs := first [ eapply crr_TK_constrained_deadline_model; crel
    | eapply crr_false_rel; crel
    | eapply crr_arrives_in; crel
    | eapply crr_consistent; crel
    | eapply crr_mem; crel
    | eapply crr_US_jobs_come_from_arrival_sequence; crel
    | eapply crr_US_jobs_must_arrive_to_execute; crel
    | eapply crr_US_completed_jobs_dont_execute; crel
    | eapply crr_SP_work_conserving; crel
    | eapply crr_SP_respects_JLDP_policy; crel
    | eapply crr_SI_respects_self_suspensions; crel
    | eapply crr_PR_FP_is_reflexive; crel
    | eapply crr_PR_FP_is_transitive; crel
    | eapply crr_PR_FP_is_total_over_task_set; crel
    | eapply crr_VS_valid_suspension_aware_schedule; crel
    | eapply crr_RT_is_response_time_bound_of_job; crel
    | eapply crr_TA_sporadic_task_model; crel
    | eapply crr_is_a_set; crel
    | eapply crr_uniq; crel
    | eapply crr_RT_is_response_time_bound_of_task; crel ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_valid_response_time_bound_in_sched_susp (Task Job : eqType) : Prop :=
  forall p0 p1 : Task -> nat,
    ltac:(type_of_term (@RTAByReduction.valid_response_time_bound_in_sched_susp Task p0 p1 Job)).
Definition tgt_valid_response_time_bound_in_sched_susp (Task Job : eqType) : SProp :=
  forall p0 p1 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Jitter_RtaByReduction_RTAByReduction_valid_response_time_bound_in_sched_susp Task (ct_decidable_eq Task) p0 p1 Job (ct_decidable_eq Job))).
Theorem RTAByReduction_valid_response_time_bound_in_sched_susp_correspondence (Task Job : eqType) :
  PropSPropRel (src_valid_response_time_bound_in_sched_susp Task Job) (tgt_valid_response_time_bound_in_sched_susp Task Job).
Proof. unfold src_valid_response_time_bound_in_sched_susp, tgt_valid_response_time_bound_in_sched_susp. crel_spine. crel. Unshelve. all: crel. Qed.
