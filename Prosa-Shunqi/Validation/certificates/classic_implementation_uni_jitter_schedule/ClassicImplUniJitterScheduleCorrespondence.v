From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.minmax classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.jitter.arrival_sequence classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.jitter.schedule classic.model.schedule.uni.jitter.platform classic.model.schedule.uni.transformation.construction classic.implementation.uni.jitter.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicImplUniJitterSchedule.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicImplUniJitterScheduleBase ClassicImplUniJitterScheduleList.

Module I := ImportedClassicImplUniJitterSchedule.
Local Open Scope nat_scope.

(** Certificates for [classic/implementation/uni/jitter/schedule.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by its decision procedure
    ([ct_decidable_eq]); times by [SubNatRel]; job parameters (including jitters) pointwise through [SubNatRel]; arrival sequences
    pointwise on related times; JLDP policies pointwise on related times (Booleans); uniprocessor schedules pointwise
    through the option map; all with two-way totals.  [seq_min] as in the accepted classic minmax certificate; the
    construction from prefixes as in the accepted classic uniprocessor construction certificate (re-bound below; the
    construction function [highest_priority_job] maps related schedules and instants to related choices, so the
    scheduler itself is related to its Lean counterpart); [schedule_prefix] through its kernel-checked Lean recursion
    equations exported with the artifact.

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof is not
    used); every input is quantified and covered in both directions.
    The jitter-aware [pending], [actual_arrivals_up_to], [jobs_execute_after_jitter] and platform notions are related as in
    the accepted classic uniprocessor jitter certificates. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cuj_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cuj_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cuj_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cuj_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cuj_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cuj_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cuj_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cuj_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cuj_unmap_rel T l) PR PL).
Qed.

Definition CujParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cuj_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CujParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cuj_forall_cover _ _ (CujParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cuj_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cuj_natl s') end.

Definition cuj_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cuj_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cuj_one) (cuj_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cuj_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cuj_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cuj_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cuj_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cuj_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cuj_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cuj_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cuj_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cuj_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cuj_cl_append. reflexivity.
Qed.

Lemma cuj_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CujFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cuj_bigcat_rel (A : Type) fR fL (Hf : CujFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicImplUniJitterScheduleInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cuj_iota_range (nR - mR) 0) cuj_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cuj_cl_map_ext _ _ Hpt) (cuj_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cuj_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cuj_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CujArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cuj_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cuj_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cuj_arr_canonical aR : CujArrRel aR (cuj_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cuj_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cuj_arr_surjective aL : CujArrRel (cuj_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cuj_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CujArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cuj_forall_cover _ _ CujArrRel cuj_arr_to_target cuj_arr_to_source cuj_arr_canonical cuj_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cuj_jobs_arrived_between aR aL (Ha : CujArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cuj_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cuj_arrives_in aR aL (Ha : CujArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cuj_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cuj_consistent pR pL (Hp : CujParRel Job pR pL) aR aL (Ha : CujArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cuj_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cuj_jobs_arrived_before aR aL (Ha : CujArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job dJ aL tL).
Proof. exact (cuj_jobs_arrived_between Job aR aL Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma cuj_arrives_at aR aL (Ha : CujArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cuj_mem Job j _ _ (Ha tR tL Ht))). Qed.

End ArrivalDefs2.

Fixpoint cuj_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cuj_snatl s') end.

Lemma cuj_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cuj_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cuj_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cuj_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cuj_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cuj_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cuj_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CujFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cuj_fun_canonical FR FL (HF : CujFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cuj_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cuj_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CujFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cuj_nat_sub_canonical nR mR.
  rewrite cuj_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cuj_foldr_add FL FR (cuj_fun_canonical FR FL HF)).
  by rewrite cuj_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cuj_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cuj_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cuj_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cuj_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cuj_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CujSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cuj_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cuj_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cuj_sched_canonical sR : CujSchedRel sR (cuj_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cuj_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cuj_sched_surjective sL : CujSchedRel (cuj_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cuj_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cuj_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CujSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cuj_forall_cover _ _ CujSchedRel cuj_sched_to_target cuj_sched_to_source cuj_sched_canonical cuj_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cuj_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CujSchedRel Job sR (cuj_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CujSchedRel Job (cuj_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cuj_sched_canonical Job) (cuj_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CujSchedRel Job sR sL.

Lemma cuj_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cuj_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cuj_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cuj_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cuj_US_scheduled_at j tR tL Ht)). Qed.

Lemma cuj_service_at_fun j : CujFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cuj_US_service_at j kR kL Hk). Qed.

Lemma cuj_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cuj_ico _ _ _ _ _ _ H1 H2 (cuj_service_at_fun j)). Qed.

Lemma cuj_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cuj_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cuj_US_completed_by cR cL (Hc : CujParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cuj_US_service j tR tL Ht)). Qed.

Lemma cuj_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CujArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cuj_US_scheduled_at j tR tL Ht)).
  exact (cuj_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cuj_US_completed_jobs_dont_execute cR cL (Hc : CujParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cuj_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(** The imported [ArrivalSequenceWithJitter] definitions (as in the accepted classic jitter arrival_sequence certificate). *)
Section JitterArrDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cuj_AJ_actual_arrival pR pL (Hp : CujParRel Job pR pL) qR qL (Hq : CujParRel Job qR qL) j :
  SubNatRel (ArrivalSequenceWithJitter.actual_arrival pR qR j) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Hp j) (Hq j)). Qed.

Lemma cuj_AJ_jitter_has_passed pR pL (Hp : CujParRel Job pR pL) qR qL (Hq : CujParRel Job qR qL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequenceWithJitter.jitter_has_passed pR qR j tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_jitter_has_passed Job dJ pL qL j tL).
Proof. exact (ct_decide_le _ _ _ _ (cuj_AJ_actual_arrival pR pL Hp qR qL Hq j) Ht). Qed.

Lemma cuj_AJ_actual_arrivals_between pR pL (Hp : CujParRel Job pR pL) qR qL (Hq : CujParRel Job qR qL)
    aR aL (Ha : CujArrRel Job aR aL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_between pR qR aR t1R t2R) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_between Job dJ pL qL aL t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cuj_jobs_arrived_before Job aR aL Ha t2R t2L H2).
  have F := cl_filter cid _
              (fun j => I.Bool_and
                 (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j))
                    (I.Nat_decLe t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j)))
                 (I.Decidable_decide (I.LT_lt_inst1 Lean.Nat I.instLTNat (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)
                    (I.Nat_decLt (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)))
              (fun j => ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (cuj_AJ_actual_arrival pR pL Hp qR qL Hq j))
                                          (ct_decide_lt _ _ _ _ (cuj_AJ_actual_arrival pR pL Hp qR qL Hq j) H2))
              (ArrivalSequence.jobs_arrived_before aR t2R).
  rewrite -E in F. exact F.
Qed.

Lemma cuj_AJ_actual_arrivals_up_to pR pL (Hp : CujParRel Job pR pL) qR qL (Hq : CujParRel Job qR qL)
    aR aL (Ha : CujArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_up_to pR qR aR tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_up_to Job dJ pL qL aL tL).
Proof. exact (cuj_AJ_actual_arrivals_between pR pL Hp qR qL Hq aR aL Ha 0 _ (sub_nat_rel_canonical 0) tR.+1 _ (cuj_succ_rel tR tL Ht)). Qed.

End JitterArrDefs.

Section UjschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CujSchedRel Job sR sL.

Lemma cuj_UJ_pending aR aL (Ha : CujParRel Job aR aL) cR cL (Hc : CujParRel Job cR cL)
    jjR jjL (Hjj : CujParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.pending aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_pending Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cuj_AJ_jitter_has_passed Job aR aL Ha jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cuj_US_completed_by Job sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

Lemma cuj_UJ_backlogged aR aL (Ha : CujParRel Job aR aL) cR cL (Hc : CujParRel Job cR cL)
    jjR jjL (Hjj : CujParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.backlogged aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_backlogged Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cuj_UJ_pending aR aL Ha cR cL Hc jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cuj_US_scheduled_at Job sR sL Hs j tR tL Ht))).
Qed.

Lemma cuj_UJ_jobs_execute_after_jitter aR aL (Ha : CujParRel Job aR aL) jjR jjL (Hjj : CujParRel Job jjR jjL) :
  PropSPropRel (UniprocessorScheduleWithJitter.jobs_execute_after_jitter aR jjR sR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_jobs_execute_after_jitter Job dJ aL jjL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cuj_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (cuj_AJ_jitter_has_passed Job aR aL Ha jjR jjL Hjj j tR tL Ht)).
Qed.

End UjschedDefs.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CujRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cuj_rel_canonical (T : Type) (rR : T -> T -> bool) : CujRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cuj_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CujRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cuj_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CujRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cuj_forall_cover _ _ (CujRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cuj_rel_canonical T) (cuj_rel_surjective T) PR PL).
Qed.

Definition CujJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CujRelRel T (rR tR) (rL tL).

Lemma cuj_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CujJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cuj_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CujJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cuj_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CujJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cuj_forall_cover _ _ (CujJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cuj_jldp_canonical T) (cuj_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cuj_PR_JLDP_policy :
  And (forall rR : Priority.JLDP_policy Job, CujJldpRel Job rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLDP_policy Job dJ,
         CujJldpRel Job (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL).
Proof. exact (And_intro _ _ (cuj_jldp_canonical Job) (cuj_jldp_surjective Job)). Qed.

Lemma cuj_transitive (T : Type) rR rL (Hr : CujRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma cuj_PR_JLDP_is_transitive rR rL (Hr : CujJldpRel Job rR rL) :
  PropSPropRel (Priority.JLDP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_JLDP_is_transitive Job dJ rL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cuj_transitive Job _ _ (Hr tR tL Ht)). Qed.

Lemma cuj_PR_JLDP_is_total aR aL (Ha : CujArrRel Job aR aL) rR rL (Hr : CujJldpRel Job rR rL) :
  PropSPropRel (Priority.JLDP_is_total aR rR) (I.Prosa_Classic_Model_Priority_Priority_JLDP_is_total Job dJ aL rL).
Proof.
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cuj_arrives_in Job aR aL Ha j1).
  apply: ct_imp; first exact (cuj_arrives_in Job aR aL Ha j2).
  exact (ct_bool_truth _ _ (ct_bool_or _ _ _ _ (Hr tR tL Ht j1 j2) (Hr tR tL Ht j2 j1))).
Qed.

End PriodefsDefs.

Section UjplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CujSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (jjR : Job -> nat) (jjL : Job -> Lean.Nat).
Hypotheses (Ha : CujParRel Job aR aL) (Hc : CujParRel Job cR cL) (Hjj : CujParRel Job jjR jjL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CujArrRel Job arrR arrL.

Notation BL := (cuj_UJ_backlogged Job sR sL Hs aR aL Ha cR cL Hc jjR jjL Hjj).
Notation SA := (cuj_US_scheduled_at Job sR sL Hs).

Lemma cuj_UJP_work_conserving :
  PropSPropRel (Platform.work_conserving aR cR jjR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Platform_Platform_work_conserving Job dJ aL cL jjL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cuj_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (BL j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (SA j_other tR tL Ht)).
Qed.

Lemma cuj_UJP_respects_JLDP_policy hR hL (Hh : CujJldpRel Job hR hL) :
  PropSPropRel (Platform.respects_JLDP_policy aR cR jjR arrR sR hR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Platform_Platform_respects_JLDP_policy Job dJ aL cL jjL arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cuj_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (BL j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh tR tL Ht j_hp j)).
Qed.

End UjplatDefs.

(* ------------------------------------------------------------------ *)
(** * [seq_min] (as in the accepted classic minmax certificate) *)

Lemma cuj_opt_eq {A} (o1 o2 : option A) : PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
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

Lemma cuj_argmin_step x l :
  Logic.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (I.List_cons T1 x l))
    (I.Prosa_Classic_Util_Minmax_seq_argmin_match_1 T1 (fun _ => I.Option T1)
       (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL l)
       (fun y => I.ite (I.Option T1) (Lean.eq (relL (FL x) (FL y)) I.Bool_true) (I.instDecidableEqBool (relL (FL x) (FL y)) I.Bool_true)
                   (I.Option_some T1 x) (I.Option_some T1 y))
       (fun _ => I.Option_some T1 x)).
Proof. reflexivity. Qed.

Lemma cuj_argmin_rel : forall l,
  Logic.eq (cl_opt (seq_argmin relR FR l)) (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (cl_map cid l)).
Proof.
  elim => [|x l IH] //=. rewrite cuj_argmin_step -IH.
  case: (seq_argmin relR FR l) => [y|] //=.
  rewrite (ct_bool_rel_logic _ _ (Hcomp x y)). by case: (relR (FR x) (FR y)).
Qed.

Lemma cuj_argmin_eq l L (H : ClListRel cid l L) o :
  PropSPropRel (Logic.eq (seq_argmin relR FR l) o)
    (Lean.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL L) (cl_opt o)).
Proof. destruct H. rewrite -cuj_argmin_rel. exact (cuj_opt_eq _ _). Qed.

End MinmaxArg.

Lemma cuj_seq_min (T : eqType) relR relL (Hrel : forall a b, CtBoolRel (relR a b) (relL a b)) l :
  Logic.eq (cl_opt (seq_min relR l)) (I.Prosa_Classic_Util_Minmax_seq_min T (ct_decidable_eq T) relL (cl_map cid l)).
Proof. exact (cuj_argmin_rel T T T (ct_decidable_eq T) relR relL (@Datatypes.id T) (I.id T) (fun x y => Hrel _ _) l). Qed.

(* ------------------------------------------------------------------ *)
(** * Options *)

Lemma cuj_opt_rel_eq (A : Type) (o1 o2 : option A) l1 l2 :
  Lean.eq (cl_opt o1) l1 -> Lean.eq (cl_opt o2) l2 -> PropSPropRel (Logic.eq o1 o2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. destruct H1. destruct H2. apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cuj_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Definition cuj_lsym {A : Type} {x y : A} (E : Lean.eq x y) : Lean.eq y x :=
  match E in Lean.eq _ z return Lean.eq z x with Lean.eq_refl => @Lean.eq_refl _ _ end.

Lemma cuj_src_transport {A : Type} (P : A -> SProp) (x y : A) : Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

Lemma cuj_nat_input (nR : nat) (nL : Lean.Nat) : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
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
Hypothesis Hbuild : forall sR sL, CujSchedRel Job sR sL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (buildR sR tR)) (buildL sL tL).
Variables (baseR : UniprocessorSchedule.schedule Job) (baseL : LSched).
Hypothesis Hbase : CujSchedRel Job baseR baseL.

Lemma cuj_nat_eqb tR tL t'R t'L : SubNatRel tR tL -> SubNatRel t'R t'L ->
  CtBoolRel (tR == t'R) (I.Decidable_decide (Lean.eq tL t'L) (I.instDecidableEqNat tL t'L)).
Proof. intros Ht Ht'. exact (ct_decide_eq_nat _ _ _ _ Ht Ht'). Qed.

Lemma cuj_UC_update_schedule prevR prevL (Hprev : CujSchedRel Job prevR prevL) nR nL (Hn : SubNatRel nR nL) :
  CujSchedRel Job (@ScheduleConstruction.update_schedule Job buildR prevR nR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule Job dJ buildL prevL nL).
Proof.
  intros tR tL Ht. unfold ScheduleConstruction.update_schedule, I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule. cbv beta.
  apply: coq_eq_to_imported_eq.
  rewrite (ct_bool_rel_logic _ _ (cuj_nat_eqb tR tL nR nL Ht Hn)).
  case: (tR == nR).
  - exact (imported_eq_to_coq_eq _ _ (Hbuild prevR prevL Hprev tR tL Ht)).
  - exact (imported_eq_to_coq_eq _ _ (Hprev tR tL Ht)).
Qed.

Lemma cuj_prefix_canonical (mR : nat) :
  CujSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL (sub_nat_to_imported mR)).
Proof.
  induction mR as [|m IH].
  - refine (cuj_trs (cuj_lsym (I.Prosa_Validation_ClassicImplUniJitterScheduleInterface_production_schedule_prefix_zero Job dJ buildL baseL))
              (fun z => CujSchedRel Job _ z) _).
    exact (cuj_UC_update_schedule baseR baseL Hbase 0 _ (sub_nat_rel_canonical 0)).
  - assert (Hm1 : SubNatRel m.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
                                 (sub_nat_to_imported m) (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)))).
    { exact (cuj_src_transport (fun x => SubNatRel x _) _ _ (addn1 m)
               (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical 1))). }
    refine (cuj_trs Hm1 (fun z => CujSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR m.+1) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) _).
    refine (cuj_trs (cuj_lsym (I.Prosa_Validation_ClassicImplUniJitterScheduleInterface_production_schedule_prefix_succ Job dJ buildL baseL (sub_nat_to_imported m)))
              (fun z => CujSchedRel Job _ z) _).
    exact (cuj_UC_update_schedule _ _ IH _ _ Hm1).
Qed.

Lemma cuj_UC_schedule_prefix mR mL (Hm : SubNatRel mR mL) :
  CujSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL mL).
Proof. exact (cuj_trs Hm (fun z => CujSchedRel Job _ (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) (cuj_prefix_canonical mR)). Qed.

Lemma cuj_UC_build_schedule_from_prefixes :
  CujSchedRel Job (@ScheduleConstruction.build_schedule_from_prefixes Job buildR baseR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_build_schedule_from_prefixes Job dJ buildL baseL).
Proof. intros tR tL Ht. exact (cuj_UC_schedule_prefix tR tL Ht tR tL Ht). Qed.

End UconsConstruction.



(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (jjR : Job -> nat) (jjL : Job -> Lean.Nat).
Hypotheses (Hja : CujParRel Job jaR jaL) (Hc : CujParRel Job cR cL) (Hjj : CujParRel Job jjR jjL).
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CujArrRel Job aR aL.
Variables (hR : nat -> Job -> Job -> bool) (hL : Lean.Nat -> Job -> Job -> I.Bool).
Hypothesis Hh : CujJldpRel Job hR hL.

Theorem ConcreteScheduler_pending_jobs_correspondence sR sL (Hs : CujSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (@ConcreteScheduler.pending_jobs Job jaR cR jjR aR sR tR) (I.Prosa_Classic_Implementation_Uni_Jitter_Schedule_ConcreteScheduler_pending_jobs Job dJ jaL cL jjL aL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cuj_AJ_actual_arrivals_up_to Job jaR jaL Hja jjR jjL Hjj aR aL Ha tR tL Ht).
  have F := cl_filter cid _ (fun j => I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_pending Job dJ jaL cL jjL sL j tL)
              (fun j => cuj_UJ_pending Job sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j tR tL Ht) (ArrivalSequenceWithJitter.actual_arrivals_up_to jaR jjR aR tR).
  rewrite -E in F. exact F.
Qed.

Theorem ConcreteScheduler_highest_priority_job_correspondence sR sL (Hs : CujSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  Lean.eq (cl_opt (@ConcreteScheduler.highest_priority_job Job jaR cR jjR aR hR sR tR)) (I.Prosa_Classic_Implementation_Uni_Jitter_Schedule_ConcreteScheduler_highest_priority_job Job dJ jaL cL jjL aL hL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite /ConcreteScheduler.highest_priority_job (cuj_seq_min Job (hR tR) (hL tL) (Hh tR tL Ht)).
  rewrite -(cl_list_logic _ _ _ (ConcreteScheduler_pending_jobs_correspondence sR sL Hs tR tL Ht)).
  reflexivity.
Qed.

Lemma cuj_empty : CujSchedRel Job (fun _ => None) (fun _ => I.Option_none Job).
Proof. intros tR tL Ht. exact (@Lean.eq_refl _ _). Qed.

Theorem ConcreteScheduler_scheduler_correspondence :
  CujSchedRel Job (@ConcreteScheduler.scheduler Job jaR cR jjR aR hR) (I.Prosa_Classic_Implementation_Uni_Jitter_Schedule_ConcreteScheduler_scheduler Job dJ jaL cL jjL aL hL).
Proof.
  exact (cuj_UC_build_schedule_from_prefixes Job _ _ ConcreteScheduler_highest_priority_job_correspondence _ _ cuj_empty).
Qed.
End Defs.

Notation SCH := ConcreteScheduler_scheduler_correspondence.
Notation HPJ := ConcreteScheduler_highest_priority_job_correspondence.

(** [transitive r], unfolded on the Lean side (as in the accepted classic minmax certificate). *)
Lemma cuj_trans (T : Type) (R : T -> T -> bool) RL (HR : forall a b, CtBoolRel (R a b) (RL a b)) :
  PropSPropRel (transitive R)
    (forall y x z, Lean.eq (RL x y) I.Bool_true -> Lean.eq (RL y z) I.Bool_true -> Lean.eq (RL x z) I.Bool_true).
Proof.
  rewrite /transitive. apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (HR x y)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (HR y z)) (ct_bool_truth _ _ (HR x z))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_scheduler_depends_only_on_prefix (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_depends_only_on_prefix Job)).
Definition tgt_scheduler_depends_only_on_prefix (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Jitter_Schedule_ConcreteScheduler_scheduler_depends_only_on_prefix Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_depends_only_on_prefix_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_depends_only_on_prefix Job) (tgt_scheduler_depends_only_on_prefix Job).
Proof.
  unfold src_scheduler_depends_only_on_prefix, tgt_scheduler_depends_only_on_prefix.
  apply: cuj_forall_par => jaR jaL Hja. apply: cuj_forall_par => cR cL Hc. apply: cuj_forall_par => jjR jjL Hjj.
  apply: (cuj_forall_arr Job) => aR aL Ha.
  apply: (cuj_forall_jldp Job) => hR hL Hh.
  apply: (cuj_forall_sched Job) => s1R s1L Hs1. apply: (cuj_forall_sched Job) => s2R s2L Hs2.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp.
  { apply: ct_forall_nat => t0R t0L Ht0.
    apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht0 Ht).
    exact (cuj_opt_rel_eq _ _ _ _ _ (Hs1 t0R t0L Ht0) (Hs2 t0R t0L Ht0)). }
  exact (cuj_opt_rel_eq _ _ _ _ _ (HPJ Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh s1R s1L Hs1 tR tL Ht)
           (HPJ Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh s2R s2L Hs2 tR tL Ht)).
Qed.

Definition src_scheduler_uses_construction_function (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_uses_construction_function Job)).
Definition tgt_scheduler_uses_construction_function (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Jitter_Schedule_ConcreteScheduler_scheduler_uses_construction_function Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_uses_construction_function_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_uses_construction_function Job) (tgt_scheduler_uses_construction_function Job).
Proof.
  unfold src_scheduler_uses_construction_function, tgt_scheduler_uses_construction_function.
  apply: cuj_forall_par => jaR jaL Hja. apply: cuj_forall_par => cR cL Hc. apply: cuj_forall_par => jjR jjL Hjj.
  apply: (cuj_forall_arr Job) => aR aL Ha.
  apply: (cuj_forall_jldp Job) => hR hL Hh.
  apply: ct_forall_nat => tR tL Ht.
  have Hs := SCH Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh.
  exact (cuj_opt_rel_eq _ _ _ _ _ (Hs tR tL Ht) (HPJ Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh _ _ Hs tR tL Ht)).
Qed.

Definition src_scheduler_jobs_come_from_arrival_sequence (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_jobs_come_from_arrival_sequence Job)).
Definition tgt_scheduler_jobs_come_from_arrival_sequence (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Jitter_Schedule_ConcreteScheduler_scheduler_jobs_come_from_arrival_sequence Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_jobs_come_from_arrival_sequence_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_jobs_come_from_arrival_sequence Job) (tgt_scheduler_jobs_come_from_arrival_sequence Job).
Proof.
  unfold src_scheduler_jobs_come_from_arrival_sequence, tgt_scheduler_jobs_come_from_arrival_sequence.
  apply: cuj_forall_par => jaR jaL Hja. apply: cuj_forall_par => cR cL Hc. apply: cuj_forall_par => jjR jjL Hjj.
  apply: (cuj_forall_arr Job) => aR aL Ha.
  apply: (cuj_forall_jldp Job) => hR hL Hh.
  exact (cuj_US_jobs_come_from_arrival_sequence Job _ _ (SCH Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh) aR aL Ha).
Qed.

Definition src_scheduler_jobs_execute_after_jitter (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_jobs_execute_after_jitter Job)).
Definition tgt_scheduler_jobs_execute_after_jitter (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Jitter_Schedule_ConcreteScheduler_scheduler_jobs_execute_after_jitter Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_jobs_execute_after_jitter_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_jobs_execute_after_jitter Job) (tgt_scheduler_jobs_execute_after_jitter Job).
Proof.
  unfold src_scheduler_jobs_execute_after_jitter, tgt_scheduler_jobs_execute_after_jitter.
  apply: cuj_forall_par => jaR jaL Hja. apply: cuj_forall_par => cR cL Hc. apply: cuj_forall_par => jjR jjL Hjj.
  apply: (cuj_forall_arr Job) => aR aL Ha.
  apply: (cuj_forall_jldp Job) => hR hL Hh.
  exact (cuj_UJ_jobs_execute_after_jitter Job _ _ (SCH Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh) jaR jaL Hja jjR jjL Hjj).
Qed.

Definition src_scheduler_completed_jobs_dont_execute (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_completed_jobs_dont_execute Job)).
Definition tgt_scheduler_completed_jobs_dont_execute (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Jitter_Schedule_ConcreteScheduler_scheduler_completed_jobs_dont_execute Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_completed_jobs_dont_execute_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_completed_jobs_dont_execute Job) (tgt_scheduler_completed_jobs_dont_execute Job).
Proof.
  unfold src_scheduler_completed_jobs_dont_execute, tgt_scheduler_completed_jobs_dont_execute.
  apply: cuj_forall_par => jaR jaL Hja. apply: cuj_forall_par => cR cL Hc. apply: cuj_forall_par => jjR jjL Hjj.
  apply: (cuj_forall_arr Job) => aR aL Ha.
  apply: (cuj_forall_jldp Job) => hR hL Hh.
  exact (cuj_US_completed_jobs_dont_execute Job _ _ (SCH Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh) cR cL Hc).
Qed.

Definition src_scheduler_work_conserving (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_work_conserving Job)).
Definition tgt_scheduler_work_conserving (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Jitter_Schedule_ConcreteScheduler_scheduler_work_conserving Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_work_conserving_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_work_conserving Job) (tgt_scheduler_work_conserving Job).
Proof.
  unfold src_scheduler_work_conserving, tgt_scheduler_work_conserving.
  apply: cuj_forall_par => jaR jaL Hja. apply: cuj_forall_par => cR cL Hc. apply: cuj_forall_par => jjR jjL Hjj.
  apply: (cuj_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cuj_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cuj_forall_jldp Job) => hR hL Hh.
  exact (cuj_UJP_work_conserving Job _ _ (SCH Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh) jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha).
Qed.

Definition src_scheduler_respects_policy (Job : eqType) : Prop :=
  ltac:(type_of_term (@ConcreteScheduler.scheduler_respects_policy Job)).
Definition tgt_scheduler_respects_policy (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Implementation_Uni_Jitter_Schedule_ConcreteScheduler_scheduler_respects_policy Job (ct_decidable_eq Job))).
Theorem ConcreteScheduler_scheduler_respects_policy_correspondence (Job : eqType) :
  PropSPropRel (src_scheduler_respects_policy Job) (tgt_scheduler_respects_policy Job).
Proof.
  unfold src_scheduler_respects_policy, tgt_scheduler_respects_policy.
  apply: cuj_forall_par => jaR jaL Hja. apply: cuj_forall_par => cR cL Hc. apply: cuj_forall_par => jjR jjL Hjj.
  apply: (cuj_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cuj_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cuj_forall_jldp Job) => hR hL Hh.
  apply: ct_imp; first exact (cuj_PR_JLDP_is_transitive Job hR hL Hh).
  apply: ct_imp; first exact (cuj_PR_JLDP_is_total Job aR aL Ha hR hL Hh).
  exact (cuj_UJP_respects_JLDP_policy Job _ _ (SCH Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh) jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh).
Qed.
