From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.jitter.arrival_sequence classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.service classic.model.schedule.uni.workload classic.model.schedule.uni.jitter.schedule classic.model.schedule.uni.jitter.platform classic.model.schedule.uni.jitter.busy_interval.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniJitterBusyInterval.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniJitterBusyIntervalBase ClassicUniJitterBusyIntervalList.

Module I := ImportedClassicUniJitterBusyInterval.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/jitter/busy_interval.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by its decision procedure
    ([ct_decidable_eq]); times by [SubNatRel]; job parameters (arrivals, costs, jitters) pointwise through [SubNatRel];
    arrival sequences pointwise on related times; JLFP policies pointwise on Booleans; uniprocessor schedules pointwise
    through the option map; all with two-way totals.  The service, workload, jitter-arrival, jitter-schedule and
    jitter-platform notions as in the accepted classic certificates (re-bound below); the Prop-valued [quiet_time],
    [busy_interval_prefix] and [busy_interval] related for arbitrary related inputs.

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof is not
    used); every input is quantified and covered in both directions. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cbi_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cbi_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cbi_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cbi_false_rel). Qed.

Lemma cbi_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cbi_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cbi_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cbi_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cbi_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cbi_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cbi_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cbi_unmap_rel T l) PR PL).
Qed.

Definition CbiParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cbi_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CbiParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cbi_forall_cover _ _ (CbiParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cbi_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cbi_natl s') end.

Definition cbi_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cbi_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cbi_one) (cbi_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cbi_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cbi_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cbi_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cbi_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cbi_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cbi_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cbi_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cbi_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cbi_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cbi_cl_append. reflexivity.
Qed.

Lemma cbi_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CbiFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cbi_bigcat_rel (A : Type) fR fL (Hf : CbiFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicUniJitterBusyIntervalInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cbi_iota_range (nR - mR) 0) cbi_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cbi_cl_map_ext _ _ Hpt) (cbi_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cbi_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cbi_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CbiArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cbi_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cbi_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cbi_arr_canonical aR : CbiArrRel aR (cbi_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cbi_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cbi_arr_surjective aL : CbiArrRel (cbi_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cbi_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CbiArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cbi_forall_cover _ _ CbiArrRel cbi_arr_to_target cbi_arr_to_source cbi_arr_canonical cbi_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cbi_jobs_arrived_between aR aL (Ha : CbiArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (cbi_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma cbi_arrives_in aR aL (Ha : CbiArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cbi_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cbi_consistent pR pL (Hp : CbiParRel Job pR pL) aR aL (Ha : CbiArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cbi_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cbi_is_a_set aR aL (Ha : CbiArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cbi_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cbi_jobs_arrived_before aR aL (Ha : CbiArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_before aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_before Job dJ aL tL).
Proof. exact (cbi_jobs_arrived_between Job aR aL Ha 0 _ tR tL (sub_nat_rel_canonical 0) Ht). Qed.

Lemma cbi_arrives_at aR aL (Ha : CbiArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cbi_mem Job j _ _ (Ha tR tL Ht))). Qed.

End ArrivalDefs2.

Fixpoint cbi_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cbi_snatl s') end.

Lemma cbi_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cbi_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cbi_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cbi_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cbi_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cbi_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cbi_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CbiFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cbi_fun_canonical FR FL (HF : CbiFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cbi_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cbi_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CbiFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cbi_nat_sub_canonical nR mR.
  rewrite cbi_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cbi_foldr_add FL FR (cbi_fun_canonical FR FL HF)).
  by rewrite cbi_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cbi_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cbi_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cbi_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cbi_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cbi_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CbiSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cbi_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cbi_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cbi_sched_canonical sR : CbiSchedRel sR (cbi_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cbi_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cbi_sched_surjective sL : CbiSchedRel (cbi_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cbi_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cbi_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CbiSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cbi_forall_cover _ _ CbiSchedRel cbi_sched_to_target cbi_sched_to_source cbi_sched_canonical cbi_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cbi_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CbiSchedRel Job sR (cbi_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CbiSchedRel Job (cbi_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cbi_sched_canonical Job) (cbi_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CbiSchedRel Job sR sL.

Lemma cbi_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cbi_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cbi_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cbi_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cbi_US_scheduled_at j tR tL Ht)). Qed.

Lemma cbi_service_at_fun j : CbiFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cbi_US_service_at j kR kL Hk). Qed.

Lemma cbi_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cbi_ico _ _ _ _ _ _ H1 H2 (cbi_service_at_fun j)). Qed.

Lemma cbi_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cbi_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cbi_US_completed_by cR cL (Hc : CbiParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cbi_US_service j tR tL Ht)). Qed.

Lemma cbi_US_is_idle tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.is_idle sR tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_is_idle Job dJ sL tL).
Proof.
  apply: ct_decide_bool.
  exact (cbi_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == None) (Lean.eq z (cl_opt None)))
           (cbi_opt_eqb_rel Job (sR tR) None)).
Qed.

Lemma cbi_busy_fun : CbiFunRel (fun t => nat_of_bool (~~ UniprocessorSchedule.is_idle sR t))
    (fun t => I.Bool_toNat (I.Bool_not (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_is_idle Job dJ sL t))).
Proof. intros kR kL Hk. exact (ct_bool_to_nat _ _ (ct_bool_not _ _ (cbi_US_is_idle kR kL Hk))). Qed.

Lemma cbi_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CbiArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cbi_US_scheduled_at j tR tL Ht)).
  exact (cbi_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cbi_US_completed_jobs_dont_execute cR cL (Hc : CbiParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cbi_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cbi_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicUniJitterBusyIntervalInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicUniJitterBusyIntervalInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cbi_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cbi_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cbi_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicUniJitterBusyIntervalInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicUniJitterBusyIntervalInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicUniJitterBusyIntervalInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cbi_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cbi_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CbiPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma cbi_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CbiPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cbi_forall_cover _ _ (CbiPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CbiRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cbi_rel_canonical (T : Type) (rR : T -> T -> bool) : CbiRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cbi_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CbiRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cbi_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CbiRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cbi_forall_cover _ _ (CbiRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cbi_rel_canonical T) (cbi_rel_surjective T) PR PL).
Qed.

Definition CbiJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CbiRelRel T (rR tR) (rL tL).

Lemma cbi_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CbiJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cbi_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CbiJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cbi_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CbiJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cbi_forall_cover _ _ (CbiJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cbi_jldp_canonical T) (cbi_jldp_surjective T) PR PL).
Qed.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cbi_PR_JLFP_policy :
  And (forall rR : Priority.JLFP_policy Job, CbiRelRel Job rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLFP_policy Job dJ, CbiRelRel Job (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cbi_rel_canonical Job) (cbi_rel_surjective Job)). Qed.

Lemma cbi_reflexive (T : Type) rR rL (Hr : CbiRelRel T rR rL) :
  PropSPropRel (reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_reflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (Hr x x)). Qed.

Lemma cbi_transitive (T : Type) rR rL (Hr : CbiRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma cbi_PR_JLFP_is_reflexive rR rL (Hr : CbiRelRel Job rR rL) :
  PropSPropRel (Priority.JLFP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_JLFP_is_reflexive Job dJ rL).
Proof. exact (cbi_reflexive Job rR rL Hr). Qed.

Lemma cbi_PR_JLFP_is_transitive rR rL (Hr : CbiRelRel Job rR rL) :
  PropSPropRel (Priority.JLFP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_JLFP_is_transitive Job dJ rL).
Proof. exact (cbi_transitive Job rR rL Hr). Qed.

End PriodefsDefs.

Section UwlDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cbi_WL_workload_of_jobs cR cL (Hc : CbiParRel Job cR cL) jobsR jobsL (Hj : ClListRel cid jobsR jobsL)
    pR pL (Hp : CbiPredRel Job pR pL) :
  SubNatRel (Workload.workload_of_jobs cR jobsR pR) (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_workload_of_jobs Job dJ cL jobsL pL).
Proof. exact (cbi_sum_filtered_rel Job cR cL Hc pR pL Hp _ _ Hj). Qed.

Lemma cbi_WL_workload_of_higher_or_equal_priority_jobs cR cL (Hc : CbiParRel Job cR cL)
    jobsR jobsL (Hj : ClListRel cid jobsR jobsL) hR hL (Hh : CbiRelRel Job hR hL) j :
  SubNatRel (Workload.workload_of_higher_or_equal_priority_jobs cR jobsR hR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_workload_of_higher_or_equal_priority_jobs Job dJ cL jobsL hL j).
Proof. exact (cbi_WL_workload_of_jobs cR cL Hc jobsR jobsL Hj _ _ (fun j_hp => Hh j_hp j)). Qed.

End UwlDefs.

(** The imported [ArrivalSequenceWithJitter] definitions (as in the accepted classic jitter arrival_sequence certificate). *)
Section JitterArrDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cbi_AJ_actual_arrival pR pL (Hp : CbiParRel Job pR pL) qR qL (Hq : CbiParRel Job qR qL) j :
  SubNatRel (ArrivalSequenceWithJitter.actual_arrival pR qR j) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Hp j) (Hq j)). Qed.

Lemma cbi_AJ_jitter_has_passed pR pL (Hp : CbiParRel Job pR pL) qR qL (Hq : CbiParRel Job qR qL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequenceWithJitter.jitter_has_passed pR qR j tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_jitter_has_passed Job dJ pL qL j tL).
Proof. exact (ct_decide_le _ _ _ _ (cbi_AJ_actual_arrival pR pL Hp qR qL Hq j) Ht). Qed.

Lemma cbi_AJ_actual_arrival_before pR pL (Hp : CbiParRel Job pR pL) qR qL (Hq : CbiParRel Job qR qL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequenceWithJitter.actual_arrival_before pR qR j tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival_before Job dJ pL qL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (cbi_AJ_actual_arrival pR pL Hp qR qL Hq j) Ht). Qed.

Lemma cbi_AJ_actual_arrival_between pR pL (Hp : CbiParRel Job pR pL) qR qL (Hq : CbiParRel Job qR qL) j
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  CtBoolRel (ArrivalSequenceWithJitter.actual_arrival_between pR qR j t1R t2R) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival_between Job dJ pL qL j t1L t2L).
Proof.
  exact (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (cbi_AJ_actual_arrival pR pL Hp qR qL Hq j))
                             (ct_decide_lt _ _ _ _ (cbi_AJ_actual_arrival pR pL Hp qR qL Hq j) H2)).
Qed.

Lemma cbi_AJ_actual_arrivals_between pR pL (Hp : CbiParRel Job pR pL) qR qL (Hq : CbiParRel Job qR qL)
    aR aL (Ha : CbiArrRel Job aR aL) t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequenceWithJitter.actual_arrivals_between pR qR aR t1R t2R) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrivals_between Job dJ pL qL aL t1L t2L).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (cbi_jobs_arrived_before Job aR aL Ha t2R t2L H2).
  have F := cl_filter cid _
              (fun j => I.Bool_and
                 (I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j))
                    (I.Nat_decLe t1L (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j)))
                 (I.Decidable_decide (I.LT_lt_inst1 Lean.Nat I.instLTNat (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)
                    (I.Nat_decLt (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j) t2L)))
              (fun j => ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (cbi_AJ_actual_arrival pR pL Hp qR qL Hq j))
                                          (ct_decide_lt _ _ _ _ (cbi_AJ_actual_arrival pR pL Hp qR qL Hq j) H2))
              (ArrivalSequence.jobs_arrived_before aR t2R).
  rewrite -E in F. exact F.
Qed.

End JitterArrDefs.

Section UjschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CbiSchedRel Job sR sL.

Lemma cbi_UJ_pending aR aL (Ha : CbiParRel Job aR aL) cR cL (Hc : CbiParRel Job cR cL)
    jjR jjL (Hjj : CbiParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.pending aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_pending Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cbi_AJ_jitter_has_passed Job aR aL Ha jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cbi_US_completed_by Job sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

Lemma cbi_UJ_backlogged aR aL (Ha : CbiParRel Job aR aL) cR cL (Hc : CbiParRel Job cR cL)
    jjR jjL (Hjj : CbiParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.backlogged aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_backlogged Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cbi_UJ_pending aR aL Ha cR cL Hc jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cbi_US_scheduled_at Job sR sL Hs j tR tL Ht))).
Qed.

Lemma cbi_UJ_jobs_execute_after_jitter aR aL (Ha : CbiParRel Job aR aL) jjR jjL (Hjj : CbiParRel Job jjR jjL) :
  PropSPropRel (UniprocessorScheduleWithJitter.jobs_execute_after_jitter aR jjR sR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_jobs_execute_after_jitter Job dJ aL jjL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cbi_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (cbi_AJ_jitter_has_passed Job aR aL Ha jjR jjL Hjj j tR tL Ht)).
Qed.

End UjschedDefs.

Section UjplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CbiSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (jjR : Job -> nat) (jjL : Job -> Lean.Nat).
Hypotheses (Ha : CbiParRel Job aR aL) (Hc : CbiParRel Job cR cL) (Hjj : CbiParRel Job jjR jjL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CbiArrRel Job arrR arrL.

Notation BL := (cbi_UJ_backlogged Job sR sL Hs aR aL Ha cR cL Hc jjR jjL Hjj).
Notation SA := (cbi_US_scheduled_at Job sR sL Hs).

Lemma cbi_UJP_work_conserving :
  PropSPropRel (Platform.work_conserving aR cR jjR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Platform_Platform_work_conserving Job dJ aL cL jjL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cbi_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (BL j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (SA j_other tR tL Ht)).
Qed.

Lemma cbi_UJP_respects_JLFP_policy hR hL (Hh : CbiRelRel Job hR hL) :
  PropSPropRel (Platform.respects_JLFP_policy aR cR jjR arrR sR hR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Platform_Platform_respects_JLFP_policy Job dJ aL cL jjL arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cbi_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (BL j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh j_hp j)).
Qed.

End UjplatDefs.



(* ------------------------------------------------------------------ *)
(** * Service of jobs (as in the accepted classic uniprocessor service certificate) *)

Section Svc.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CbiSchedRel Job sR sL.

Lemma cbi_service_of_jobs jobsR jobsL (Hj : ClListRel cid jobsR jobsL) pR pL (Hp : CbiPredRel Job pR pL)
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.service_of_jobs sR jobsR pR t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs Job dJ sL jobsL pL t1L t2L).
Proof.
  exact (cbi_sum_filtered_rel Job (fun j => UniprocessorSchedule.service_during sR j t1R t2R)
           (fun j => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L)
           (fun j => cbi_US_service_during Job sR sL Hs j _ _ H1 _ _ H2) pR pL Hp _ _ Hj).
Qed.

Lemma cbi_service_of_hep_jobs jobsR jobsL (Hj : ClListRel cid jobsR jobsL)
    hR hL (Hh : CbiRelRel Job hR hL) j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.service_of_higher_or_equal_priority_jobs sR jobsR hR j t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_higher_or_equal_priority_jobs Job dJ sL jobsL hL j t1L t2L).
Proof. exact (cbi_service_of_jobs _ _ Hj _ _ (fun j_hp => Hh j_hp j) _ _ H1 _ _ H2). Qed.
End Svc.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (jjR : Job -> nat) (jjL : Job -> Lean.Nat).
Hypotheses (Hja : CbiParRel Job jaR jaL) (Hc : CbiParRel Job cR cL) (Hjj : CbiParRel Job jjR jjL).
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CbiArrRel Job aR aL.
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CbiSchedRel Job sR sL.
Variables (hR : Job -> Job -> bool) (hL : Job -> Job -> I.Bool).
Hypothesis Hh : CbiRelRel Job hR hL.
Variable j : Job.

Theorem BusyInterval_quiet_time_correspondence tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (@BusyInterval.quiet_time Job jaR cR jjR aR sR hR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_quiet_time Job dJ jaL cL jjL aL sL hL j tL).
Proof.
  apply: ct_forall_identity => j_hp.
  apply: ct_imp; first exact (cbi_arrives_in Job aR aL Ha j_hp).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hh j_hp j)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cbi_AJ_actual_arrival_before Job jaR jaL Hja jjR jjL Hjj j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (cbi_US_completed_by Job sR sL Hs cR cL Hc j_hp tR tL Ht)).
Qed.

Notation QT := BusyInterval_quiet_time_correspondence.

Lemma cbi_not_quiet tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (~ @BusyInterval.quiet_time Job jaR cR jjR aR sR hR j tR) (I.Not (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_quiet_time Job dJ jaL cL jjL aL sL hL j tL)).
Proof. exact (ct_imp _ _ _ _ (QT tR tL Ht) cbi_false_rel). Qed.

Theorem BusyInterval_busy_interval_prefix_correspondence t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (@BusyInterval.busy_interval_prefix Job jaR cR jjR aR sR hR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_busy_interval_prefix Job dJ jaL cL jjL aL sL hL j t1L t2L).
Proof.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ H1 H2).
  apply: ct_and; first exact (QT t1R t1L H1).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  exact (cbi_not_quiet tR tL Ht).
Qed.

Theorem BusyInterval_busy_interval_correspondence t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  PropSPropRel (@BusyInterval.busy_interval Job jaR cR jjR aR sR hR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_busy_interval Job dJ jaL cL jjL aL sL hL j t1L t2L).
Proof. exact (ct_and _ _ _ _ (BusyInterval_busy_interval_prefix_correspondence t1R t1L H1 t2R t2L H2) (QT t2R t2L H2)). Qed.
End Defs.

Notation QTc := BusyInterval_quiet_time_correspondence.
Notation NQc := cbi_not_quiet.
Notation BPc := BusyInterval_busy_interval_prefix_correspondence.
Notation BIc := BusyInterval_busy_interval_correspondence.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_job_completes_within_busy_interval (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyInterval.job_completes_within_busy_interval Job)).
Definition tgt_job_completes_within_busy_interval (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_job_completes_within_busy_interval Job (ct_decidable_eq Job))).
Theorem BusyInterval_job_completes_within_busy_interval_correspondence (Job : eqType) :
  PropSPropRel (src_job_completes_within_busy_interval Job) (tgt_job_completes_within_busy_interval Job).
Proof.
  unfold src_job_completes_within_busy_interval, tgt_job_completes_within_busy_interval.
  apply: cbi_forall_par => jaR jaL Hja. apply: cbi_forall_par => cR cL Hc. apply: cbi_forall_par => jjR jjL Hjj.
  apply: (cbi_forall_arr Job) => aR aL Ha.
  apply: (cbi_forall_sched Job) => sR sL Hs.
  apply: (cbi_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cbi_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cbi_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_forall_nat => t1R t1L H1.
  apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (BIc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ H1 _ _ H2).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cbi_UJ_pending Job sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j tR tL Ht)).
  exact (ct_bool_truth _ _ (cbi_US_completed_by Job sR sL Hs cR cL Hc j _ _ H2)).
Qed.

Definition src_job_arrives_within_busy_interval (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyInterval.job_arrives_within_busy_interval Job)).
Definition tgt_job_arrives_within_busy_interval (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_job_arrives_within_busy_interval Job (ct_decidable_eq Job))).
Theorem BusyInterval_job_arrives_within_busy_interval_correspondence (Job : eqType) :
  PropSPropRel (src_job_arrives_within_busy_interval Job) (tgt_job_arrives_within_busy_interval Job).
Proof.
  unfold src_job_arrives_within_busy_interval, tgt_job_arrives_within_busy_interval.
  apply: cbi_forall_par => jaR jaL Hja. apply: cbi_forall_par => cR cL Hc. apply: cbi_forall_par => jjR jjL Hjj.
  apply: (cbi_forall_arr Job) => aR aL Ha.
  apply: (cbi_forall_sched Job) => sR sL Hs.
  apply: (cbi_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cbi_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cbi_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_forall_nat => t1R t1L H1.
  apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (BIc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ H1 _ _ H2).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (cbi_UJ_pending Job sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j tR tL Ht)).
  exact (sub_nat_le_correspondence _ _ _ _ H1 (cbi_AJ_actual_arrival Job jaR jaL Hja jjR jjL Hjj j)).
Qed.

Definition src_not_quiet_implies_exists_pending_job (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyInterval.not_quiet_implies_exists_pending_job Job)).
Definition tgt_not_quiet_implies_exists_pending_job (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_not_quiet_implies_exists_pending_job Job (ct_decidable_eq Job))).
Theorem BusyInterval_not_quiet_implies_exists_pending_job_correspondence (Job : eqType) :
  PropSPropRel (src_not_quiet_implies_exists_pending_job Job) (tgt_not_quiet_implies_exists_pending_job Job).
Proof.
  unfold src_not_quiet_implies_exists_pending_job, tgt_not_quiet_implies_exists_pending_job.
  apply: cbi_forall_par => jaR jaL Hja. apply: cbi_forall_par => cR cL Hc. apply: cbi_forall_par => jjR jjL Hjj.
  apply: (cbi_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cbi_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cbi_forall_sched Job) => sR sL Hs.
  apply: (cbi_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1.
  apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 H2).
  apply: ct_imp; first exact (QTc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ H1).
  apply: ct_imp; first exact (NQc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ H2).
  apply: ct_exists_identity => j_hp.
  apply: ct_and; first exact (cbi_arrives_in Job aR aL Ha j_hp).
  apply: ct_and; first exact (ct_bool_truth _ _ (cbi_AJ_actual_arrival_between Job jaR jaL Hja jjR jjL Hjj j_hp _ _ H1 _ _ H2)).
  apply: ct_and; first exact (ct_bool_truth _ _ (Hh j_hp j)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (cbi_US_completed_by Job sR sL Hs cR cL Hc j_hp _ _ H2)) cbi_false_rel).
Qed.

Definition src_not_quiet_implies_not_idle (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyInterval.not_quiet_implies_not_idle Job)).
Definition tgt_not_quiet_implies_not_idle (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_not_quiet_implies_not_idle Job (ct_decidable_eq Job))).
Theorem BusyInterval_not_quiet_implies_not_idle_correspondence (Job : eqType) :
  PropSPropRel (src_not_quiet_implies_not_idle Job) (tgt_not_quiet_implies_not_idle Job).
Proof.
  unfold src_not_quiet_implies_not_idle, tgt_not_quiet_implies_not_idle.
  apply: cbi_forall_par => jaR jaL Hja. apply: cbi_forall_par => cR cL Hc. apply: cbi_forall_par => jjR jjL Hjj.
  apply: (cbi_forall_arr Job) => aR aL Ha.
  apply: (cbi_forall_sched Job) => sR sL Hs.
  apply: (cbi_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cbi_UJP_work_conserving Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha).
  apply: ct_forall_nat => t1R t1L H1.
  apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ H1 H2).
  apply: ct_imp.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_le _ _ _ _ Ht H2))).
    exact (NQc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ Ht). }
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_le _ _ _ _ Ht H2))).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (cbi_US_is_idle Job sR sL Hs tR tL Ht)) cbi_false_rel).
Qed.

Definition src_not_quiet_implies_exists_scheduled_hp_job (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyInterval.not_quiet_implies_exists_scheduled_hp_job Job)).
Definition tgt_not_quiet_implies_exists_scheduled_hp_job (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_not_quiet_implies_exists_scheduled_hp_job Job (ct_decidable_eq Job))).
Theorem BusyInterval_not_quiet_implies_exists_scheduled_hp_job_correspondence (Job : eqType) :
  PropSPropRel (src_not_quiet_implies_exists_scheduled_hp_job Job) (tgt_not_quiet_implies_exists_scheduled_hp_job Job).
Proof.
  unfold src_not_quiet_implies_exists_scheduled_hp_job, tgt_not_quiet_implies_exists_scheduled_hp_job.
  apply: cbi_forall_par => jaR jaL Hja. apply: cbi_forall_par => cR cL Hc. apply: cbi_forall_par => jjR jjL Hjj.
  apply: (cbi_forall_arr Job) => aR aL Ha.
  apply: (cbi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cbi_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: (cbi_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cbi_UJP_work_conserving Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha).
  apply: ct_imp; first exact (cbi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cbi_UJ_jobs_execute_after_jitter Job sR sL Hs jaR jaL Hja jjR jjL Hjj).
  apply: ct_forall_nat => t1R t1L H1.
  apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ H1 H2).
  apply: ct_imp; first exact (QTc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ H1).
  apply: ct_imp.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_le _ _ _ _ Ht H2))).
    exact (NQc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ Ht). }
  apply: ct_imp; first exact (cbi_PR_JLFP_is_transitive Job hR hL Hh).
  apply: ct_imp; first exact (cbi_UJP_respects_JLFP_policy Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: ct_exists_identity => j_hp.
  apply: ct_and; first exact (ct_bool_truth _ _ (cbi_AJ_actual_arrival_between Job jaR jaL Hja jjR jjL Hjj j_hp _ _ H1 _ _ H2)).
  apply: ct_and; first exact (ct_bool_truth _ _ (Hh j_hp j)).
  exact (ct_bool_truth _ _ (cbi_US_scheduled_at Job sR sL Hs j_hp tR tL Ht)).
Qed.

Definition src_exists_busy_interval_prefix (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyInterval.exists_busy_interval_prefix Job)).
Definition tgt_exists_busy_interval_prefix (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_exists_busy_interval_prefix Job (ct_decidable_eq Job))).
Theorem BusyInterval_exists_busy_interval_prefix_correspondence (Job : eqType) :
  PropSPropRel (src_exists_busy_interval_prefix Job) (tgt_exists_busy_interval_prefix Job).
Proof.
  unfold src_exists_busy_interval_prefix, tgt_exists_busy_interval_prefix.
  apply: cbi_forall_par => jaR jaL Hja. apply: cbi_forall_par => cR cL Hc. apply: cbi_forall_par => jjR jjL Hjj.
  apply: (cbi_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cbi_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cbi_forall_sched Job) => sR sL Hs.
  apply: (cbi_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cbi_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cbi_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_forall_nat => bR bL Hb.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cbi_UJ_pending Job sR sL Hs jaR jaL Hja cR cL Hc jjR jjL Hjj j bR bL Hb)).
  apply: ct_exists_nat => t1R t1L H1.
  apply: ct_and; first exact (BPc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ H1 _ _ (cbi_succ_rel _ _ Hb)).
  exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (cbi_AJ_actual_arrival Job jaR jaL Hja jjR jjL Hjj j)) (ct_decide_le _ _ _ _ (cbi_AJ_actual_arrival Job jaR jaL Hja jjR jjL Hjj j) Hb))).
Qed.

Definition src_busy_interval_has_uninterrupted_service (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyInterval.busy_interval_has_uninterrupted_service Job)).
Definition tgt_busy_interval_has_uninterrupted_service (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_busy_interval_has_uninterrupted_service Job (ct_decidable_eq Job))).
Theorem BusyInterval_busy_interval_has_uninterrupted_service_correspondence (Job : eqType) :
  PropSPropRel (src_busy_interval_has_uninterrupted_service Job) (tgt_busy_interval_has_uninterrupted_service Job).
Proof.
  unfold src_busy_interval_has_uninterrupted_service, tgt_busy_interval_has_uninterrupted_service.
  apply: cbi_forall_par => jaR jaL Hja. apply: cbi_forall_par => cR cL Hc. apply: cbi_forall_par => jjR jjL Hjj.
  apply: (cbi_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cbi_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cbi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cbi_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: (cbi_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cbi_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (cbi_UJ_jobs_execute_after_jitter Job sR sL Hs jaR jaL Hja jjR jjL Hjj).
  apply: ct_imp; first exact (cbi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cbi_UJP_work_conserving Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha).
  apply: ct_imp; first exact (cbi_UJP_respects_JLFP_policy Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh).
  apply: ct_imp; first exact (cbi_PR_JLFP_is_transitive Job hR hL Hh).
  apply: ct_forall_nat => bR bL Hb.
  apply: ct_forall_nat => t1R t1L H1.
  apply: ct_imp; first exact (BPc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ H1 _ _ (cbi_succ_rel _ _ Hb)).
  apply: ct_forall_nat => deltaR deltaL Hdelta.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdelta).
  apply: ct_imp.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_le _ _ _ _ Ht (sub_add_correspondence _ _ _ _ H1 Hdelta)))).
    exact (NQc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ Ht). }
  exact (sub_nat_eq_correspondence _ _ _ _ (cbi_service_of_hep_jobs Job sR sL Hs _ _ (cbi_AJ_actual_arrivals_between Job jaR jaL Hja jjR jjL Hjj aR aL Ha _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hdelta)) hR hL Hh j _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hdelta)) Hdelta).
Qed.

Definition src_busy_interval_too_much_workload (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyInterval.busy_interval_too_much_workload Job)).
Definition tgt_busy_interval_too_much_workload (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_busy_interval_too_much_workload Job (ct_decidable_eq Job))).
Theorem BusyInterval_busy_interval_too_much_workload_correspondence (Job : eqType) :
  PropSPropRel (src_busy_interval_too_much_workload Job) (tgt_busy_interval_too_much_workload Job).
Proof.
  unfold src_busy_interval_too_much_workload, tgt_busy_interval_too_much_workload.
  apply: cbi_forall_par => jaR jaL Hja. apply: cbi_forall_par => cR cL Hc. apply: cbi_forall_par => jjR jjL Hjj.
  apply: (cbi_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cbi_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cbi_forall_sched Job) => sR sL Hs.
  apply: (cbi_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cbi_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (cbi_UJ_jobs_execute_after_jitter Job sR sL Hs jaR jaL Hja jjR jjL Hjj).
  apply: ct_imp; first exact (cbi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_nat => bR bL Hb.
  apply: ct_forall_nat => t1R t1L H1.
  apply: ct_imp; first exact (BPc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ H1 _ _ (cbi_succ_rel _ _ Hb)).
  apply: ct_forall_nat => deltaR deltaL Hdelta.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdelta).
  apply: ct_imp.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_le _ _ _ _ Ht (sub_add_correspondence _ _ _ _ H1 Hdelta)))).
    exact (NQc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ Ht). }
  exact (sub_nat_lt_correspondence _ _ _ _ (cbi_service_of_hep_jobs Job sR sL Hs _ _ (cbi_AJ_actual_arrivals_between Job jaR jaL Hja jjR jjL Hjj aR aL Ha _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hdelta)) hR hL Hh j _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hdelta)) (cbi_WL_workload_of_higher_or_equal_priority_jobs Job cR cL Hc _ _ (cbi_AJ_actual_arrivals_between Job jaR jaL Hja jjR jjL Hjj aR aL Ha _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hdelta)) hR hL Hh j)).
Qed.

Definition src_busy_interval_workload_larger_than_interval (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyInterval.busy_interval_workload_larger_than_interval Job)).
Definition tgt_busy_interval_workload_larger_than_interval (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_busy_interval_workload_larger_than_interval Job (ct_decidable_eq Job))).
Theorem BusyInterval_busy_interval_workload_larger_than_interval_correspondence (Job : eqType) :
  PropSPropRel (src_busy_interval_workload_larger_than_interval Job) (tgt_busy_interval_workload_larger_than_interval Job).
Proof.
  unfold src_busy_interval_workload_larger_than_interval, tgt_busy_interval_workload_larger_than_interval.
  apply: cbi_forall_par => jaR jaL Hja. apply: cbi_forall_par => cR cL Hc. apply: cbi_forall_par => jjR jjL Hjj.
  apply: (cbi_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cbi_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cbi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cbi_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: (cbi_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cbi_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (cbi_UJ_jobs_execute_after_jitter Job sR sL Hs jaR jaL Hja jjR jjL Hjj).
  apply: ct_imp; first exact (cbi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cbi_UJP_work_conserving Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha).
  apply: ct_imp; first exact (cbi_UJP_respects_JLFP_policy Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh).
  apply: ct_imp; first exact (cbi_PR_JLFP_is_transitive Job hR hL Hh).
  apply: ct_forall_nat => bR bL Hb.
  apply: ct_forall_nat => t1R t1L H1.
  apply: ct_imp; first exact (BPc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ H1 _ _ (cbi_succ_rel _ _ Hb)).
  apply: ct_forall_nat => deltaR deltaL Hdelta.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdelta).
  apply: ct_imp.
  { apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_lt _ _ _ _ H1 Ht) (ct_decide_le _ _ _ _ Ht (sub_add_correspondence _ _ _ _ H1 Hdelta)))).
    exact (NQc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ Ht). }
  exact (sub_nat_lt_correspondence _ _ _ _ Hdelta (cbi_WL_workload_of_higher_or_equal_priority_jobs Job cR cL Hc _ _ (cbi_AJ_actual_arrivals_between Job jaR jaL Hja jjR jjL Hjj aR aL Ha _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hdelta)) hR hL Hh j)).
Qed.

Definition src_busy_interval_is_bounded (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyInterval.busy_interval_is_bounded Job)).
Definition tgt_busy_interval_is_bounded (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_busy_interval_is_bounded Job (ct_decidable_eq Job))).
Theorem BusyInterval_busy_interval_is_bounded_correspondence (Job : eqType) :
  PropSPropRel (src_busy_interval_is_bounded Job) (tgt_busy_interval_is_bounded Job).
Proof.
  unfold src_busy_interval_is_bounded, tgt_busy_interval_is_bounded.
  apply: cbi_forall_par => jaR jaL Hja. apply: cbi_forall_par => cR cL Hc. apply: cbi_forall_par => jjR jjL Hjj.
  apply: (cbi_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cbi_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cbi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cbi_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: (cbi_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cbi_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (cbi_UJ_jobs_execute_after_jitter Job sR sL Hs jaR jaL Hja jjR jjL Hjj).
  apply: ct_imp; first exact (cbi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cbi_UJP_work_conserving Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha).
  apply: ct_imp; first exact (cbi_UJP_respects_JLFP_policy Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh).
  apply: ct_imp; first exact (cbi_PR_JLFP_is_transitive Job hR hL Hh).
  apply: ct_forall_nat => bR bL Hb.
  apply: ct_forall_nat => t1R t1L H1.
  apply: ct_imp; first exact (BPc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ H1 _ _ (cbi_succ_rel _ _ Hb)).
  apply: ct_forall_nat => deltaR deltaL Hdelta.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdelta).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (cbi_WL_workload_of_higher_or_equal_priority_jobs Job cR cL Hc _ _ (cbi_AJ_actual_arrivals_between Job jaR jaL Hja jjR jjL Hjj aR aL Ha _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hdelta)) hR hL Hh j) Hdelta).
  apply: ct_exists_nat => t2R t2L H2.
  apply: ct_and; first exact (sub_nat_le_correspondence _ _ _ _ H2 (sub_add_correspondence _ _ _ _ H1 Hdelta)).
  exact (BIc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ H1 _ _ H2).
Qed.

Definition src_exists_busy_interval (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyInterval.exists_busy_interval Job)).
Definition tgt_exists_busy_interval (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_exists_busy_interval Job (ct_decidable_eq Job))).
Theorem BusyInterval_exists_busy_interval_correspondence (Job : eqType) :
  PropSPropRel (src_exists_busy_interval Job) (tgt_exists_busy_interval Job).
Proof.
  unfold src_exists_busy_interval, tgt_exists_busy_interval.
  apply: cbi_forall_par => jaR jaL Hja. apply: cbi_forall_par => cR cL Hc. apply: cbi_forall_par => jjR jjL Hjj.
  apply: (cbi_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cbi_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cbi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cbi_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: (cbi_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cbi_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cbi_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (cbi_UJ_jobs_execute_after_jitter Job sR sL Hs jaR jaL Hja jjR jjL Hjj).
  apply: ct_imp; first exact (cbi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cbi_UJP_work_conserving Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha).
  apply: ct_imp; first exact (cbi_UJP_respects_JLFP_policy Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh).
  apply: ct_imp; first exact (cbi_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_imp; first exact (cbi_PR_JLFP_is_transitive Job hR hL Hh).
  apply: ct_forall_nat => deltaR deltaL Hdelta.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdelta).
  apply: ct_imp.
  { apply: ct_forall_nat => t1R t1L H1.
    exact (sub_nat_le_correspondence _ _ _ _ (cbi_WL_workload_of_higher_or_equal_priority_jobs Job cR cL Hc _ _ (cbi_AJ_actual_arrivals_between Job jaR jaL Hja jjR jjL Hjj aR aL Ha _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hdelta)) hR hL Hh j) Hdelta). }
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (Hc j)).
  apply: ct_exists_nat => t1R t1L H1. apply: ct_exists_nat => t2R t2L H2.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 (cbi_AJ_actual_arrival Job jaR jaL Hja jjR jjL Hjj j)) (ct_decide_lt _ _ _ _ (cbi_AJ_actual_arrival Job jaR jaL Hja jjR jjL Hjj j) H2))).
  apply: ct_and; first exact (sub_nat_le_correspondence _ _ _ _ H2 (sub_add_correspondence _ _ _ _ H1 Hdelta)).
  exact (BIc Job jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha sR sL Hs hR hL Hh j _ _ H1 _ _ H2).
Qed.

Definition src_busy_interval_bounds_response_time (Job : eqType) : Prop :=
  ltac:(type_of_term (@BusyInterval.busy_interval_bounds_response_time Job)).
Definition tgt_busy_interval_bounds_response_time (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_BusyInterval_BusyInterval_busy_interval_bounds_response_time Job (ct_decidable_eq Job))).
Theorem BusyInterval_busy_interval_bounds_response_time_correspondence (Job : eqType) :
  PropSPropRel (src_busy_interval_bounds_response_time Job) (tgt_busy_interval_bounds_response_time Job).
Proof.
  unfold src_busy_interval_bounds_response_time, tgt_busy_interval_bounds_response_time.
  apply: cbi_forall_par => jaR jaL Hja. apply: cbi_forall_par => cR cL Hc. apply: cbi_forall_par => jjR jjL Hjj.
  apply: (cbi_forall_arr Job) => aR aL Ha.
  apply: ct_imp; first exact (cbi_consistent Job jaR jaL Hja aR aL Ha).
  apply: (cbi_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cbi_US_jobs_come_from_arrival_sequence Job sR sL Hs aR aL Ha).
  apply: (cbi_forall_rel Job) => hR hL Hh.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cbi_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cbi_is_a_set Job aR aL Ha).
  apply: ct_imp; first exact (cbi_UJ_jobs_execute_after_jitter Job sR sL Hs jaR jaL Hja jjR jjL Hjj).
  apply: ct_imp; first exact (cbi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (cbi_UJP_work_conserving Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha).
  apply: ct_imp; first exact (cbi_UJP_respects_JLFP_policy Job sR sL Hs jaR jaL cR cL jjR jjL Hja Hc Hjj aR aL Ha hR hL Hh).
  apply: ct_imp; first exact (cbi_PR_JLFP_is_reflexive Job hR hL Hh).
  apply: ct_imp; first exact (cbi_PR_JLFP_is_transitive Job hR hL Hh).
  apply: ct_forall_nat => deltaR deltaL Hdelta.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) Hdelta).
  apply: ct_imp.
  { apply: ct_forall_nat => t1R t1L H1.
    exact (sub_nat_le_correspondence _ _ _ _ (cbi_WL_workload_of_higher_or_equal_priority_jobs Job cR cL Hc _ _ (cbi_AJ_actual_arrivals_between Job jaR jaL Hja jjR jjL Hjj aR aL Ha _ _ H1 _ _ (sub_add_correspondence _ _ _ _ H1 Hdelta)) hR hL Hh j) Hdelta). }
  exact (ct_bool_truth _ _ (cbi_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (cbi_AJ_actual_arrival Job jaR jaL Hja jjR jjL Hjj j) Hdelta))).
Qed.
