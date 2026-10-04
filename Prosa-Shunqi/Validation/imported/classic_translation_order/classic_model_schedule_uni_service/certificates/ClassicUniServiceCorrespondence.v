From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import util.sum classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.priority classic.model.schedule.uni.schedule classic.model.schedule.uni.workload classic.model.schedule.uni.service.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniService.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniServiceBase ClassicUniServiceList.

Module I := ImportedClassicUniService.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/service.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job parameters
    pointwise through [SubNatRel]; uniprocessor schedules pointwise through the option map; arrival sequences pointwise
    on related times; job sequences elementwise; Boolean predicates and priority policies pointwise on Booleans; all
    with two-way totals.  The imported uniprocessor schedule and workload definitions are related as in the accepted
    classic certificates (re-bound below).

    Computation: [\sum_(j <- s | P j) F j] against the v0.6 [sumFiltered] and [\cat_(t1 <= t < t2) F t] against
    [bigCat], through the kernel-checked equations of [ClassicUniServiceInterface] (as in the accepted certificates);
    [predT] against [fun _ => true].

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma csv_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma csv_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma csv_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) csv_false_rel). Qed.

Lemma csv_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma csv_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma csv_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma csv_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma csv_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma csv_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (csv_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => csv_unmap_rel T l) PR PL).
Qed.

Definition CsvParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma csv_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CsvParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (csv_forall_cover _ _ (CsvParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint csv_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (csv_natl s') end.

Definition csv_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma csv_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) csv_one) (csv_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) csv_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (csv_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma csv_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (csv_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (csv_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma csv_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma csv_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma csv_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma csv_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH csv_cl_append. reflexivity.
Qed.

Lemma csv_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsvFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma csv_bigcat_rel (A : Type) fR fL (Hf : CsvFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicUniServiceInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (csv_iota_range (nR - mR) 0) csv_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (csv_cl_map_ext _ _ Hpt) (csv_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) csv_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite csv_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CsvArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition csv_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition csv_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma csv_arr_canonical aR : CsvArrRel aR (csv_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /csv_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma csv_arr_surjective aL : CsvArrRel (csv_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma csv_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CsvArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (csv_forall_cover _ _ CsvArrRel csv_arr_to_target csv_arr_to_source csv_arr_canonical csv_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma csv_jobs_arrived_between aR aL (Ha : CsvArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (csv_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma csv_arrives_in aR aL (Ha : CsvArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (csv_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma csv_consistent pR pL (Hp : CsvParRel Job pR pL) aR aL (Ha : CsvArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (csv_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma csv_is_a_set aR aL (Ha : CsvArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (csv_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma csv_arrives_at aR aL (Ha : CsvArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (csv_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma csv_has_arrived pR pL (Hp : CsvParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint csv_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (csv_snatl s') end.

Lemma csv_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (csv_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (csv_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma csv_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (csv_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (csv_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma csv_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsvFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma csv_fun_canonical FR FL (HF : CsvFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma csv_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma csv_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CsvFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := csv_nat_sub_canonical nR mR.
  rewrite csv_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (csv_foldr_add FL FR (csv_fun_canonical FR FL HF)).
  by rewrite csv_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition csv_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition csv_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma csv_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma csv_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (csv_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CsvSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition csv_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition csv_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma csv_sched_canonical sR : CsvSchedRel sR (csv_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /csv_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma csv_sched_surjective sL : CsvSchedRel (csv_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /csv_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma csv_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CsvSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (csv_forall_cover _ _ CsvSchedRel csv_sched_to_target csv_sched_to_source csv_sched_canonical csv_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma csv_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CsvSchedRel Job sR (csv_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CsvSchedRel Job (csv_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (csv_sched_canonical Job) (csv_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CsvSchedRel Job sR sL.

Lemma csv_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (csv_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (csv_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma csv_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (csv_US_scheduled_at j tR tL Ht)). Qed.

Lemma csv_service_at_fun j : CsvFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (csv_US_service_at j kR kL Hk). Qed.

Lemma csv_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (csv_ico _ _ _ _ _ _ H1 H2 (csv_service_at_fun j)). Qed.

Lemma csv_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (csv_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma csv_US_completed_by cR cL (Hc : CsvParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (csv_US_service j tR tL Ht)). Qed.

Lemma csv_US_is_idle tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.is_idle sR tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_is_idle Job dJ sL tL).
Proof.
  apply: ct_decide_bool.
  exact (csv_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == None) (Lean.eq z (cl_opt None)))
           (csv_opt_eqb_rel Job (sR tR) None)).
Qed.

Lemma csv_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CsvArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (csv_US_scheduled_at j tR tL Ht)).
  exact (csv_arrives_in Job arrR arrL Harr j).
Qed.

Lemma csv_US_jobs_must_arrive_to_execute aR aL (Ha : CsvParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (csv_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (csv_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma csv_US_completed_jobs_dont_execute cR cL (Hc : CsvParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (csv_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma csv_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicUniServiceInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicUniServiceInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma csv_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (csv_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma csv_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicUniServiceInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicUniServiceInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicUniServiceInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma csv_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (csv_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CsvPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma csv_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CsvPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (csv_forall_cover _ _ (CsvPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CsvRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma csv_rel_canonical (T : Type) (rR : T -> T -> bool) : CsvRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma csv_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CsvRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma csv_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CsvRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (csv_forall_cover _ _ (CsvRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (csv_rel_canonical T) (csv_rel_surjective T) PR PL).
Qed.

Definition CsvJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CsvRelRel T (rR tR) (rL tL).

Lemma csv_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CsvJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma csv_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CsvJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma csv_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CsvJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (csv_forall_cover _ _ (CsvJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (csv_jldp_canonical T) (csv_jldp_surjective T) PR PL).
Qed.

Section UwlDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma csv_WL_workload_of_jobs cR cL (Hc : CsvParRel Job cR cL) jobsR jobsL (Hj : ClListRel cid jobsR jobsL)
    pR pL (Hp : CsvPredRel Job pR pL) :
  SubNatRel (Workload.workload_of_jobs cR jobsR pR) (I.Prosa_Classic_Model_Schedule_Uni_Workload_Workload_workload_of_jobs Job dJ cL jobsL pL).
Proof. exact (csv_sum_filtered_rel Job cR cL Hc pR pL Hp _ _ Hj). Qed.

End UwlDefs.

Lemma csv_iff (P Q : Prop) (PL QL : SProp) :
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
(** * Definitions *)

Section Defs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CsvSchedRel Job sR sL.

Theorem Service_service_of_jobs_correspondence jobsR jobsL (Hj : ClListRel cid jobsR jobsL) pR pL (Hp : CsvPredRel Job pR pL)
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.service_of_jobs sR jobsR pR t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs Job dJ sL jobsL pL t1L t2L).
Proof.
  exact (csv_sum_filtered_rel Job (fun j => UniprocessorSchedule.service_during sR j t1R t2R)
           (fun j => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L)
           (fun j => csv_US_service_during Job sR sL Hs j _ _ H1 _ _ H2) pR pL Hp _ _ Hj).
Qed.

Theorem Service_service_of_higher_or_equal_priority_tasks_correspondence jobsR jobsL (Hj : ClListRel cid jobsR jobsL)
    (Task : eqType) (job_task : Job -> Task) hR hL (Hh : CsvRelRel Task hR hL) tsk
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.service_of_higher_or_equal_priority_tasks sR jobsR job_task hR tsk t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_higher_or_equal_priority_tasks Job dJ sL jobsL Task (ct_decidable_eq Task) job_task hL tsk t1L t2L).
Proof. exact (Service_service_of_jobs_correspondence _ _ Hj _ _ (fun j => Hh (job_task j) tsk) _ _ H1 _ _ H2). Qed.

Theorem Service_service_of_higher_or_equal_priority_jobs_correspondence jobsR jobsL (Hj : ClListRel cid jobsR jobsL)
    hR hL (Hh : CsvRelRel Job hR hL) j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.service_of_higher_or_equal_priority_jobs sR jobsR hR j t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_higher_or_equal_priority_jobs Job dJ sL jobsL hL j t1L t2L).
Proof. exact (Service_service_of_jobs_correspondence _ _ Hj _ _ (fun j_hp => Hh j_hp j) _ _ H1 _ _ H2). Qed.

Theorem Service_task_service_of_jobs_received_in_correspondence (Task : eqType) (job_task : Job -> Task)
    arrR arrL (Harr : CsvArrRel Job arrR arrL) tsk a1R a1L (Ha1 : SubNatRel a1R a1L) a2R a2L (Ha2 : SubNatRel a2R a2L)
    t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.task_service_of_jobs_received_in job_task arrR sR tsk a1R a2R t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_task_service_of_jobs_received_in Task (ct_decidable_eq Task) Job dJ job_task arrL sL tsk a1L a2L t1L t2L).
Proof.
  exact (Service_service_of_jobs_correspondence _ _ (csv_jobs_arrived_between Job arrR arrL Harr _ _ _ _ Ha1 Ha2)
           _ _ (fun j => ct_decide_eq Task (job_task j) tsk) _ _ H1 _ _ H2).
Qed.

Theorem Service_task_service_between_correspondence (Task : eqType) (job_task : Job -> Task)
    arrR arrL (Harr : CsvArrRel Job arrR arrL) tsk t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (Service.task_service_between job_task arrR sR tsk t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_task_service_between Task (ct_decidable_eq Task) Job dJ job_task arrL sL tsk t1L t2L).
Proof. exact (Service_task_service_of_jobs_received_in_correspondence Task job_task arrR arrL Harr tsk _ _ H1 _ _ H2 _ _ H1 _ _ H2). Qed.
End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation SOJ := Service_service_of_jobs_correspondence.
Notation WL := csv_WL_workload_of_jobs.

Definition src_service_of_jobs_le_workload (Job : eqType) : Prop :=
   ltac:(type_of_term (@Service.service_of_jobs_le_workload Job)).
Definition tgt_service_of_jobs_le_workload (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs_le_workload Job (ct_decidable_eq Job))).

Theorem Service_service_of_jobs_le_workload_correspondence (Job : eqType) :
  PropSPropRel (src_service_of_jobs_le_workload Job) (tgt_service_of_jobs_le_workload Job).
Proof.
  unfold src_service_of_jobs_le_workload, tgt_service_of_jobs_le_workload.
  apply: csv_forall_par => cR cL Hc. apply: csv_forall_sched => sR sL Hs.
  apply: csv_forall_list => jobsR jobsL Hj. apply: csv_forall_pred => pR pL Hp.
  apply: ct_imp; first exact (csv_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  exact (sub_nat_le_correspondence _ _ _ _ (SOJ Job sR sL Hs _ _ Hj _ _ Hp _ _ H1 _ _ H2) (WL Job cR cL Hc _ _ Hj _ _ Hp)).
Qed.
Definition src_service_of_jobs_le_delta (Job : eqType) : Prop :=
   ltac:(type_of_term (@Service.service_of_jobs_le_delta Job)).
Definition tgt_service_of_jobs_le_delta (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs_le_delta Job (ct_decidable_eq Job))).

Theorem Service_service_of_jobs_le_delta_correspondence (Job : eqType) :
  PropSPropRel (src_service_of_jobs_le_delta Job) (tgt_service_of_jobs_le_delta Job).
Proof.
  unfold src_service_of_jobs_le_delta, tgt_service_of_jobs_le_delta.
  apply: csv_forall_sched => sR sL Hs.
  apply: csv_forall_list => jobsR jobsL Hj. apply: csv_forall_pred => pR pL Hp.
  apply: ct_imp; first exact (csv_uniq Job _ _ Hj).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  exact (sub_nat_le_correspondence _ _ _ _ (SOJ Job sR sL Hs _ _ Hj _ _ Hp _ _ H1 _ _ H2) (ct_sub_rel _ _ _ _ H2 H1)).
Qed.
Definition src_service_monotonic (Job : eqType) : Prop :=
   ltac:(type_of_term (@Service.service_monotonic Job)).
Definition tgt_service_monotonic (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_monotonic Job (ct_decidable_eq Job))).

Theorem Service_service_monotonic_correspondence (Job : eqType) :
  PropSPropRel (src_service_monotonic Job) (tgt_service_monotonic Job).
Proof.
  unfold src_service_monotonic, tgt_service_monotonic.
  apply: csv_forall_sched => sR sL Hs.
  apply: ct_forall_identity => j. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 H2).
  exact (sub_nat_le_correspondence _ _ _ _ (csv_US_service Job sR sL Hs j _ _ H1) (csv_US_service Job sR sL Hs j _ _ H2)).
Qed.
Definition src_service_during_cat (Job : eqType) : Prop :=
   ltac:(type_of_term (@Service.service_during_cat Job)).
Definition tgt_service_during_cat (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_during_cat Job (ct_decidable_eq Job))).

Theorem Service_service_during_cat_correspondence (Job : eqType) :
  PropSPropRel (src_service_during_cat Job) (tgt_service_during_cat Job).
Proof.
  unfold src_service_during_cat, tgt_service_during_cat.
  apply: csv_forall_sched => sR sL Hs.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_le _ _ _ _ Ht H2))).
  exact (sub_nat_eq_correspondence _ _ _ _ (csv_US_service_during Job sR sL Hs j _ _ H1 _ _ H2)
           (sub_add_correspondence _ _ _ _ (csv_US_service_during Job sR sL Hs j _ _ H1 _ _ Ht) (csv_US_service_during Job sR sL Hs j _ _ Ht _ _ H2))).
Qed.
Definition src_incremental_service_during (Job : eqType) : Prop :=
   ltac:(type_of_term (@Service.incremental_service_during Job)).
Definition tgt_incremental_service_during (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_incremental_service_during Job (ct_decidable_eq Job))).

Theorem Service_incremental_service_during_correspondence (Job : eqType) :
  PropSPropRel (src_incremental_service_during Job) (tgt_incremental_service_during Job).
Proof.
  unfold src_incremental_service_during, tgt_incremental_service_during.
  apply: csv_forall_sched => sR sL Hs.
  apply: ct_forall_identity => j. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_forall_nat => kR kL Hk.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hk (csv_US_service_during Job sR sL Hs j _ _ H1 _ _ H2)).
  apply: ct_exists_nat => tR tL Ht.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  apply: ct_and; first exact (ct_bool_truth _ _ (csv_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (sub_nat_eq_correspondence _ _ _ _ (csv_US_service_during Job sR sL Hs j _ _ H1 _ _ Ht) Hk).
Qed.
Definition src_service_of_jobs_le_1 (Job : eqType) : Prop :=
   ltac:(type_of_term (@Service.service_of_jobs_le_1 Job)).
Definition tgt_service_of_jobs_le_1 (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs_le_1 Job (ct_decidable_eq Job))).

Theorem Service_service_of_jobs_le_1_correspondence (Job : eqType) :
  PropSPropRel (src_service_of_jobs_le_1 Job) (tgt_service_of_jobs_le_1 Job).
Proof.
  unfold src_service_of_jobs_le_1, tgt_service_of_jobs_le_1.
  apply: csv_forall_par => aR aL Ha. apply: csv_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (csv_consistent Job aR aL Ha arrR arrL Harr).
  apply: ct_imp; first exact (csv_is_a_set Job arrR arrL Harr).
  apply: csv_forall_sched => sR sL Hs.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => tR tL Ht.
  apply: csv_forall_pred => pR pL Hp.
  exact (sub_nat_le_correspondence _ _ _ _
           (csv_sum_filtered_rel Job _ _ (fun j => csv_US_service_at Job sR sL Hs j _ _ Ht) pR pL Hp _ _
              (csv_jobs_arrived_between Job arrR arrL Harr _ _ _ _ H1 H2)) (sub_nat_rel_canonical 1)).
Qed.
Definition src_total_service_of_jobs_le_delta (Job : eqType) : Prop :=
   ltac:(type_of_term (@Service.total_service_of_jobs_le_delta Job)).
Definition tgt_total_service_of_jobs_le_delta (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_total_service_of_jobs_le_delta Job (ct_decidable_eq Job))).

Theorem Service_total_service_of_jobs_le_delta_correspondence (Job : eqType) :
  PropSPropRel (src_total_service_of_jobs_le_delta Job) (tgt_total_service_of_jobs_le_delta Job).
Proof.
  unfold src_total_service_of_jobs_le_delta, tgt_total_service_of_jobs_le_delta.
  apply: csv_forall_par => aR aL Ha. apply: csv_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (csv_consistent Job aR aL Ha arrR arrL Harr).
  apply: ct_imp; first exact (csv_is_a_set Job arrR arrL Harr).
  apply: csv_forall_sched => sR sL Hs.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => dR dL Hd. apply: csv_forall_pred => pR pL Hp.
  have Htd := sub_add_correspondence _ _ _ _ Ht Hd.
  exact (sub_nat_le_correspondence _ _ _ _
           (csv_sum_filtered_rel Job _ _ (fun j => csv_US_service_during Job sR sL Hs j _ _ Ht _ _ Htd) pR pL Hp _ _
              (csv_jobs_arrived_between Job arrR arrL Harr _ _ _ _ Ht Htd)) Hd).
Qed.
Definition src_low_service_implies_existence_of_idle_time (Job : eqType) : Prop :=
   ltac:(type_of_term (@Service.low_service_implies_existence_of_idle_time Job)).
Definition tgt_low_service_implies_existence_of_idle_time (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_low_service_implies_existence_of_idle_time Job (ct_decidable_eq Job))).

Theorem Service_low_service_implies_existence_of_idle_time_correspondence (Job : eqType) :
  PropSPropRel (src_low_service_implies_existence_of_idle_time Job) (tgt_low_service_implies_existence_of_idle_time Job).
Proof.
  unfold src_low_service_implies_existence_of_idle_time, tgt_low_service_implies_existence_of_idle_time.
  apply: csv_forall_par => aR aL Ha. apply: csv_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (csv_consistent Job aR aL Ha arrR arrL Harr).
  apply: csv_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (csv_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (csv_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 H2).
  apply: ct_imp.
  { exact (sub_nat_lt_correspondence _ _ _ _
             (SOJ Job sR sL Hs _ _ (csv_jobs_arrived_between Job arrR arrL Harr _ _ _ _ (sub_nat_rel_canonical 0) H2)
                 predT (fun _ => I.Bool_true) (fun _ => ct_bool_canonical true) _ _ H1 _ _ H2)
             (ct_sub_rel _ _ _ _ H2 H1)). }
  apply: ct_exists_nat => tR tL Ht.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  exact (ct_bool_truth _ _ (csv_US_is_idle Job sR sL Hs _ _ Ht)).
Qed.
Definition src_service_of_jobs_cat_scheduling_interval (Job : eqType) : Prop :=
   ltac:(type_of_term (@Service.service_of_jobs_cat_scheduling_interval Job)).
Definition tgt_service_of_jobs_cat_scheduling_interval (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs_cat_scheduling_interval Job (ct_decidable_eq Job))).

Theorem Service_service_of_jobs_cat_scheduling_interval_correspondence (Job : eqType) :
  PropSPropRel (src_service_of_jobs_cat_scheduling_interval Job) (tgt_service_of_jobs_cat_scheduling_interval Job).
Proof.
  unfold src_service_of_jobs_cat_scheduling_interval, tgt_service_of_jobs_cat_scheduling_interval.
  apply: csv_forall_par => aR aL Ha. apply: csv_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (csv_consistent Job aR aL Ha arrR arrL Harr).
  apply: csv_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (csv_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: csv_forall_pred => pR pL Hp.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_le _ _ _ _ Ht H2))).
  have A := fun xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) => csv_jobs_arrived_between Job arrR arrL Harr _ _ _ _ Hx Hy.
  have S := fun jR jL (Hj : ClListRel cid jR jL) xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) =>
    SOJ Job sR sL Hs jR jL Hj pR pL Hp xR xL Hx yR yL Hy.
  exact (sub_nat_eq_correspondence _ _ _ _ (S _ _ (A _ _ H1 _ _ H2) _ _ H1 _ _ H2)
           (sub_add_correspondence _ _ _ _
              (sub_add_correspondence _ _ _ _ (S _ _ (A _ _ H1 _ _ Ht) _ _ H1 _ _ Ht) (S _ _ (A _ _ H1 _ _ Ht) _ _ Ht _ _ H2))
              (S _ _ (A _ _ Ht _ _ H2) _ _ Ht _ _ H2))).
Qed.
Definition src_service_of_jobs_cat_arrival_interval (Job : eqType) : Prop :=
   ltac:(type_of_term (@Service.service_of_jobs_cat_arrival_interval Job)).
Definition tgt_service_of_jobs_cat_arrival_interval (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_service_of_jobs_cat_arrival_interval Job (ct_decidable_eq Job))).

Theorem Service_service_of_jobs_cat_arrival_interval_correspondence (Job : eqType) :
  PropSPropRel (src_service_of_jobs_cat_arrival_interval Job) (tgt_service_of_jobs_cat_arrival_interval Job).
Proof.
  unfold src_service_of_jobs_cat_arrival_interval, tgt_service_of_jobs_cat_arrival_interval.
  apply: csv_forall_arr => arrR arrL Harr. apply: csv_forall_sched => sR sL Hs.
  apply: csv_forall_pred => pR pL Hp.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_le _ _ _ _ Ht H2))).
  have A := fun xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) => csv_jobs_arrived_between Job arrR arrL Harr _ _ _ _ Hx Hy.
  have S := fun jR jL (Hj : ClListRel cid jR jL) xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) =>
    SOJ Job sR sL Hs jR jL Hj pR pL Hp xR xL Hx yR yL Hy.
  exact (sub_nat_eq_correspondence _ _ _ _ (S _ _ (A _ _ H1 _ _ H2) _ _ Ht _ _ H2)
           (sub_add_correspondence _ _ _ _ (S _ _ (A _ _ H1 _ _ Ht) _ _ Ht _ _ H2) (S _ _ (A _ _ Ht _ _ H2) _ _ Ht _ _ H2))).
Qed.
Definition src_workload_eq_service_impl_all_jobs_have_completed (Job : eqType) : Prop :=
   ltac:(type_of_term (@Service.workload_eq_service_impl_all_jobs_have_completed Job)).
Definition tgt_workload_eq_service_impl_all_jobs_have_completed (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_workload_eq_service_impl_all_jobs_have_completed Job (ct_decidable_eq Job))).

Theorem Service_workload_eq_service_impl_all_jobs_have_completed_correspondence (Job : eqType) :
  PropSPropRel (src_workload_eq_service_impl_all_jobs_have_completed Job) (tgt_workload_eq_service_impl_all_jobs_have_completed Job).
Proof.
  unfold src_workload_eq_service_impl_all_jobs_have_completed, tgt_workload_eq_service_impl_all_jobs_have_completed.
  apply: csv_forall_par => aR aL Ha. apply: csv_forall_par => cR cL Hc. apply: csv_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (csv_consistent Job aR aL Ha arrR arrL Harr).
  apply: csv_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (csv_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (csv_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: csv_forall_pred => pR pL Hp.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => tcR tcL Htc.
  have Hj := csv_jobs_arrived_between Job arrR arrL Harr _ _ _ _ H1 H2.
  have EQ := sub_nat_eq_correspondence _ _ _ _ (WL Job cR cL Hc _ _ Hj _ _ Hp) (SOJ Job sR sL Hs _ _ Hj _ _ Hp _ _ H1 _ _ Htc).
  have ALL : PropSPropRel _ _ := ct_forall_identity _ _ _ (fun j =>
    ct_imp _ _ _ _ (csv_mem Job j _ _ Hj) (ct_imp _ _ _ _ (ct_bool_truth _ _ (Hp j))
      (ct_bool_truth _ _ (csv_US_completed_by Job sR sL Hs cR cL Hc j _ _ Htc)))).
  exact (ct_imp _ _ _ _ EQ ALL).
Qed.
Definition src_all_jobs_have_completed_impl_workload_eq_service (Job : eqType) : Prop :=
   ltac:(type_of_term (@Service.all_jobs_have_completed_impl_workload_eq_service Job)).
Definition tgt_all_jobs_have_completed_impl_workload_eq_service (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_all_jobs_have_completed_impl_workload_eq_service Job (ct_decidable_eq Job))).

Theorem Service_all_jobs_have_completed_impl_workload_eq_service_correspondence (Job : eqType) :
  PropSPropRel (src_all_jobs_have_completed_impl_workload_eq_service Job) (tgt_all_jobs_have_completed_impl_workload_eq_service Job).
Proof.
  unfold src_all_jobs_have_completed_impl_workload_eq_service, tgt_all_jobs_have_completed_impl_workload_eq_service.
  apply: csv_forall_par => aR aL Ha. apply: csv_forall_par => cR cL Hc. apply: csv_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (csv_consistent Job aR aL Ha arrR arrL Harr).
  apply: csv_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (csv_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (csv_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: csv_forall_pred => pR pL Hp.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => tcR tcL Htc.
  have Hj := csv_jobs_arrived_between Job arrR arrL Harr _ _ _ _ H1 H2.
  have EQ := sub_nat_eq_correspondence _ _ _ _ (WL Job cR cL Hc _ _ Hj _ _ Hp) (SOJ Job sR sL Hs _ _ Hj _ _ Hp _ _ H1 _ _ Htc).
  have ALL : PropSPropRel _ _ := ct_forall_identity _ _ _ (fun j =>
    ct_imp _ _ _ _ (csv_mem Job j _ _ Hj) (ct_imp _ _ _ _ (ct_bool_truth _ _ (Hp j))
      (ct_bool_truth _ _ (csv_US_completed_by Job sR sL Hs cR cL Hc j _ _ Htc)))).
  exact (ct_imp _ _ _ _ ALL EQ).
Qed.
Definition src_all_jobs_have_completed_equiv_workload_eq_service (Job : eqType) : Prop :=
   ltac:(type_of_term (@Service.all_jobs_have_completed_equiv_workload_eq_service Job)).
Definition tgt_all_jobs_have_completed_equiv_workload_eq_service (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Service_Service_all_jobs_have_completed_equiv_workload_eq_service Job (ct_decidable_eq Job))).

Theorem Service_all_jobs_have_completed_equiv_workload_eq_service_correspondence (Job : eqType) :
  PropSPropRel (src_all_jobs_have_completed_equiv_workload_eq_service Job) (tgt_all_jobs_have_completed_equiv_workload_eq_service Job).
Proof.
  unfold src_all_jobs_have_completed_equiv_workload_eq_service, tgt_all_jobs_have_completed_equiv_workload_eq_service.
  apply: csv_forall_par => aR aL Ha. apply: csv_forall_par => cR cL Hc. apply: csv_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (csv_consistent Job aR aL Ha arrR arrL Harr).
  apply: csv_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (csv_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (csv_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: csv_forall_pred => pR pL Hp.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2. apply: ct_forall_nat => tcR tcL Htc.
  have Hj := csv_jobs_arrived_between Job arrR arrL Harr _ _ _ _ H1 H2.
  have EQ := sub_nat_eq_correspondence _ _ _ _ (WL Job cR cL Hc _ _ Hj _ _ Hp) (SOJ Job sR sL Hs _ _ Hj _ _ Hp _ _ H1 _ _ Htc).
  have ALL : PropSPropRel _ _ := ct_forall_identity _ _ _ (fun j =>
    ct_imp _ _ _ _ (csv_mem Job j _ _ Hj) (ct_imp _ _ _ _ (ct_bool_truth _ _ (Hp j))
      (ct_bool_truth _ _ (csv_US_completed_by Job sR sL Hs cR cL Hc j _ _ Htc)))).
  exact (csv_iff _ _ _ _ ALL EQ).
Qed.
