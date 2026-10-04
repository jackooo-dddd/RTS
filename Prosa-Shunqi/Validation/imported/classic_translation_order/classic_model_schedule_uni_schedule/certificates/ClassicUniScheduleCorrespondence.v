From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import util.unit_growth classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.schedule.uni.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniSchedule.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniScheduleBase ClassicUniScheduleList ClassicUniScheduleOrd.

Module I := ImportedClassicUniSchedule.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/schedule.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job parameters
    [Job -> time] pointwise through [SubNatRel]; uniprocessor schedules [time -> option Job] pointwise on related
    times through the option map ([CusSchedRel]); arrival sequences pointwise on related times (as in the accepted
    classic arrival_sequence certificate); all with two-way totals.

    Computation: [sched t == Some j] / [sched t == None] against [decide (sched t = some j)] / [decide (sched t =
    none)] through the option map ([ct_decide_bool], the decision procedures are never unfolded); [nat_of_bool]
    against [Bool.toNat]; the half-open sums [\sum_(t1 <= t < t2) F t] against the projected Lean fold
    [List.foldr Nat.add 0 (List.map F (List.range' t1 (t2 - t1) 1))] — the export form of [service_during] /
    [total_service_during] (definition-body projections guarded by kernel-checked [rfl] equalities) and of the two
    statements with [Finset.Ico] sums (kernel-checked normalization guards), related by [cus_ico] as in the accepted
    classic sum / schedule certificates; [[exists t : 'I_n, P t]] against [(List.finRange n).any P] ([co_exists_rel],
    through the exported kernel-checked [finRange_any]).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cus_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cus_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cus_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cus_false_rel). Qed.

Lemma cus_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cus_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cus_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cus_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Definition CusParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cus_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CusParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cus_forall_cover _ _ (CusParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cus_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cus_natl s') end.

Definition cus_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cus_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cus_one) (cus_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cus_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cus_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cus_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cus_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cus_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CusFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CusArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cus_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cus_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cus_arr_canonical aR : CusArrRel aR (cus_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cus_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cus_arr_surjective aL : CusArrRel (cus_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cus_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CusArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cus_forall_cover _ _ CusArrRel cus_arr_to_target cus_arr_to_source cus_arr_canonical cus_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cus_arrives_in aR aL (Ha : CusArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cus_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cus_has_arrived pR pL (Hp : CusParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

Lemma cus_arrived_before pR pL (Hp : CusParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrived_before pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrived_before Job dJ pL j tL).
Proof. exact (ct_decide_lt _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cus_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cus_snatl s') end.

Lemma cus_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cus_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cus_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cus_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cus_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cus_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cus_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CusFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cus_fun_canonical FR FL (HF : CusFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cus_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cus_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CusFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cus_nat_sub_canonical nR mR.
  rewrite cus_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cus_foldr_add FL FR (cus_fun_canonical FR FL HF)).
  by rewrite cus_big_fold.
Qed.


(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cus_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cus_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cus_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cus_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CusSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cus_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cus_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cus_sched_canonical sR : CusSchedRel sR (cus_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cus_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cus_sched_surjective sL : CusSchedRel (cus_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cus_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cus_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CusSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cus_forall_cover _ _ CusSchedRel cus_sched_to_target cus_sched_to_source cus_sched_canonical cus_sched_surjective PR PL). Qed.
End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem UniprocessorSchedule_schedule_correspondence (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CusSchedRel Job sR (cus_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CusSchedRel Job (cus_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cus_sched_canonical Job) (cus_sched_surjective Job)). Qed.

Section Defs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CusSchedRel Job sR sL.

Theorem UniprocessorSchedule_scheduled_at_correspondence j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cus_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cus_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Theorem UniprocessorSchedule_service_at_correspondence j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (UniprocessorSchedule_scheduled_at_correspondence j tR tL Ht)). Qed.

Lemma cus_service_at_fun j : CusFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (UniprocessorSchedule_service_at_correspondence j kR kL Hk). Qed.

Theorem UniprocessorSchedule_service_during_correspondence j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cus_ico _ _ _ _ _ _ H1 H2 (cus_service_at_fun j)). Qed.

Theorem UniprocessorSchedule_service_correspondence j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (UniprocessorSchedule_service_during_correspondence j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Theorem UniprocessorSchedule_completed_by_correspondence cR cL (Hc : CusParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (UniprocessorSchedule_service_correspondence j tR tL Ht)). Qed.

Theorem UniprocessorSchedule_pending_correspondence aR aL (Ha : CusParRel Job aR aL) cR cL (Hc : CusParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cus_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (UniprocessorSchedule_completed_by_correspondence cR cL Hc j tR tL Ht))).
Qed.

Theorem UniprocessorSchedule_pending_earlier_and_at_correspondence aR aL (Ha : CusParRel Job aR aL) cR cL (Hc : CusParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending_earlier_and_at aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending_earlier_and_at Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cus_arrived_before Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (UniprocessorSchedule_completed_by_correspondence cR cL Hc j tR tL Ht))).
Qed.

Theorem UniprocessorSchedule_backlogged_correspondence aR aL (Ha : CusParRel Job aR aL) cR cL (Hc : CusParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.backlogged aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_backlogged Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (UniprocessorSchedule_pending_correspondence aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (UniprocessorSchedule_scheduled_at_correspondence j tR tL Ht))).
Qed.

Theorem UniprocessorSchedule_is_idle_correspondence tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.is_idle sR tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_is_idle Job dJ sL tL).
Proof.
  apply: ct_decide_bool.
  exact (cus_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == None) (Lean.eq z (cl_opt None)))
           (cus_opt_eqb_rel Job (sR tR) None)).
Qed.

Lemma cus_busy_fun : CusFunRel (fun t => nat_of_bool (~~ UniprocessorSchedule.is_idle sR t))
    (fun t => I.Bool_toNat (I.Bool_not (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_is_idle Job dJ sL t))).
Proof. intros kR kL Hk. exact (ct_bool_to_nat _ _ (ct_bool_not _ _ (UniprocessorSchedule_is_idle_correspondence kR kL Hk))). Qed.

Theorem UniprocessorSchedule_total_service_during_correspondence t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.total_service_during sR t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_total_service_during Job dJ sL t1L t2L).
Proof. exact (cus_ico _ _ _ _ _ _ H1 H2 cus_busy_fun). Qed.

Theorem UniprocessorSchedule_total_service_correspondence tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.total_service sR tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_total_service Job dJ sL tL).
Proof. exact (UniprocessorSchedule_total_service_during_correspondence 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Theorem UniprocessorSchedule_sequential_jobs_correspondence (Task : eqType) aR aL (Ha : CusParRel Job aR aL) cR cL (Hc : CusParRel Job cR cL)
    (job_task : Job -> Task) :
  PropSPropRel (UniprocessorSchedule.sequential_jobs aR cR sR job_task)
    (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_sequential_jobs Job dJ aL cL sL Task (ct_decidable_eq Task) job_task).
Proof.
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_eq Task (job_task j1) (job_task j2))).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha j1) (Ha j2)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (UniprocessorSchedule_scheduled_at_correspondence j2 tR tL Ht)).
  exact (ct_bool_truth _ _ (UniprocessorSchedule_completed_by_correspondence cR cL Hc j1 tR tL Ht)).
Qed.

Theorem UniprocessorSchedule_jobs_come_from_arrival_sequence_correspondence arrR arrL (Harr : CusArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (UniprocessorSchedule_scheduled_at_correspondence j tR tL Ht)).
  exact (cus_arrives_in Job arrR arrL Harr j).
Qed.

Theorem UniprocessorSchedule_jobs_must_arrive_to_execute_correspondence aR aL (Ha : CusParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (UniprocessorSchedule_scheduled_at_correspondence j tR tL Ht)).
  exact (ct_bool_truth _ _ (cus_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Theorem UniprocessorSchedule_completed_jobs_dont_execute_correspondence cR cL (Hc : CusParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (UniprocessorSchedule_service_correspondence j tR tL Ht) (Hc j)).
Qed.

Theorem UniprocessorSchedule_remaining_cost_correspondence cR cL (Hc : CusParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.remaining_cost cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_remaining_cost Job dJ cL sL j tL).
Proof. exact (ct_sub_rel _ _ _ _ (Hc j) (UniprocessorSchedule_service_correspondence j tR tL Ht)). Qed.
End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation SA := UniprocessorSchedule_scheduled_at_correspondence.
Notation SV := UniprocessorSchedule_service_correspondence.
Notation SD := UniprocessorSchedule_service_during_correspondence.
Notation CB := UniprocessorSchedule_completed_by_correspondence.
Notation c0 := (sub_nat_rel_canonical 0).

Definition src_scheduler_executes_job_with_earliest_arrival (Job Task : eqType) : Prop :=
  ltac:(type_of_term (fun ja jc s => @UniprocessorSchedule.scheduler_executes_job_with_earliest_arrival Job ja jc s Task)).
Definition tgt_scheduler_executes_job_with_earliest_arrival (Job Task : eqType) : SProp :=
  ltac:(type_of_term (fun ja jc s => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduler_executes_job_with_earliest_arrival Job (ct_decidable_eq Job) ja jc s
                                       Task (ct_decidable_eq Task))).

(** The task type sits after [job_arrival job_cost sched] in both binder lists; it is fixed as an [eqType] with its
    canonical Lean instance (the instantiation used for every other type parameter). *)
Theorem UniprocessorSchedule_scheduler_executes_job_with_earliest_arrival_correspondence (Job Task : eqType) :
  PropSPropRel (src_scheduler_executes_job_with_earliest_arrival Job Task)
    (tgt_scheduler_executes_job_with_earliest_arrival Job Task).
Proof.
  unfold src_scheduler_executes_job_with_earliest_arrival, tgt_scheduler_executes_job_with_earliest_arrival.
  apply: cus_forall_par => aR aL Ha. apply: cus_forall_par => cR cL Hc. apply: cus_forall_sched => sR sL Hs.
  apply: ct_forall_identity => job_task.
  apply: ct_imp; first exact (UniprocessorSchedule_sequential_jobs_correspondence Job sR sL Hs Task aR aL Ha cR cL Hc job_task).
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_eq Task (job_task j1) (job_task j2))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (CB Job sR sL Hs cR cL Hc j2 tR tL Ht))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA Job sR sL Hs j1 tR tL Ht)).
  exact (sub_nat_le_correspondence _ _ _ _ (Ha j1) (Ha j2)).
Qed.

Definition src_service_at_most_one (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.service_at_most_one Job)).
Definition tgt_service_at_most_one (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at_most_one Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_service_at_most_one_correspondence (Job : eqType) :
  PropSPropRel (src_service_at_most_one Job) (tgt_service_at_most_one Job).
Proof.
  unfold src_service_at_most_one, tgt_service_at_most_one.
  apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (UniprocessorSchedule_service_at_correspondence Job sR sL Hs j tR tL Ht) (sub_nat_rel_canonical 1)).
Qed.

Definition src_cumulative_service_le_delta (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.cumulative_service_le_delta Job)).
Definition tgt_cumulative_service_le_delta (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_cumulative_service_le_delta Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_cumulative_service_le_delta_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_service_le_delta Job) (tgt_cumulative_service_le_delta Job).
Proof.
  unfold src_cumulative_service_le_delta, tgt_cumulative_service_le_delta.
  apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => dR dL Hd.
  exact (sub_nat_le_correspondence _ _ _ _ (SD Job sR sL Hs j tR tL Ht _ _ (sub_add_correspondence _ _ _ _ Ht Hd)) Hd).
Qed.

Definition src_scheduled_implies_positive_remaining_cost (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.scheduled_implies_positive_remaining_cost Job)).
Definition tgt_scheduled_implies_positive_remaining_cost (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_implies_positive_remaining_cost Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_scheduled_implies_positive_remaining_cost_correspondence (Job : eqType) :
  PropSPropRel (src_scheduled_implies_positive_remaining_cost Job) (tgt_scheduled_implies_positive_remaining_cost Job).
Proof.
  unfold src_scheduled_implies_positive_remaining_cost, tgt_scheduled_implies_positive_remaining_cost.
  apply: cus_forall_par => cR cL Hc. apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (UniprocessorSchedule_completed_jobs_dont_execute_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA Job sR sL Hs j tR tL Ht)).
  exact (sub_nat_lt_correspondence _ _ _ _ c0 (UniprocessorSchedule_remaining_cost_correspondence Job sR sL Hs cR cL Hc j tR tL Ht)).
Qed.

Definition src_completion_monotonic (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.completion_monotonic Job)).
Definition tgt_completion_monotonic (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completion_monotonic Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_completion_monotonic_correspondence (Job : eqType) :
  PropSPropRel (src_completion_monotonic Job) (tgt_completion_monotonic Job).
Proof.
  unfold src_completion_monotonic, tgt_completion_monotonic.
  apply: cus_forall_par => cR cL Hc. apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Ht Ht').
  apply: ct_imp; first exact (ct_bool_truth _ _ (CB Job sR sL Hs cR cL Hc j tR tL Ht)).
  exact (ct_bool_truth _ _ (CB Job sR sL Hs cR cL Hc j t'R t'L Ht')).
Qed.

Definition src_completed_implies_not_scheduled (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.completed_implies_not_scheduled Job)).
Definition tgt_completed_implies_not_scheduled (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_implies_not_scheduled Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_completed_implies_not_scheduled_correspondence (Job : eqType) :
  PropSPropRel (src_completed_implies_not_scheduled Job) (tgt_completed_implies_not_scheduled Job).
Proof.
  unfold src_completed_implies_not_scheduled, tgt_completed_implies_not_scheduled.
  apply: cus_forall_par => cR cL Hc. apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (UniprocessorSchedule_completed_jobs_dont_execute_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (CB Job sR sL Hs cR cL Hc j tR tL Ht)).
  exact (ct_bool_truth _ _ (ct_bool_not _ _ (SA Job sR sL Hs j tR tL Ht))).
Qed.

Definition src_scheduled_implies_not_completed (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.scheduled_implies_not_completed Job)).
Definition tgt_scheduled_implies_not_completed (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_implies_not_completed Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_scheduled_implies_not_completed_correspondence (Job : eqType) :
  PropSPropRel (src_scheduled_implies_not_completed Job) (tgt_scheduled_implies_not_completed Job).
Proof.
  unfold src_scheduled_implies_not_completed, tgt_scheduled_implies_not_completed.
  apply: cus_forall_par => cR cL Hc. apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (UniprocessorSchedule_completed_jobs_dont_execute_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA Job sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (ct_bool_not _ _ (CB Job sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

Definition src_cumulative_service_le_job_cost (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.cumulative_service_le_job_cost Job)).
Definition tgt_cumulative_service_le_job_cost (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_cumulative_service_le_job_cost Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_cumulative_service_le_job_cost_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_service_le_job_cost Job) (tgt_cumulative_service_le_job_cost Job).
Proof.
  unfold src_cumulative_service_le_job_cost, tgt_cumulative_service_le_job_cost.
  apply: cus_forall_par => cR cL Hc. apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (UniprocessorSchedule_completed_jobs_dont_execute_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => t'R t'L Ht'.
  exact (sub_nat_le_correspondence _ _ _ _ (SD Job sR sL Hs j tR tL Ht t'R t'L Ht') (Hc j)).
Qed.

Definition src_job_doesnt_complete_before_remaining_cost (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.job_doesnt_complete_before_remaining_cost Job)).
Definition tgt_job_doesnt_complete_before_remaining_cost (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_job_doesnt_complete_before_remaining_cost Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_job_doesnt_complete_before_remaining_cost_correspondence (Job : eqType) :
  PropSPropRel (src_job_doesnt_complete_before_remaining_cost Job) (tgt_job_doesnt_complete_before_remaining_cost Job).
Proof.
  unfold src_job_doesnt_complete_before_remaining_cost, tgt_job_doesnt_complete_before_remaining_cost.
  apply: cus_forall_par => cR cL Hc. apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_imp; first exact (UniprocessorSchedule_completed_jobs_dont_execute_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (CB Job sR sL Hs cR cL Hc j tR tL Ht))).
  have Hr := UniprocessorSchedule_remaining_cost_correspondence Job sR sL Hs cR cL Hc j tR tL Ht.
  exact (ct_bool_truth _ _ (ct_bool_not _ _ (CB Job sR sL Hs cR cL Hc j _ _
           (ct_sub_rel _ _ _ _ (sub_add_correspondence _ _ _ _ Ht Hr) (sub_nat_rel_canonical 1))))).
Qed.

Definition src_completed_implies_scheduled_before (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.completed_implies_scheduled_before Job)).
Definition tgt_completed_implies_scheduled_before (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_implies_scheduled_before Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_completed_implies_scheduled_before_correspondence (Job : eqType) :
  PropSPropRel (src_completed_implies_scheduled_before Job) (tgt_completed_implies_scheduled_before Job).
Proof.
  unfold src_completed_implies_scheduled_before, tgt_completed_implies_scheduled_before.
  apply: cus_forall_par => aR aL Ha. apply: cus_forall_par => cR cL Hc. apply: cus_forall_sched => sR sL Hs.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ c0 (Hc j)).
  apply: ct_imp; first exact (UniprocessorSchedule_jobs_must_arrive_to_execute_correspondence Job sR sL Hs aR aL Ha).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (CB Job sR sL Hs cR cL Hc j tR tL Ht)).
  apply: ct_exists_nat => t'R t'L Ht'.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ (Ha j) Ht') (ct_decide_lt _ _ _ _ Ht' Ht))).
  exact (ct_bool_truth _ _ (SA Job sR sL Hs j t'R t'L Ht')).
Qed.

Definition src_service_before_job_arrival_zero (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.service_before_job_arrival_zero Job)).
Definition tgt_service_before_job_arrival_zero (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_before_job_arrival_zero Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_service_before_job_arrival_zero_correspondence (Job : eqType) :
  PropSPropRel (src_service_before_job_arrival_zero Job) (tgt_service_before_job_arrival_zero Job).
Proof.
  unfold src_service_before_job_arrival_zero, tgt_service_before_job_arrival_zero.
  apply: cus_forall_par => aR aL Ha. apply: cus_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (UniprocessorSchedule_jobs_must_arrive_to_execute_correspondence Job sR sL Hs aR aL Ha).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht (Ha j)).
  exact (sub_nat_eq_correspondence _ _ _ _ (UniprocessorSchedule_service_at_correspondence Job sR sL Hs j tR tL Ht) c0).
Qed.

Definition src_cumulative_service_before_job_arrival_zero (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.cumulative_service_before_job_arrival_zero Job)).
Definition tgt_cumulative_service_before_job_arrival_zero (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_cumulative_service_before_job_arrival_zero Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_cumulative_service_before_job_arrival_zero_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_service_before_job_arrival_zero Job) (tgt_cumulative_service_before_job_arrival_zero Job).
Proof.
  unfold src_cumulative_service_before_job_arrival_zero, tgt_cumulative_service_before_job_arrival_zero.
  apply: cus_forall_par => aR aL Ha. apply: cus_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (UniprocessorSchedule_jobs_must_arrive_to_execute_correspondence Job sR sL Hs aR aL Ha).
  apply: ct_forall_identity => j. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H2 (Ha j)).
  exact (sub_nat_eq_correspondence _ _ _ _ (cus_ico _ _ _ _ _ _ H1 H2 (cus_service_at_fun Job sR sL Hs j)) c0).
Qed.

Definition src_ignore_service_before_arrival (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.ignore_service_before_arrival Job)).
Definition tgt_ignore_service_before_arrival (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_ignore_service_before_arrival Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_ignore_service_before_arrival_correspondence (Job : eqType) :
  PropSPropRel (src_ignore_service_before_arrival Job) (tgt_ignore_service_before_arrival Job).
Proof.
  unfold src_ignore_service_before_arrival, tgt_ignore_service_before_arrival.
  apply: cus_forall_par => aR aL Ha. apply: cus_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (UniprocessorSchedule_jobs_must_arrive_to_execute_correspondence Job sR sL Hs aR aL Ha).
  apply: ct_forall_identity => j. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H1 (Ha j)).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Ha j) H2).
  exact (sub_nat_eq_correspondence _ _ _ _ (cus_ico _ _ _ _ _ _ H1 H2 (cus_service_at_fun Job sR sL Hs j))
           (cus_ico _ _ _ _ _ _ (Ha j) H2 (cus_service_at_fun Job sR sL Hs j))).
Qed.

Definition src_scheduled_implies_pending (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.scheduled_implies_pending Job)).
Definition tgt_scheduled_implies_pending (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_implies_pending Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_scheduled_implies_pending_correspondence (Job : eqType) :
  PropSPropRel (src_scheduled_implies_pending Job) (tgt_scheduled_implies_pending Job).
Proof.
  unfold src_scheduled_implies_pending, tgt_scheduled_implies_pending.
  apply: cus_forall_par => aR aL Ha. apply: cus_forall_par => cR cL Hc. apply: cus_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (UniprocessorSchedule_jobs_must_arrive_to_execute_correspondence Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (UniprocessorSchedule_completed_jobs_dont_execute_correspondence Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA Job sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (UniprocessorSchedule_pending_correspondence Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
Qed.

Definition src_job_pending_at_arrival (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.job_pending_at_arrival Job)).
Definition tgt_job_pending_at_arrival (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_job_pending_at_arrival Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_job_pending_at_arrival_correspondence (Job : eqType) :
  PropSPropRel (src_job_pending_at_arrival Job) (tgt_job_pending_at_arrival Job).
Proof.
  unfold src_job_pending_at_arrival, tgt_job_pending_at_arrival.
  apply: cus_forall_par => aR aL Ha. apply: cus_forall_par => cR cL Hc. apply: cus_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (UniprocessorSchedule_jobs_must_arrive_to_execute_correspondence Job sR sL Hs aR aL Ha).
  apply: ct_forall_identity => j. apply: cus_forall_arr => arrR arrL Harr.
  apply: ct_imp; first exact (cus_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ c0 (Hc j)).
  exact (ct_bool_truth _ _ (UniprocessorSchedule_pending_correspondence Job sR sL Hs aR aL Ha cR cL Hc j _ _ (Ha j))).
Qed.

Definition src_only_one_job_scheduled (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.only_one_job_scheduled Job)).
Definition tgt_only_one_job_scheduled (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_only_one_job_scheduled Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_only_one_job_scheduled_correspondence (Job : eqType) :
  PropSPropRel (src_only_one_job_scheduled Job) (tgt_only_one_job_scheduled Job).
Proof.
  unfold src_only_one_job_scheduled, tgt_only_one_job_scheduled.
  apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j1. apply: ct_forall_identity => j2.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA Job sR sL Hs j1 tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA Job sR sL Hs j2 tR tL Ht)).
  exact (ct_eq_rel Job j1 j2).
Qed.

Definition src_service_is_a_step_function (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.service_is_a_step_function Job)).
Definition tgt_service_is_a_step_function (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_is_a_step_function Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_service_is_a_step_function_correspondence (Job : eqType) :
  PropSPropRel (src_service_is_a_step_function Job) (tgt_service_is_a_step_function Job).
Proof.
  unfold src_service_is_a_step_function, tgt_service_is_a_step_function.
  apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_forall_nat => tR tL Ht.
  have Ht1 := sub_add_correspondence _ _ _ _ Ht (sub_nat_rel_canonical 1).
  exact (sub_nat_le_correspondence _ _ _ _ (SV Job sR sL Hs j _ _ Ht1)
           (sub_add_correspondence _ _ _ _ (SV Job sR sL Hs j tR tL Ht) (sub_nat_rel_canonical 1))).
Qed.

Definition src_exists_intermediate_service (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.exists_intermediate_service Job)).
Definition tgt_exists_intermediate_service (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_exists_intermediate_service Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_exists_intermediate_service_correspondence (Job : eqType) :
  PropSPropRel (src_exists_intermediate_service Job) (tgt_exists_intermediate_service Job).
Proof.
  unfold src_exists_intermediate_service, tgt_exists_intermediate_service.
  apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => s0R s0L Hs0.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hs0 (SV Job sR sL Hs j tR tL Ht)).
  apply: ct_exists_nat => t0R t0L Ht0.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Ht0 Ht).
  exact (sub_nat_eq_correspondence _ _ _ _ (SV Job sR sL Hs j t0R t0L Ht0) Hs0).
Qed.

Definition src_scheduled_at_earlier_time (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.scheduled_at_earlier_time Job)).
Definition tgt_scheduled_at_earlier_time (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at_earlier_time Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_scheduled_at_earlier_time_correspondence (Job : eqType) :
  PropSPropRel (src_scheduled_at_earlier_time Job) (tgt_scheduled_at_earlier_time Job).
Proof.
  unfold src_scheduled_at_earlier_time, tgt_scheduled_at_earlier_time.
  apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ c0 (SV Job sR sL Hs j tR tL Ht)).
  apply: ct_exists_nat => t0R t0L Ht0.
  apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ Ht0 Ht).
  exact (ct_bool_truth _ _ (SA Job sR sL Hs j t0R t0L Ht0)).
Qed.

Definition src_cumulative_service_implies_scheduled (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.cumulative_service_implies_scheduled Job)).
Definition tgt_cumulative_service_implies_scheduled (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_cumulative_service_implies_scheduled Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_cumulative_service_implies_scheduled_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_service_implies_scheduled Job) (tgt_cumulative_service_implies_scheduled Job).
Proof.
  unfold src_cumulative_service_implies_scheduled, tgt_cumulative_service_implies_scheduled.
  apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ c0 (SD Job sR sL Hs j t1R t1L H1 t2R t2L H2)).
  apply: ct_exists_nat => tR tL Ht.
  apply: ct_and; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Ht) (ct_decide_lt _ _ _ _ Ht H2))).
  exact (ct_bool_truth _ _ (SA Job sR sL Hs j tR tL Ht)).
Qed.

Definition src_same_service_implies_scheduled_at_earlier_times (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorSchedule.same_service_implies_scheduled_at_earlier_times Job)).
Definition tgt_same_service_implies_scheduled_at_earlier_times (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_same_service_implies_scheduled_at_earlier_times Job (ct_decidable_eq Job))).

Theorem UniprocessorSchedule_same_service_implies_scheduled_at_earlier_times_correspondence (Job : eqType) :
  PropSPropRel (src_same_service_implies_scheduled_at_earlier_times Job)
    (tgt_same_service_implies_scheduled_at_earlier_times Job).
Proof.
  unfold src_same_service_implies_scheduled_at_earlier_times, tgt_same_service_implies_scheduled_at_earlier_times.
  apply: cus_forall_sched => sR sL Hs. apply: ct_forall_identity => j.
  apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (SV Job sR sL Hs j t1R t1L H1) (SV Job sR sL Hs j t2R t2L H2)).
  apply: ct_bool_eq.
  - apply: (co_exists_rel t1R t1L H1). intros oR oL Ho. exact (SA Job sR sL Hs j _ _ Ho).
  - apply: (co_exists_rel t2R t2L H2). intros oR oL Ho. exact (SA Job sR sL Hs j _ _ Ho).
Qed.
