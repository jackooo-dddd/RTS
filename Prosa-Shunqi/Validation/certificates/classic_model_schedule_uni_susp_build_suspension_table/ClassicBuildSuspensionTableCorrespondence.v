From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.suspension classic.model.arrival.basic.arrival_sequence classic.model.schedule.uni.schedule classic.model.schedule.uni.susp.last_execution classic.model.schedule.uni.susp.suspension_intervals classic.model.schedule.uni.susp.build_suspension_table.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicBuildSuspensionTable.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicBuildSuspensionTableBase ClassicBuildSuspensionTableList ClassicBuildSuspensionTableOrd.

Module I := ImportedClassicBuildSuspensionTable.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/susp/build_suspension_table.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by its decision procedure
    ([ct_decidable_eq]); times by [SubNatRel]; job parameters pointwise through [SubNatRel]; uniprocessor schedules
    pointwise through the option map; suspension predicates [Job -> time -> bool] pointwise on related times (two-way
    totals).  The filtered half-open sums [\sum_(m <= t < n | P t) F t] against list folds over the filtered
    [List.range'] ([cbt_icof]), the Lean side through a kernel-guarded [rfl] body projection of
    [build_suspension_duration] and kernel-guarded type normalization of the statement with such a sum;
    [time_after_last_execution], [service], [completed_by] and [suspended_at] as in the accepted classic uniprocessor
    schedule and suspension certificates (re-bound below).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof is not
    used); local [let]s are zeta-reduced on both sides. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cbt_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cbt_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cbt_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cbt_false_rel). Qed.

Lemma cbt_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cbt_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cbt_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cbt_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cbt_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cbt_unmap_rel T l) PR PL).
Qed.

Definition CbtParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cbt_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CbtParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cbt_forall_cover _ _ (CbtParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cbt_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cbt_natl s') end.

Definition cbt_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cbt_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cbt_one) (cbt_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cbt_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cbt_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cbt_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cbt_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cbt_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cbt_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cbt_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cbt_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cbt_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cbt_cl_append. reflexivity.
Qed.

Lemma cbt_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CbtFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cbt_has_arrived pR pL (Hp : CbtParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cbt_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cbt_snatl s') end.

Lemma cbt_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cbt_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cbt_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cbt_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cbt_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cbt_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cbt_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CbtFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cbt_fun_canonical FR FL (HF : CbtFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cbt_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cbt_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CbtFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cbt_nat_sub_canonical nR mR.
  rewrite cbt_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cbt_foldr_add FL FR (cbt_fun_canonical FR FL HF)).
  by rewrite cbt_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Filtered half-open sums [\sum_(m <= i < n | P i) F i] against [foldr] over a filtered [List.range'] *)

Lemma cbt_snatl_filter (PR : nat -> bool) (PL : Lean.Nat -> I.Bool) (HP : forall k, CtBoolRel (PR k) (PL (sub_nat_to_imported k))) :
  forall s, Logic.eq (I.List_filter_inst1 Lean.Nat PL (cbt_snatl s)) (cbt_snatl (filter PR s)).
Proof.
  elim => [|x s IH] //=.
  have -> : Logic.eq (I.List_filter_inst1 Lean.Nat PL (I.List_cons_inst1 _ (sub_nat_to_imported x) (cbt_snatl s)))
      (match PL (sub_nat_to_imported x) with
       | I.Bool_true => I.List_cons_inst1 _ (sub_nat_to_imported x) (I.List_filter_inst1 Lean.Nat PL (cbt_snatl s))
       | I.Bool_false => I.List_filter_inst1 Lean.Nat PL (cbt_snatl s) end).
  { cbn. destruct (PL (sub_nat_to_imported x)); reflexivity. }
  rewrite (ct_bool_rel_logic _ _ (HP x)) IH. by case: (PR x).
Qed.

Lemma cbt_icof mR mL nR nL PR PL (HP : forall k, CtBoolRel (PR k) (PL (sub_nat_to_imported k))) FR FL
    (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CbtFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR | PR i) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL
          (I.List_filter_inst1 Lean.Nat PL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero))))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cbt_nat_sub_canonical nR mR.
  rewrite cbt_siota_range (cbt_snatl_filter PR PL HP).
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cbt_foldr_add FL FR (cbt_fun_canonical FR FL HF)).
  rewrite -cbt_big_fold big_filter /index_iota. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cbt_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cbt_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cbt_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cbt_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cbt_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CbtSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cbt_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cbt_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cbt_sched_canonical sR : CbtSchedRel sR (cbt_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cbt_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cbt_sched_surjective sL : CbtSchedRel (cbt_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cbt_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cbt_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CbtSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cbt_forall_cover _ _ CbtSchedRel cbt_sched_to_target cbt_sched_to_source cbt_sched_canonical cbt_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cbt_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CbtSchedRel Job sR (cbt_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CbtSchedRel Job (cbt_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cbt_sched_canonical Job) (cbt_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CbtSchedRel Job sR sL.

Lemma cbt_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cbt_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cbt_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cbt_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cbt_US_scheduled_at j tR tL Ht)). Qed.

Lemma cbt_service_at_fun j : CbtFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cbt_US_service_at j kR kL Hk). Qed.

Lemma cbt_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cbt_ico _ _ _ _ _ _ H1 H2 (cbt_service_at_fun j)). Qed.

Lemma cbt_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cbt_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cbt_US_completed_by cR cL (Hc : CbtParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cbt_US_service j tR tL Ht)). Qed.

Lemma cbt_US_jobs_must_arrive_to_execute aR aL (Ha : CbtParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cbt_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cbt_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

End USchedDefs.

(** * [\max] over ordinals against [maxFiltered] over [List.finRange] *)

Lemma cbt_foldr_max (f : Lean.Nat -> Lean.Nat) (g : nat -> nat)
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

Lemma cbt_max_rel nR nL (Hn : SubNatRel nR nL) (QR : 'I_nR -> bool) (QL : Fin nL -> I.Bool) (HQ : CoOrdPredRel nR nL QR QL) :
  SubNatRel (\max_(i < nR | QR i) nat_of_ord i)
    (I.Prosa_Util_Sum_maxFiltered_inst1 (Fin nL) (I.List_finRange nL) QL (fun o => I.Fin_val nL o)).
Proof.
  have E := co_nat_logic _ _ Hn. subst nL. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicBuildSuspensionTableInterface_maxFiltered_finRange
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
  exact (cbt_foldr_max _ _ (co_fam_related nR sub_nat_to_imported (fun i => if QR i then nat_of_ord i else 0)
           (fun oL => I.cond Lean.Nat (QL oL) (I.Fin_val _ oL) (sub_nat_to_imported 0)) 0 HF) (iota 0 nR)).
Qed.

Lemma cbt_ite_rel bR bL (Hb : CtBoolRel bR bL) xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) :
  SubNatRel (if bR then xR else yR)
    (I.ite Lean.Nat (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) xL yL).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). destruct bR; [exact Hx | exact Hy]. Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cbt_LE_time_after_last_execution (Job : eqType) aR aL (Ha : CbtParRel Job aR aL)
    sR sL (Hs : CbtSchedRel Job sR sL) j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (LastExecution.time_after_last_execution aR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Susp_LastExecution_LastExecution_time_after_last_execution Job (ct_decidable_eq Job) aL sL j tL).
Proof.
  assert (HQ : CoOrdPredRel tR tL (fun o => UniprocessorSchedule.scheduled_at sR j o)
      (fun oL => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job (ct_decidable_eq Job) sL j (I.Fin_val tL oL))).
  { intros o oL Ho. exact (cbt_US_scheduled_at Job sR sL Hs j _ _ Ho). }
  exact (cbt_ite_rel _ _ (co_exists_rel tR tL Ht _ _ HQ) _ _
           (sub_add_correspondence _ _ _ _ (cbt_max_rel tR tL Ht _ _ HQ) (sub_nat_rel_canonical 1)) _ _ (Ha j)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Section SuspSusp.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSusp := (I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).

Definition CbtSuspRel (sR : Suspension.job_suspension Job) (sL : LSusp) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (sR j tR) (sL j tL).

Definition cbt_susp_to_target (sR : Suspension.job_suspension Job) : LSusp :=
  fun j tL => sub_nat_to_imported (sR j (sub_nat_to_rocq tL)).

Definition cbt_susp_to_source (sL : LSusp) : Suspension.job_suspension Job :=
  fun j tR => sub_nat_to_rocq (sL j (sub_nat_to_imported tR)).

Lemma cbt_susp_canonical sR : CbtSuspRel sR (cbt_susp_to_target sR).
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  unfold cbt_susp_to_target. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma cbt_susp_surjective sL : CbtSuspRel (cbt_susp_to_source sL) sL.
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma cbt_forall_susp (PR : Suspension.job_suspension Job -> Prop) (PL : LSusp -> SProp) :
  (forall sR sL, CbtSuspRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cbt_forall_cover _ _ CbtSuspRel cbt_susp_to_target cbt_susp_to_source cbt_susp_canonical cbt_susp_surjective PR PL). Qed.

End SuspSusp.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cbt_SU_job_suspension (Job : eqType) :
  And (forall sR : Suspension.job_suspension Job, CbtSuspRel Job sR (cbt_susp_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job (ct_decidable_eq Job), CbtSuspRel Job (cbt_susp_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cbt_susp_canonical Job) (cbt_susp_surjective Job)). Qed.

Section SuspintDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CbtSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CbtParRel Job aR aL) (Hc : CbtParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CbtSuspRel Job nR nL.

Notation TALE := (cbt_LE_time_after_last_execution Job aR aL Ha sR sL Hs).

Lemma cbt_SI_suspension_duration j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (SuspensionIntervals.suspension_duration aR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspension_duration Job dJ aL nL sL j tL).
Proof. exact (Hn j _ _ (cbt_US_service Job sR sL Hs j _ _ (TALE j tR tL Ht))). Qed.

Lemma cbt_SI_suspended_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (SuspensionIntervals.suspended_at aR cR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspended_at Job dJ aL cL nL sL j tL).
Proof.
  have HT := TALE j tR tL Ht.
  exact (ct_bool_and _ _ _ _ (ct_bool_not _ _ (cbt_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht))
           (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ HT Ht)
              (ct_decide_lt _ _ _ _ Ht (sub_add_correspondence _ _ _ _ HT (cbt_SI_suspension_duration j tR tL Ht))))).
Qed.

End SuspintDefs.



(* ------------------------------------------------------------------ *)
(** * Suspension predicates [Job -> time -> bool] (pointwise on related times, two-way totals) *)

Section SPred.
Variable Job : eqType.
Definition CbtSPredRel (pR : Job -> nat -> bool) (pL : Job -> Lean.Nat -> I.Bool) : SProp :=
  forall j tR tL, SubNatRel tR tL -> CtBoolRel (pR j tR) (pL j tL).
Lemma cbt_spred_canonical pR : CbtSPredRel pR (fun j tL => ct_b2l (pR j (sub_nat_to_rocq tL))).
Proof. intros j tR tL Ht. rewrite (cl_nat_input _ _ Ht). exact (ct_bool_canonical _). Qed.
Lemma cbt_spred_surjective pL : CbtSPredRel (fun j tR => ct_l2b (pL j (sub_nat_to_imported tR))) pL.
Proof.
  intros j tR tL Ht. rewrite -(cl_nat_logic _ _ Ht). exact (ct_bool_surjective _).
Qed.
Lemma cbt_forall_spred (PR : (Job -> nat -> bool) -> Prop) (PL : (Job -> Lean.Nat -> I.Bool) -> SProp) :
  (forall pR pL, CbtSPredRel pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof. exact (cbt_forall_cover _ _ CbtSPredRel _ _ cbt_spred_canonical cbt_spred_surjective PR PL). Qed.
End SPred.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem SuspensionTableConstruction_build_suspension_duration_correspondence (Job : eqType) sR sL (Hs : CbtSchedRel Job sR sL)
    tmR tmL (Htm : SubNatRel tmR tmL) pR pL (Hp : CbtSPredRel Job pR pL) :
  CbtSuspRel Job (@SuspensionTableConstruction.build_suspension_duration Job sR tmR pR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_BuildSuspensionTable_SuspensionTableConstruction_build_suspension_duration Job (ct_decidable_eq Job) sL tmL pL).
Proof.
  intros j xR xL Hx.
  exact (cbt_icof 0 _ tmR tmL _ _ (fun k => ct_decide_eq_nat _ _ _ _ (cbt_US_service Job sR sL Hs j k _ (sub_nat_rel_canonical k)) Hx)
           _ _ (sub_nat_rel_canonical 0) Htm (fun kR kL Hk => ct_bool_to_nat _ _ (Hp j kR kL Hk))).
Qed.

Notation BSD := SuspensionTableConstruction_build_suspension_duration_correspondence.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_not_suspended_before_suspension_start (Job : eqType) : Prop :=
  ltac:(type_of_term (@SuspensionTableConstruction.not_suspended_before_suspension_start Job)).
Definition tgt_not_suspended_before_suspension_start (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Susp_BuildSuspensionTable_SuspensionTableConstruction_not_suspended_before_suspension_start Job (ct_decidable_eq Job))).
Theorem SuspensionTableConstruction_not_suspended_before_suspension_start_correspondence (Job : eqType) :
  PropSPropRel (src_not_suspended_before_suspension_start Job) (tgt_not_suspended_before_suspension_start Job).
Proof.
  unfold src_not_suspended_before_suspension_start, tgt_not_suspended_before_suspension_start. cbv zeta.
  apply: cbt_forall_par => jaR jaL Hja.
  apply: (cbt_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cbt_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_forall_nat => tmR tmL Htm.
  apply: (cbt_forall_spred Job) => pR pL Hp.
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht Htm).
    apply: ct_imp; first exact (ct_bool_truth _ _ (Hp j tR tL Ht)).
    exact (ct_bool_truth _ _ (cbt_has_arrived Job jaR jaL Hja j tR tL Ht)). }
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht Htm).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hp j tR tL Ht)).
  have Hss := cbt_LE_time_after_last_execution Job jaR jaL Hja sR sL Hs j tR tL Ht.
  apply: sub_nat_eq_correspondence; last exact (sub_nat_rel_canonical 0).
  exact (cbt_icof 0 _ _ _ _ _ (fun k => ct_decide_eq_nat _ _ _ _ (cbt_US_service Job sR sL Hs j k _ (sub_nat_rel_canonical k))
                                           (cbt_US_service Job sR sL Hs j _ _ Hss))
           _ _ (sub_nat_rel_canonical 0) Hss (fun kR kL Hk => ct_bool_to_nat _ _ (Hp j kR kL Hk))).
Qed.

Definition src_suspension_duration_no_suspension_after_t_max (Job : eqType) : Prop :=
  ltac:(type_of_term (@SuspensionTableConstruction.suspension_duration_no_suspension_after_t_max Job)).
Definition tgt_suspension_duration_no_suspension_after_t_max (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Susp_BuildSuspensionTable_SuspensionTableConstruction_suspension_duration_no_suspension_after_t_max Job (ct_decidable_eq Job))).
Theorem SuspensionTableConstruction_suspension_duration_no_suspension_after_t_max_correspondence (Job : eqType) :
  PropSPropRel (src_suspension_duration_no_suspension_after_t_max Job) (tgt_suspension_duration_no_suspension_after_t_max Job).
Proof.
  unfold src_suspension_duration_no_suspension_after_t_max, tgt_suspension_duration_no_suspension_after_t_max.
  apply: cbt_forall_par => jaR jaL Hja. apply: cbt_forall_par => cR cL Hc.
  apply: (cbt_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cbt_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_forall_nat => tmR tmL Htm.
  apply: (cbt_forall_spred Job) => pR pL Hp.
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht Htm).
    apply: ct_imp; first exact (ct_bool_truth _ _ (Hp j tR tL Ht)).
    exact (ct_bool_truth _ _ (cbt_has_arrived Job jaR jaL Hja j tR tL Ht)). }
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cbt_has_arrived Job jaR jaL Hja j tR tL Ht)).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Htm Ht).
  exact (ct_bool_truth _ _ (ct_bool_not _ _ (cbt_SI_suspended_at Job sR sL Hs jaR jaL cR cL Hja Hc _ _ (BSD Job sR sL Hs tmR tmL Htm pR pL Hp) j tR tL Ht))).
Qed.

Definition src_suspension_duration_matches_predicate_up_to_t_max (Job : eqType) : Prop :=
  ltac:(type_of_term (@SuspensionTableConstruction.suspension_duration_matches_predicate_up_to_t_max Job)).
Definition tgt_suspension_duration_matches_predicate_up_to_t_max (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Susp_BuildSuspensionTable_SuspensionTableConstruction_suspension_duration_matches_predicate_up_to_t_max Job (ct_decidable_eq Job))).
Theorem SuspensionTableConstruction_suspension_duration_matches_predicate_up_to_t_max_correspondence (Job : eqType) :
  PropSPropRel (src_suspension_duration_matches_predicate_up_to_t_max Job) (tgt_suspension_duration_matches_predicate_up_to_t_max Job).
Proof.
  unfold src_suspension_duration_matches_predicate_up_to_t_max, tgt_suspension_duration_matches_predicate_up_to_t_max.
  apply: cbt_forall_par => jaR jaL Hja. apply: cbt_forall_par => cR cL Hc.
  apply: (cbt_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cbt_US_jobs_must_arrive_to_execute Job sR sL Hs jaR jaL Hja).
  apply: ct_forall_nat => tmR tmL Htm.
  apply: (cbt_forall_spred Job) => pR pL Hp.
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht Htm).
    apply: ct_imp; first exact (ct_bool_truth _ _ (Hp j tR tL Ht)).
    exact (ct_bool_truth _ _ (cbt_has_arrived Job jaR jaL Hja j tR tL Ht)). }
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
    apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht Htm).
    apply: ct_imp; first exact (ct_bool_truth _ _ (Hp j tR tL Ht)).
    exact (ct_bool_truth _ _ (ct_bool_not _ _ (cbt_US_completed_by Job sR sL Hs cR cL Hc j tR tL Ht))). }
  apply: ct_imp.
  { apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => uR uL Hu.
    apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht Htm).
    apply: ct_imp; first exact (ct_bool_truth _ _ (Hp j tR tL Ht)).
    apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _
       (ct_decide_le _ _ _ _ (cbt_LE_time_after_last_execution Job jaR jaL Hja sR sL Hs j tR tL Ht) Hu) (ct_decide_lt _ _ _ _ Hu Ht))).
    exact (ct_bool_truth _ _ (Hp j uR uL Hu)). }
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht Htm).
  exact (ct_bool_eq _ _ _ _ (Hp j tR tL Ht)
           (cbt_SI_suspended_at Job sR sL Hs jaR jaL cR cL Hja Hc _ _ (BSD Job sR sL Hs tmR tmL Htm pR pL Hp) j tR tL Ht)).
Qed.
