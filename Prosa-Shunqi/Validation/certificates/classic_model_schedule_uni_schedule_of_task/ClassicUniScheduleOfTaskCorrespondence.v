From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.schedule.uni.schedule classic.model.schedule.uni.schedule_of_task.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniScheduleOfTask.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniScheduleOfTaskBase ClassicUniScheduleOfTaskList.

Module I := ImportedClassicUniScheduleOfTask.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/schedule_of_task.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; uniprocessor
    schedules pointwise through the option map (two-way totals).

    Computation: [if sched t is Some j then job_task j == tsk else false] against the Lean [match] through the
    option map; [nat_of_bool] against [Bool.toNat]; the half-open sum of [task_service_during] against its
    kernel-guarded body projection [ClassicUniScheduleOfTaskInterface.task_service_during_proj] (as for the accepted
    classic schedule certificates), related by [cst_ico]. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cst_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cst_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cst_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cst_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cst_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Definition CstParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cst_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CstParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cst_forall_cover _ _ (CstParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cst_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cst_snatl s') end.

Lemma cst_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cst_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cst_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cst_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cst_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cst_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cst_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CstFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cst_fun_canonical FR FL (HF : CstFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cst_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cst_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CstFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cst_nat_sub_canonical nR mR.
  rewrite cst_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cst_foldr_add FL FR (cst_fun_canonical FR FL HF)).
  by rewrite cst_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cst_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cst_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cst_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cst_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cst_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CstSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cst_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cst_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cst_sched_canonical sR : CstSchedRel sR (cst_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cst_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cst_sched_surjective sL : CstSchedRel (cst_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cst_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cst_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CstSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cst_forall_cover _ _ CstSchedRel cst_sched_to_target cst_sched_to_source cst_sched_canonical cst_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cst_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CstSchedRel Job sR (cst_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CstSchedRel Job (cst_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cst_sched_canonical Job) (cst_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CstSchedRel Job sR sL.

End USchedDefs.


(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CstSchedRel Job sR sL.
Variable job_task : Job -> Task.

Theorem ScheduleOfTask_task_scheduled_at_correspondence tsk tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleOfTask.task_scheduled_at job_task sR tsk tR) (I.Prosa_Classic_Model_Schedule_Uni_ScheduleOfTask_ScheduleOfTask_task_scheduled_at Task dT Job dJ job_task sL tsk tL).
Proof.
  refine (cst_trs (Hs tR tL Ht)
            (fun z => CtBoolRel (ScheduleOfTask.task_scheduled_at job_task sR tsk tR)
                        (match z with
                         | I.Option_some j => I.Decidable_decide (Lean.eq (job_task j) tsk) (dT (job_task j) tsk)
                         | I.Option_none => I.Bool_false end)) _).
  rewrite /ScheduleOfTask.task_scheduled_at. destruct (sR tR) as [x|].
  - exact (ct_decide_eq Task (job_task x) tsk).
  - exact (ct_bool_canonical false).
Qed.

Theorem ScheduleOfTask_task_service_at_correspondence tsk tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (ScheduleOfTask.task_service_at job_task sR tsk tR) (I.Prosa_Classic_Model_Schedule_Uni_ScheduleOfTask_ScheduleOfTask_task_service_at Task dT Job dJ job_task sL tsk tL).
Proof. exact (ct_bool_to_nat _ _ (ScheduleOfTask_task_scheduled_at_correspondence tsk tR tL Ht)). Qed.

Theorem ScheduleOfTask_task_service_during_correspondence tsk t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (ScheduleOfTask.task_service_during job_task sR tsk t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_ScheduleOfTask_ScheduleOfTask_task_service_during Task dT Job dJ job_task sL tsk t1L t2L).
Proof.
  exact (cst_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ScheduleOfTask_task_service_at_correspondence tsk kR kL Hk)).
Qed.

Theorem ScheduleOfTask_task_service_correspondence tsk tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (ScheduleOfTask.task_service job_task sR tsk tR) (I.Prosa_Classic_Model_Schedule_Uni_ScheduleOfTask_ScheduleOfTask_task_service Task dT Job dJ job_task sL tsk tL).
Proof. exact (ScheduleOfTask_task_service_during_correspondence tsk 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.
End Defs.
