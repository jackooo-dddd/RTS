From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import analysis.definitions.service InterferenceSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedInterference ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedInterference.
Module S := InterferenceSemanticSource.InterferenceSemanticSource.

(** Definition certificates for [analysis/definitions/interference.v]: for
    related inputs (processor state with the two-sided [SvcProcessorStateRel],
    schedule, arrival sequence, FP and JLFP policies pointwise on Booleans,
    [job_task] by [Lean.eq], [job_cost] by [SubNatRel], jobs and instants) the
    fifteen source definitions and the compiled Lean definitions are related.
    Composed from the accepted ArrivalSequence / Arrivals / Service proofs
    re-instantiated at this artifact; replayed here: the [has]/[List.any]
    bridge (accepted ReadinessInterference certificate), the [!=] observation
    (accepted PriorityDerived), the filtered sum (accepted [ari_sum_related])
    and the Boolean-to-Nat interval sum (accepted Supply proof). *)

(** ** Generic operations *)

Lemma if_bool_or_related (aR bR : bool) (aL bL : I.Bool) :
  ArBoolRel aR aL -> ArBoolRel bR bL -> ArBoolRel (aR || bR) (I.Bool_or aL bL).
Proof.
  unfold ArBoolRel. intros Ha Hb. destruct Ha. destruct Hb.
  destruct aR, bR; exact (@Lean.eq_refl _ _).
Qed.

Lemma if_has_canonical (T : Type) (PR : T -> bool) (PL : T -> I.Bool) :
  ArPredRel PR PL ->
  forall xs : seq T, ArBoolRel (has PR xs) (I.List_any T (ar_list_to_imported xs) PL).
Proof.
  intros HP xs. induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - exact (if_bool_or_related _ _ _ _ (HP x) IH).
Qed.

Lemma if_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma if_has_related (T : Type) (PR : T -> bool) (PL : T -> I.Bool)
    (xsR : seq T) (xsL : I.List T) :
  ArPredRel PR PL -> ArListRel xsR xsL -> ArBoolRel (has PR xsR) (I.List_any T xsL PL).
Proof.
  intros HP Hxs.
  exact (if_lean_transport (fun l => ArBoolRel (has PR xsR) (I.List_any T l PL))
    _ _ Hxs (if_has_canonical T PR PL HP xsR)).
Qed.

Lemma if_ne_observation (T : eqType) (x y : T) :
  ArBoolRel (x != y)
    (I.Decidable_decide (I.Ne T x y) (I.instDecidableNot (Lean.eq x y) (ar_decidable_eq T x y))).
Proof.
  unfold ar_decidable_eq, ArBoolRel.
  destruct (@eqP T x y); cbn; exact (@Lean.eq_refl _ _).
Qed.

Definition if_target_decide_ne (T : eqType) (x y : T) : I.Bool :=
  I.Decidable_decide (I.Ne T x y) (I.instDecidableNot (Lean.eq x y) (ar_decidable_eq T x y)).

Lemma if_ne_transport (T : eqType) (xR yR xL yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL -> ArBoolRel (xR != yR) (if_target_decide_ne T xL yL).
Proof.
  intros Hx Hy. unfold ArBoolRel.
  exact (sub_imported_eq_trans _ _ _ (if_ne_observation T xR yR)
    (sub_imported_eq_congr2 (if_target_decide_ne T) _ _ _ _ Hx Hy)).
Qed.

Definition if_target_decide_eq (T : eqType) (x y : T) : I.Bool :=
  I.Decidable_decide (Lean.eq x y) (ar_decidable_eq T x y).

Lemma if_eq_transport (T : eqType) (xR yR xL yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL -> ArBoolRel (xR == yR) (if_target_decide_eq T xL yL).
Proof.
  intros Hx Hy. unfold ArBoolRel.
  exact (sub_imported_eq_trans _ _ _ (ari_decide_eq_related T xR yR)
    (sub_imported_eq_congr2 (if_target_decide_eq T) _ _ _ _ Hx Hy)).
Qed.

Lemma if_bool_to_nat_related (bR : bool) (bL : I.Bool) :
  ArBoolRel bR bL -> SubNatRel (nat_of_bool bR) (I.Bool_toNat bL).
Proof.
  unfold ArBoolRel. intro Hb. destruct Hb. destruct bR.
  - exact (sub_nat_rel_canonical 1).
  - exact (sub_nat_rel_canonical O).
Qed.

Lemma if_sum_filter_related (T : Type) (PR : T -> bool) (PL : T -> I.Bool)
    (FR : T -> nat) (FL : T -> Lean.Nat) xsR xsL :
  ArPredRel PR PL -> (forall x, SubNatRel (FR x) (FL x)) -> ArListRel xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (ari_list_sum T FL (ar_target_filter PL xsL)).
Proof.
  intros HP HF Hxs. rewrite -big_filter.
  exact (ari_sum_related T FR FL _ _ HF (ar_filter_related T PR PL xsR xsL HP Hxs)).
Qed.

(** ** Definitions *)

Section Interference.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jcR : prosa.behavior.job.JobCost Job.
  Variable jcL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hjc : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job jcR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ jcL j).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable fpR : prosa.model.priority.definitions.FP_policy Task.
  Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hfp : forall x y : Task,
    ArBoolRel (@prosa.model.priority.definitions.hep_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL x y).
  Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hp : forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).


  Lemma if_hp_task_canonical (x y : Task) :
    ArBoolRel (@prosa.model.priority.definitions.hp_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_hp_task Task dT fpL x y).
  Proof.
    unfold prosa.model.priority.definitions.hp_task.
    cbn [I.Prosa_Model_Priority_Definitions_hp_task].
    exact (ar_bool_and_related _ _ _ _ (Hfp x y) (svc_bool_not_related _ _ (Hfp y x))).
  Qed.

  Lemma if_ep_task_canonical (x y : Task) :
    ArBoolRel (@prosa.model.priority.definitions.ep_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_ep_task Task dT fpL x y).
  Proof.
    unfold prosa.model.priority.definitions.ep_task.
    cbn [I.Prosa_Model_Priority_Definitions_ep_task].
    exact (ar_bool_and_related _ _ _ _ (Hfp x y) (Hfp y x)).
  Qed.

  Lemma if_hp_task_jobs (j1 j2 : Job) :
    ArBoolRel (@prosa.model.priority.definitions.hp_task Task fpR
        (@prosa.model.task.concept.job_task Job Task jtR j1)
        (@prosa.model.task.concept.job_task Job Task jtR j2))
      (I.Prosa_Model_Priority_Definitions_hp_task Task dT fpL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j1)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j2)).
  Proof.
    unfold ArBoolRel.
    exact (sub_imported_eq_trans _ _ _ (if_hp_task_canonical _ _)
      (sub_imported_eq_congr2 (I.Prosa_Model_Priority_Definitions_hp_task Task dT fpL)
        _ _ _ _ (Hjt j1) (Hjt j2))).
  Qed.

  Lemma if_ep_task_jobs (j1 j2 : Job) :
    ArBoolRel (@prosa.model.priority.definitions.ep_task Task fpR
        (@prosa.model.task.concept.job_task Job Task jtR j1)
        (@prosa.model.task.concept.job_task Job Task jtR j2))
      (I.Prosa_Model_Priority_Definitions_ep_task Task dT fpL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j1)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j2)).
  Proof.
    unfold ArBoolRel.
    exact (sub_imported_eq_trans _ _ _ (if_ep_task_canonical _ _)
      (sub_imported_eq_congr2 (I.Prosa_Model_Priority_Definitions_ep_task Task dT fpL)
        _ _ _ _ (Hjt j1) (Hjt j2))).
  Qed.

  Lemma if_another_hep_job_related (x y : Job) :
    ArBoolRel (@prosa.model.priority.definitions.another_hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_another_hep_job Job dJ pL x y).
  Proof.
    unfold prosa.model.priority.definitions.another_hep_job,
      I.Prosa_Model_Priority_Definitions_another_hep_job.
    exact (ar_bool_and_related _ _ _ _ (Hp x y) (if_ne_observation Job x y)).
  Qed.

  Lemma if_another_task_hep_job_related (x y : Job) :
    ArBoolRel (@prosa.model.priority.definitions.another_task_hep_job Task Job jtR pR x y)
      (I.Prosa_Model_Priority_Definitions_another_task_hep_job Task dT Job dJ jtL pL x y).
  Proof.
    unfold prosa.model.priority.definitions.another_task_hep_job,
      I.Prosa_Model_Priority_Definitions_another_task_hep_job.
    exact (ar_bool_and_related _ _ _ _ (Hp x y) (if_ne_transport Task _ _ _ _ (Hjt x) (Hjt y))).
  Qed.

  Lemma if_another_hep_job_of_same_task_related (x y : Job) :
    ArBoolRel (@prosa.model.priority.definitions.another_hep_job_of_same_task Task Job jtR pR x y)
      (I.Prosa_Model_Priority_Definitions_another_hep_job_of_same_task Task dT Job dJ jtL pL x y).
  Proof.
    unfold prosa.model.priority.definitions.another_hep_job_of_same_task,
      I.Prosa_Model_Priority_Definitions_another_hep_job_of_same_task.
    exact (ar_bool_and_related _ _ _ _ (if_another_hep_job_related x y)
      (if_eq_transport Task _ _ _ _ (Hjt x) (Hjt y))).
  Qed.

  Lemma if_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [I.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma if_receives_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel (@prosa.behavior.service.receives_service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_receives_service_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.receives_service_at.
    cbn [I.Prosa_Behavior_Service_receives_service_at].
    exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (if_service_at_related j tR tL Ht)).
  Qed.

  Lemma if_served_jobs_at_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArListRel (@prosa.analysis.definitions.service.served_jobs_at Job PStateR arrR schedR tR)
      (I.Prosa_Analysis_Definitions_Service_served_jobs_at Job dJ PStateL arrL schedL tL).
  Proof.
    intro Ht. unfold prosa.analysis.definitions.service.served_jobs_at.
    cbn [I.Prosa_Analysis_Definitions_Service_served_jobs_at].
    apply ar_filter_related.
    - intro j. exact (if_receives_service_at_related j tR tL Ht).
    - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr tR tL Ht).
  Qed.

  (** *** FP definitions *)

  Theorem hp_task_interference_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel
      (@S.hp_task_interference
        Task Job jtR PStateR arrR schedR fpR j tR)
      (I.Prosa_Analysis_Definitions_Interference_hp_task_interference
        Task dT Job dJ jtL PStateL arrL schedL fpL j tL).
  Proof.
    intro Ht.
    unfold S.hp_task_interference.
    cbn [I.Prosa_Analysis_Definitions_Interference_hp_task_interference].
    apply if_has_related.
    - intro jhp. exact (ar_bool_and_related _ _ _ _ (if_hp_task_jobs jhp j)
        (if_receives_service_at_related jhp tR tL Ht)).
    - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr tR tL Ht).
  Qed.

  Theorem ep_task_hep_job_correspondence (j1 j2 : Job) :
    ArBoolRel
      (@S.ep_task_hep_job Task Job jtR fpR pR j1 j2)
      (I.Prosa_Analysis_Definitions_Interference_ep_task_hep_job Task dT Job dJ jtL fpL pL j1 j2).
  Proof.
    unfold S.ep_task_hep_job.
    cbn [I.Prosa_Analysis_Definitions_Interference_ep_task_hep_job].
    exact (ar_bool_and_related _ _ _ _ (Hp j1 j2) (if_ep_task_jobs j1 j2)).
  Qed.

  Theorem other_ep_task_hep_job_correspondence (j1 j2 : Job) :
    ArBoolRel
      (@S.other_ep_task_hep_job Task Job jtR fpR pR j1 j2)
      (I.Prosa_Analysis_Definitions_Interference_other_ep_task_hep_job
        Task dT Job dJ jtL fpL pL j1 j2).
  Proof.
    unfold S.other_ep_task_hep_job.
    cbn [I.Prosa_Analysis_Definitions_Interference_other_ep_task_hep_job].
    exact (ar_bool_and_related _ _ _ _ (ep_task_hep_job_correspondence j1 j2)
      (if_ne_transport Task _ _ _ _ (Hjt j1) (Hjt j2))).
  Qed.

  Theorem hep_job_from_other_ep_task_interference_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel
      (@S.hep_job_from_other_ep_task_interference
        Task Job jtR PStateR arrR schedR fpR pR j tR)
      (I.Prosa_Analysis_Definitions_Interference_hep_job_from_other_ep_task_interference
        Task dT Job dJ jtL PStateL arrL schedL fpL pL j tL).
  Proof.
    intro Ht.
    unfold S.hep_job_from_other_ep_task_interference.
    cbn [I.Prosa_Analysis_Definitions_Interference_hep_job_from_other_ep_task_interference].
    apply if_has_related.
    - intro x. exact (other_ep_task_hep_job_correspondence x j).
    - exact (if_served_jobs_at_related tR tL Ht).
  Qed.

  Theorem hp_task_hep_job_correspondence (j1 j2 : Job) :
    ArBoolRel
      (@S.hp_task_hep_job Task Job jtR fpR pR j1 j2)
      (I.Prosa_Analysis_Definitions_Interference_hp_task_hep_job Task dT Job dJ jtL fpL pL j1 j2).
  Proof.
    unfold S.hp_task_hep_job.
    cbn [I.Prosa_Analysis_Definitions_Interference_hp_task_hep_job].
    exact (ar_bool_and_related _ _ _ _ (Hp j1 j2) (if_hp_task_jobs j1 j2)).
  Qed.

  Theorem hep_job_from_hp_task_interference_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel
      (@S.hep_job_from_hp_task_interference
        Task Job jtR PStateR arrR schedR fpR pR j tR)
      (I.Prosa_Analysis_Definitions_Interference_hep_job_from_hp_task_interference
        Task dT Job dJ jtL PStateL arrL schedL fpL pL j tL).
  Proof.
    intro Ht.
    unfold S.hep_job_from_hp_task_interference.
    cbn [I.Prosa_Analysis_Definitions_Interference_hep_job_from_hp_task_interference].
    apply if_has_related.
    - intro x. exact (hp_task_hep_job_correspondence x j).
    - exact (if_served_jobs_at_related tR tL Ht).
  Qed.

  Theorem cumulative_interference_from_hep_jobs_from_hp_tasks_correspondence (j : Job)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@S.cumulative_interference_from_hep_jobs_from_hp_tasks
        Task Job jtR PStateR arrR schedR fpR pR j t1R t2R)
      (I.Prosa_Analysis_Definitions_Interference_cumulative_interference_from_hep_jobs_from_hp_tasks
        Task dT Job dJ jtL PStateL arrL schedL fpL pL j t1L t2L).
  Proof.
    intros H1 H2.
    unfold S.cumulative_interference_from_hep_jobs_from_hp_tasks.
    cbn [I.Prosa_Analysis_Definitions_Interference_cumulative_interference_from_hep_jobs_from_hp_tasks].
    exact (svc_interval_sum_related _ _ _ _ _ _ H1 H2 (fun tR tL Ht => if_bool_to_nat_related _ _
      (hep_job_from_hp_task_interference_correspondence j tR tL Ht))).
  Qed.

  Theorem cumulative_interference_from_hep_jobs_from_other_ep_tasks_correspondence (j : Job)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@S.cumulative_interference_from_hep_jobs_from_other_ep_tasks
        Task Job jtR PStateR arrR schedR fpR pR j t1R t2R)
      (I.Prosa_Analysis_Definitions_Interference_cumulative_interference_from_hep_jobs_from_other_ep_tasks
        Task dT Job dJ jtL PStateL arrL schedL fpL pL j t1L t2L).
  Proof.
    intros H1 H2.
    unfold S.cumulative_interference_from_hep_jobs_from_other_ep_tasks.
    cbn [I.Prosa_Analysis_Definitions_Interference_cumulative_interference_from_hep_jobs_from_other_ep_tasks].
    exact (svc_interval_sum_related _ _ _ _ _ _ H1 H2 (fun tR tL Ht => if_bool_to_nat_related _ _
      (hep_job_from_other_ep_task_interference_correspondence j tR tL Ht))).
  Qed.

  (** *** JLFP definitions *)

  Theorem another_hep_job_interference_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel
      (@S.another_hep_job_interference
        Job PStateR arrR schedR pR j tR)
      (I.Prosa_Analysis_Definitions_Interference_another_hep_job_interference
        Job dJ PStateL arrL schedL pL j tL).
  Proof.
    intro Ht.
    unfold S.another_hep_job_interference.
    cbn [I.Prosa_Analysis_Definitions_Interference_another_hep_job_interference].
    apply if_has_related.
    - intro x. exact (if_another_hep_job_related x j).
    - exact (if_served_jobs_at_related tR tL Ht).
  Qed.

  Theorem another_task_hep_job_interference_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel
      (@S.another_task_hep_job_interference
        Task Job jtR PStateR arrR schedR pR j tR)
      (I.Prosa_Analysis_Definitions_Interference_another_task_hep_job_interference
        Task dT Job dJ jtL PStateL arrL schedL pL j tL).
  Proof.
    intro Ht.
    unfold S.another_task_hep_job_interference.
    cbn [I.Prosa_Analysis_Definitions_Interference_another_task_hep_job_interference].
    apply if_has_related.
    - intro x. exact (if_another_task_hep_job_related x j).
    - exact (if_served_jobs_at_related tR tL Ht).
  Qed.

  Theorem another_hep_job_of_same_task_interference_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel
      (@S.another_hep_job_of_same_task_interference
        Task Job jtR PStateR arrR schedR pR j tR)
      (I.Prosa_Analysis_Definitions_Interference_another_hep_job_of_same_task_interference
        Task dT Job dJ jtL PStateL arrL schedL pL j tL).
  Proof.
    intro Ht.
    unfold S.another_hep_job_of_same_task_interference.
    cbn [I.Prosa_Analysis_Definitions_Interference_another_hep_job_of_same_task_interference].
    apply if_has_related.
    - intro jhp. exact (ar_bool_and_related _ _ _ _ (if_another_hep_job_of_same_task_related jhp j)
        (if_receives_service_at_related jhp tR tL Ht)).
    - exact (arrivals_up_to_correspondence_certificate Job arrR arrL Harr tR tL Ht).
  Qed.

  Theorem other_hep_jobs_interfering_workload_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel
      (@S.other_hep_jobs_interfering_workload
        Job jcR arrR pR j tR)
      (I.Prosa_Analysis_Definitions_Interference_other_hep_jobs_interfering_workload
        Job dJ jcL arrL pL j tL).
  Proof.
    intro Ht.
    unfold S.other_hep_jobs_interfering_workload.
    cbn [I.Prosa_Analysis_Definitions_Interference_other_hep_jobs_interfering_workload].
    exact (if_sum_filter_related Job _ _ _ _ _ _ (fun x => if_another_hep_job_related x j) Hjc
      (arrivals_at_correspondence_certificate Job arrR arrL Harr tR tL Ht)).
  Qed.

  Theorem cumulative_another_hep_job_interference_correspondence (j : Job)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@S.cumulative_another_hep_job_interference
        Job PStateR arrR schedR pR j t1R t2R)
      (I.Prosa_Analysis_Definitions_Interference_cumulative_another_hep_job_interference
        Job dJ PStateL arrL schedL pL j t1L t2L).
  Proof.
    intros H1 H2.
    unfold S.cumulative_another_hep_job_interference.
    cbn [I.Prosa_Analysis_Definitions_Interference_cumulative_another_hep_job_interference].
    exact (svc_interval_sum_related _ _ _ _ _ _ H1 H2 (fun tR tL Ht => if_bool_to_nat_related _ _
      (another_hep_job_interference_correspondence j tR tL Ht))).
  Qed.

  Theorem cumulative_another_task_hep_job_interference_correspondence (j : Job)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@S.cumulative_another_task_hep_job_interference
        Task Job jtR PStateR arrR schedR pR j t1R t2R)
      (I.Prosa_Analysis_Definitions_Interference_cumulative_another_task_hep_job_interference
        Task dT Job dJ jtL PStateL arrL schedL pL j t1L t2L).
  Proof.
    intros H1 H2.
    unfold S.cumulative_another_task_hep_job_interference.
    cbn [I.Prosa_Analysis_Definitions_Interference_cumulative_another_task_hep_job_interference].
    exact (svc_interval_sum_related _ _ _ _ _ _ H1 H2 (fun tR tL Ht => if_bool_to_nat_related _ _
      (another_task_hep_job_interference_correspondence j tR tL Ht))).
  Qed.

  Theorem cumulative_other_hep_jobs_interfering_workload_correspondence (j : Job)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@S.cumulative_other_hep_jobs_interfering_workload
        Job jcR arrR pR j t1R t2R)
      (I.Prosa_Analysis_Definitions_Interference_cumulative_other_hep_jobs_interfering_workload
        Job dJ jcL arrL pL j t1L t2L).
  Proof.
    intros H1 H2.
    unfold S.cumulative_other_hep_jobs_interfering_workload.
    cbn [I.Prosa_Analysis_Definitions_Interference_cumulative_other_hep_jobs_interfering_workload].
    exact (svc_interval_sum_related _ _ _ _ _ _ H1 H2 (fun tR tL Ht =>
      other_hep_jobs_interfering_workload_correspondence j tR tL Ht)).
  Qed.
End Interference.
