From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import analysis.facts.model.ideal_uni_exceed.

Local Transparent prosa.behavior.schedule.scheduled_on
  prosa.behavior.schedule.supply_on
  prosa.behavior.schedule.service_on.

(** The source computation is derived from the official ProcessorState fields,
    not from any of this file's seven public theorem proofs. *)
Lemma facts_source_scheduled_in_iff_on (Job : eqType) (j : Job)
    (s : @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state Job) :
  is_true (@prosa.behavior.schedule.scheduled_in Job
    (@prosa.model.processor.ideal_uni_exceed.exceedance_proc_state Job) j s) <->
  is_true (@prosa.model.processor.ideal_uni_exceed.exceedance_scheduled_on
    Job j s tt).
Proof.
  split.
  - rewrite /prosa.behavior.schedule.scheduled_in.
    move/existsP=> [c H]. by destruct c.
  - move=> H. rewrite /prosa.behavior.schedule.scheduled_in.
    apply/existsP. by exists tt.
Qed.

Lemma facts_bool_iff_eq (a b : bool) :
  (is_true a <-> is_true b) -> a = b.
Proof.
  destruct a, b; simpl; intros H; try reflexivity.
  - exfalso. discriminate (proj1 H (Logic.eq_refl true)).
  - exfalso. discriminate (proj2 H (Logic.eq_refl true)).
Qed.

Lemma facts_source_scheduled_in_concrete (Job : eqType) (j : Job)
    (s : @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state Job) :
  @prosa.behavior.schedule.scheduled_in Job
    (@prosa.model.processor.ideal_uni_exceed.exceedance_proc_state Job) j s =
  @prosa.model.processor.ideal_uni_exceed.exceedance_scheduled_on
    Job j s tt.
Proof.
  apply facts_bool_iff_eq.
  exact (facts_source_scheduled_in_iff_on Job j s).
Qed.

Local Lemma facts_sum_unit1 : forall {F : unit -> nat}, \sum_r F r = F tt.
Proof.
  move=> F.
  rewrite /index_enum unlock_with -enumT /=.
  have -> : enum (unit : finType) = [:: tt]
    by rewrite /(enum _) unlock //=.
  by rewrite big_seq1.
Qed.

Lemma facts_source_supply_in_concrete (Job : eqType)
    (s : @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state Job) :
  @prosa.behavior.schedule.supply_in Job
    (@prosa.model.processor.ideal_uni_exceed.exceedance_proc_state Job) s =
  @prosa.model.processor.ideal_uni_exceed.exceedance_supply_on Job s tt.
Proof.
  rewrite /prosa.behavior.schedule.supply_in /prosa.behavior.schedule.supply_on.
  exact facts_sum_unit1.
Qed.

Lemma facts_source_service_in_concrete (Job : eqType) (j : Job)
    (s : @prosa.model.processor.ideal_uni_exceed.exceedance_processor_state Job) :
  @prosa.behavior.schedule.service_in Job
    (@prosa.model.processor.ideal_uni_exceed.exceedance_proc_state Job) j s =
  @prosa.model.processor.ideal_uni_exceed.exceedance_service_on Job j s tt.
Proof.
  rewrite /prosa.behavior.schedule.service_in /prosa.behavior.schedule.service_on.
  exact facts_sum_unit1.
Qed.

Print Assumptions facts_source_scheduled_in_iff_on.
Print Assumptions facts_source_scheduled_in_concrete.
Print Assumptions facts_source_supply_in_concrete.
Print Assumptions facts_source_service_in_concrete.
