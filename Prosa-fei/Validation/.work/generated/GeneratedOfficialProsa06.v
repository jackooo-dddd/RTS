From mathcomp Require Import ssreflect ssrbool eqtype fintype.
From prosa Require Import behavior.service model.processor.ideal.

(** AUTO-GENERATED from official Prosa source. Declaration blocks below
    are copied verbatim; only the legacy broad import prelude is replaced. *)
Module GeneratedOfficialProsa06.
Section ScheduleClass.
  #[local] Existing Instance ideal.processor_state.
  Local Transparent scheduled_in scheduled_on.
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  Lemma scheduled_in_def (j : Job) s :
    scheduled_in j s = (s == Some j).
  Proof.
    rewrite /scheduled_in/scheduled_on/=.
    case: existsP=>[[_->]//|].
    case: (s == Some j)=>//=[[]].
    by exists.
  Qed.

  Lemma scheduled_at_def sched (j : Job) t :
    scheduled_at sched j t = (sched t == Some j).
  Proof.
      by rewrite /scheduled_at scheduled_in_def.
  Qed.

End ScheduleClass.
End GeneratedOfficialProsa06.

Check @GeneratedOfficialProsa06.scheduled_at_def.
Print Assumptions GeneratedOfficialProsa06.scheduled_at_def.
Check @GeneratedOfficialProsa06.scheduled_in_def.
Print Assumptions GeneratedOfficialProsa06.scheduled_in_def.
