From mathcomp Require Import ssreflect ssrbool eqtype fintype.
From prosa Require Import behavior.service model.processor.ideal.

(** Source-extracted replay of the two relevant declarations from Prosa v0.6
    [analysis/facts/model/ideal/schedule.v].  The statements and proof scripts
    below are verbatim; only unrelated declarations and broad re-export imports
    are omitted so this slice remains buildable on Rocq 9.3. *)
Module OriginalProsa06IdealSchedule.

#[local] Existing Instance prosa.model.processor.ideal.processor_state.

Local Transparent
  prosa.behavior.schedule.scheduled_in
  prosa.behavior.schedule.scheduled_on.

Section ScheduleClass.
  Context {Job : prosa.behavior.job.JobType}.
  Context `{prosa.behavior.job.JobArrival Job}.
  Context `{prosa.behavior.job.JobCost Job}.

  Lemma scheduled_in_def (j : Job) s :
    prosa.behavior.schedule.scheduled_in j s = (s == Some j).
  Proof.
    rewrite /prosa.behavior.schedule.scheduled_in
            /prosa.behavior.schedule.scheduled_on/=.
    case: existsP=>[[_->]//|].
    case: (s == Some j)=>//=[[]].
    by exists.
  Qed.

  Lemma scheduled_at_def sched (j : Job) t :
    prosa.behavior.service.scheduled_at sched j t = (sched t == Some j).
  Proof.
    by rewrite /prosa.behavior.service.scheduled_at scheduled_in_def.
  Qed.
End ScheduleClass.

End OriginalProsa06IdealSchedule.

Print Assumptions OriginalProsa06IdealSchedule.scheduled_at_def.
