Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.ScheduleLimitedPreemptiveSemanticSource.
Import ScheduleLimitedPreemptiveSemanticSource.
Goal True. idtac "BEGIN|prosa.model.schedule.limited_preemptive.schedule_respects_preemption_model". Abort.
Check @schedule_respects_preemption_model.
Goal True. idtac "END|prosa.model.schedule.limited_preemptive.schedule_respects_preemption_model". Abort.
