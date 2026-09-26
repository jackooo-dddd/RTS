Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.PreemptionTimeSemanticSource.
Import PreemptionTimeSemanticSource.
Goal True. idtac "BEGIN|prosa.model.schedule.preemption_time.preemption_time". Abort.
Check @preemption_time.
Goal True. idtac "END|prosa.model.schedule.preemption_time.preemption_time". Abort.
