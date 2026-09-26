Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.PriorityDrivenSemanticSource.
Import PriorityDrivenSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
Require Import prosa.PreemptionTimeSemanticSource.
Import PreemptionTimeSemanticSource.
Goal True. idtac "BEGIN|prosa.model.schedule.priority_driven.respects_JLDP_policy_at_preemption_point". Abort.
Check @respects_JLDP_policy_at_preemption_point.
Goal True. idtac "END|prosa.model.schedule.priority_driven.respects_JLDP_policy_at_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.priority_driven.respects_JLFP_policy_at_preemption_point". Abort.
Check @respects_JLFP_policy_at_preemption_point.
Goal True. idtac "END|prosa.model.schedule.priority_driven.respects_JLFP_policy_at_preemption_point". Abort.
Goal True. idtac "BEGIN|prosa.model.schedule.priority_driven.respects_FP_policy_at_preemption_point". Abort.
Check @respects_FP_policy_at_preemption_point.
Goal True. idtac "END|prosa.model.schedule.priority_driven.respects_FP_policy_at_preemption_point". Abort.
