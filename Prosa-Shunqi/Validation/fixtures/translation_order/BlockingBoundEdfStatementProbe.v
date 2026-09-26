Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BlockingBoundEdfSemanticSource.
Import BlockingBoundEdfSemanticSource.
Goal True. idtac "BEGIN|prosa.analysis.definitions.blocking_bound.edf.blocking_relevant". Abort.
Check @blocking_relevant.
Goal True. idtac "END|prosa.analysis.definitions.blocking_bound.edf.blocking_relevant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.blocking_bound.edf.blocking_bound". Abort.
Check @blocking_bound.
Goal True. idtac "END|prosa.analysis.definitions.blocking_bound.edf.blocking_bound". Abort.
