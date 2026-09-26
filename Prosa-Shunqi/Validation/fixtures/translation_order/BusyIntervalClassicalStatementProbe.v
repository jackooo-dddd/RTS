Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.BusyIntervalClassicalSemanticSource.
Import BusyIntervalClassicalSemanticSource.
Goal True. idtac "BEGIN|prosa.analysis.definitions.busy_interval.classical.quiet_time". Abort.
Check @quiet_time.
Goal True. idtac "END|prosa.analysis.definitions.busy_interval.classical.quiet_time". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.busy_interval.classical.busy_interval_prefix". Abort.
Check @busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.definitions.busy_interval.classical.busy_interval_prefix". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.busy_interval.classical.busy_interval". Abort.
Check @busy_interval.
Goal True. idtac "END|prosa.analysis.definitions.busy_interval.classical.busy_interval". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.busy_interval.classical.quiet_time_dec". Abort.
Check @quiet_time_dec.
Goal True. idtac "END|prosa.analysis.definitions.busy_interval.classical.quiet_time_dec". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.busy_interval.classical.quiet_time_P". Abort.
Print statement_quiet_time_P.
Goal True. idtac "END|prosa.analysis.definitions.busy_interval.classical.quiet_time_P". Abort.
