import Prosa.Analysis.Facts.BusyInterval.CarryIn
import Validation.fixtures.translation_order.ExistenceComputationInterface
import Validation.fixtures.translation_order.SupplyComputationInterface
import Validation.fixtures.translation_order.CarryInComputationInterface

/-!
Export root for `analysis/facts/busy_interval/carry_in.v`: the nine statements
together with the accepted busy-interval-existence export root, the accepted
supply export root (whose kernel-guarded blackout projection relates the
blackout interval sum) and the accepted carry-in export root. No statement
contains a raw interval sum, so no new normalization guard is needed.
-/
