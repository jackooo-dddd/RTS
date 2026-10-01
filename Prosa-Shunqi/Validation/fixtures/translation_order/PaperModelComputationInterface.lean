import Prosa.Results.TransferSchedulability.PaperModel
import Validation.fixtures.translation_order.CriterionComputationInterface
import Validation.fixtures.translation_order.FinishTimeExportInterface

/-!
Export root for `results/transfer_schedulability/paper_model.v`: its definitions (with the source's local readiness
instance `delayed_precedence_ready_instance`, which the statements mention), the theorem `online_response_time_bound`
with its proof (the body of `online_finish_time` uses it), and the other six statements (statement-only), together with
the accepted criterion and finish-time export roots. No new equation is added.
-/
