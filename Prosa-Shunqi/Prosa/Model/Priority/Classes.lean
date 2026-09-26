-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/priority/classes.v

import Prosa.Model.Priority.Definitions
import Prosa.Model.Priority.Coercion

/-!
Lean aggregation counterpart of `prosa.model.priority.classes`.  The
authoritative Rocq module contains no named declarations; it re-exports
`model/priority/definitions.v` and `model/priority/coercion.v`.  Lean imports
are transitive, so importing this module exposes both translated modules.
-/
