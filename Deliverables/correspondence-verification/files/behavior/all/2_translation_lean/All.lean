-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: behavior/all.v

import Prosa.Behavior.Time
import Prosa.Behavior.Job
import Prosa.Behavior.Arrival_sequence
import Prosa.Behavior.Schedule
import Prosa.Behavior.Service
import Prosa.Behavior.Ready

/-!
This module is the Lean aggregation counterpart of `prosa.behavior.all`.
The authoritative Rocq source contains no named declarations; its observable
role is to re-export the six behavior modules above. Lean imports are
transitive, so importing this module exposes the translated behavior boundary.
-/
