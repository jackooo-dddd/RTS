/- Validation build shim for the declaration-free `Prosa.Util.All` import
   aggregator.  The production aggregator imports unrelated modules whose
   translated theorem proofs do not compile with the pinned Mathlib version.
   This shim deliberately declares nothing; every dependency actually used by
   a target module must still be imported by that module itself. -/
