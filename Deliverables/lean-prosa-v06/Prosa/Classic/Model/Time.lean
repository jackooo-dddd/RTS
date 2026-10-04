-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/time.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 1)

/-!
Classic Prosa's discrete time.  The source wraps its definitions in
`Module Time`; the Rocq module path is mirrored by the Lean namespace
`Prosa.Classic.Model.Time.Time`.
-/



namespace Prosa.Classic.Model.Time.Time

/-- Time is defined as a natural number. -/
abbrev time := Nat

/-- A duration of time. -/
abbrev duration := time

/-- An instant in time. -/
abbrev instant := time

end Prosa.Classic.Model.Time.Time
