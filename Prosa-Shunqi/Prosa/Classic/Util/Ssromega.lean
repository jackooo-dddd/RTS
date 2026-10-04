-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/ssromega.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 3)

/-!
`classic/util/ssromega.v` defines only the Ltac tactics `arith_hypo_ssrnat2coqnat`,
`arith_goal_ssrnat2coqnat` and `ssromega` (no named declaration; the module has no
constant in Rocq's `Print Module`).  Lean proofs use `omega` instead, so this module
is intentionally empty; it exists so that the classic utility aggregator
(`Prosa.Classic.Util.All`) mirrors the source's export list.
-/
