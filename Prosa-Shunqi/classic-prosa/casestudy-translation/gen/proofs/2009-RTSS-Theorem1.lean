-- @@PROOF@@
by
  have hchi : chi ≤ R := chi_is_least_solution R H_response_time_recurrence_holds
  exact CaseStudies.Common.rtb_mono (le_trans (Nat.sub_le _ _) hchi) Lemma4
