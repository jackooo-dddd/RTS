-- @@PROOF@@
by
  have key : ∀ n : Nat, ∀ j : Job, job_arrival j = n → arrives_in arr_seq j → job_task j = tsk →
      completed job_cost sched j (job_arrival j + R) = true := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro j hn harr htsk
      by_contra hnc
      have hprev : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
          job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j0 + R) = true :=
        fun j0 h0 ht0 hlt => ih _ (hn ▸ hlt) j0 rfl h0 ht0
      rcases Method1_10_09 j harr htsk (by simpa using hnc) hprev with
        ⟨tk, Rk, hmem, hlt⟩ | ⟨tk, Rk, hmem, hlt⟩
      · have := interference_bound_ci j tk Rk hmem
        exact absurd hlt (Nat.not_lt.mpr (min_le_min_right _ this))
      · have := interference_bound_nc j tk Rk hmem
        exact absurd hlt (Nat.not_lt.mpr (min_le_min_right _ this))
  intro j harr htsk
  exact key _ j rfl harr htsk
