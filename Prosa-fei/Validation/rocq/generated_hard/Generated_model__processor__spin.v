Require Export prosa.behavior.all.

Module Generated_model__processor__spin.

Section ExtractedContext_0.
  Variable Job : JobType.

  Inductive processor_state :=
    Idle
  | Spin (j : Job)
  | Progress (j : Job).

End ExtractedContext_0.

Section ExtractedContext_1.
  Variable Job : JobType.
    Variable j : Job.

    Definition spin_scheduled_on (s : processor_state) (_ : unit) : bool :=
      match s with
      | Idle        => false
      | Spin j'     => j' == j
      | Progress j' => j' == j
      end.

End ExtractedContext_1.

End Generated_model__processor__spin.

Check @Generated_model__processor__spin.processor_state.
Check @Generated_model__processor__spin.spin_scheduled_on.
