"""Definition variants of the 2015-BOOK case study (Lemma 18.1)."""
from snippets_base import TASK
S = {}
S["max_jobs#B"] = f"""def max_jobs {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_tsk delta : time) : Nat :=
  div_floor (delta + R_tsk - task_cost tsk) (task_period tsk)"""
S["W#B"] = f"""def W {TASK}
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_tsk delta : time) : Nat :=
  let e_k := task_cost tsk
  let p_k := task_period tsk
  min e_k (delta + R_tsk - e_k - max_jobs task_cost task_period tsk R_tsk delta * p_k) +
    max_jobs task_cost task_period tsk R_tsk delta * e_k"""
