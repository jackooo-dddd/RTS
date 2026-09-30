Require Export prosa.behavior.service.

(** 在已经知道 job j 一定会在某个有限时间内完成的前提下，定义 finish_time 为 j 第一次完成的时刻，
    并证明这个时间确实是它第一次完成的时刻。最后再用它定义精确的 response time。
    已知：job_response_time_bound sched j R (假设 job 最终会完成)
            ▼
    j 最晚在 arrival + R 时已经完成
            ▼
    ∃ t, completed_by sched j t
            ▼
    从所有完成时刻中取最小的那个
            ▼
    finish_time
            ├── ① finish_time 时确实已经完成
            ├── ② finish_time 是最早的完成时间
            └── ③ satisfies completes_at
            ▼
    response_time = finish_time - arrival *)
(** 为什么 Rocq 里面没有 include？ 因为 Rocq 的 Section dependency 处理方式不同。 
虽然 statement exists t, completed_by sched j t. 没有显式出现 R 和 H_response_time_bounded，
但是 Rocq 会看 proof 实际使用了哪些 Section variables。然后在 End JobFinishTime. 之后自动 generalize 必要的 dependency。*)
Section JobFinishTime.

  (** Consider any type of jobs with arrival times and costs ... *)
  Context {Job : JobType} `{JobArrival Job} `{JobCost Job}.

  (** ... and any schedule of such jobs. *)
  Context {PState : ProcessorState Job}.
  Variable sched : schedule PState.

  (** Consider an arbitrary job [j]. *)
  Variable j : Job.

  (** In the following, we proceed under the assumption that [j] finishes
      eventually (i.e., no later than [R] time units after its arrival, for any
      finite [R]). *)
  Variable R : nat.
  Hypothesis H_response_time_bounded : job_response_time_bound sched j R.

  (** 证明至少存在一个完成时间 t *)
  #[local] Corollary job_finishes : exists t, completed_by sched j t.
  Proof. by exists (job_arrival j + R); exact: H_response_time_bounded. Qed.

  (** ex_minn 的意思基本就是：如果已经知道 ∃ t, P t，那么取使得 P t 成立的 最小自然数 t。 
  所以 finish_time = 最小的 t，使得 completed_by sched j t 成立*)
  Definition finish_time : instant := ex_minn job_finishes.

  (** In the following, we demonstrate the reuse of [ex_minn] properties by
      establishing three natural properties of a job's finish time. *)

  (** First property, a job is indeed complete at its finish time. 
  确保这个时间本身是完成时间。*)
  Corollary finished_at_finish_time : completed_by sched j finish_time.
  Proof.
    rewrite /finish_time/ex_minn.
    by case: find_ex_minn.
  Qed.

  (** Second property, a job's finish time is the earliest time that it is complete. 
  finish_time 确实是 job j 第一次完成的时间。*)
  Corollary earliest_finish_time :
    forall t,
      completed_by sched j t ->
      finish_time <= t.
  Proof.
    move=> t COMP.
    rewrite /finish_time/ex_minn.
    by case: find_ex_minn.
  Qed.

  (** Third property, Prosa's notion of [completes_at] is satisfied at the finish time. 
  把刚刚得到的数学性质，对接回 Prosa 已经存在的 completes_at 定义。
  completed_by j t 表示到 t 为止完成了。
  completes_at j t 更强， 表示恰好在 t 完成。
  completes_at sched j finish_time 是在说我们自己通过 ex_minn 定义出来的这个 finish_time，
  和 Prosa 原本“恰好在某时完成”的概念是一致的。*)
  Corollary completes_at_finish_time :
    completes_at sched j finish_time.
  Proof.
    apply/andP; split; last exact: finished_at_finish_time.
    apply/orP; case FIN: finish_time; [by right|left].
    apply: contra_ltnN => [?|];
      first by apply: earliest_finish_time.
    by lia.
  Qed.

  (** Finally, we can define a job's precise response time as usual as the time
      from its arrival until its finish time. *)
  Definition response_time : duration := finish_time - job_arrival j.

End JobFinishTime.
