# Finish Time case study

从 [案例说明](finish_time_case_study.md) 开始：它按“官方 Rocq 源 → production Lean → 实际导出/导入 → Rocq correspondence → assumptions”排列，并明确指出本案例的最终证明文件。所有链接都留在本文件夹内。类型检查可先看[去掉 load-path warning 的阅读版](finish_time_alignment_readable.txt)；[原始输出](finish_time_alignment_check.txt)没有修改。

原始 `Print` / `Check`、`Print Assumptions` 和 Lean `#print axioms` 输出没有删节。原件按角色复制到 `source/`、`lean/`、`imported/`、`certificates/`、`audit/`、`provenance/`；少数副本为便于区分加了 `official` / `rocq93_compat` 后缀，但内容与原件逐字节一致。较长的产物校验值单独放在 [SHA256SUMS](SHA256SUMS)。这是一份可单独分享和阅读的证据包；重新编译整个依赖闭包仍需要原项目的固定工具链及上游库。
