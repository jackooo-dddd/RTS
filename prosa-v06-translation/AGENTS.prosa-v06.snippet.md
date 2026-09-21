## Prosa v0.6 translation

处理 `Prosa-Shunqi/` 的 Rocq→Lean 翻译、迁移、证明重建或表示调整时，先读取仓库根目录 `.agents/skills/prosa-v06-translation/SKILL.md`，再按需读取其 references。

固定 v0.6 source 决定语义；读取当前正式 mapping policy、DAG 和有效 manifest。旧 `Prosa-fei/` 默认只读，只提供候选与 proof 提示。不要把旧 dashboard、已存在文件或 Lean 编译成功当作语义认证。

新 computational definition 先考虑 actual-artifact validation 的计算接口；冻结 statement 后补 proof，按现有 validator 的审计结果记录 acceptance。不要通过 skill 或手写状态绕过 gate。用户指定的批次范围仍然有效。
