# 安装 prosa-v06-translation

建议放在 Git 仓库根目录，而非只放 `Prosa-Shunqi` 内：

```text
TranslationProof/
├── .agents/
│   └── skills/
│       └── prosa-v06-translation/
│           ├── SKILL.md
│           ├── references/
│           └── assets/
├── Prosa-fei/
└── Prosa-Shunqi/
```

包中的 `.agents/skills/prosa-v06-translation/` 是完整 skill。将它合并到仓库，不移动历史翻译树，不替换现有 `AGENTS.md`。

当前官方 Codex 文档使用 `.agents/skills` 作为仓库级 skill 发现位置；不沿用此前聊天中举例的 `.codex/skills`。安装到仓库根目录，可在从根目录或 `Prosa-Shunqi/` 启动时使用。不同/较旧客户端若未识别，先用显式文件路径要求读取，并核对该客户端支持的 skill 位置。

首次可显式调用：

```text
$prosa-v06-translation
继续当前 Prosa v0.6 utility batch，先读取最新 manifest。
按 skill 处理已授权范围，不扩大 scope，不重建已有 validator。
```

仅查看 skill 不应触发翻译。下面的调用用来检查加载和理解：

```text
$prosa-v06-translation
只核对你读取的 source pin、workspace、representation policy 路径和当前任务范围，不修改文件。
```

若希望长期提醒 agent，手工把附带 `AGENTS.prosa-v06.snippet.md` 合并到适用 `AGENTS.md`。不要把整个 skill 粘进 AGENTS，也不要覆盖已有指令。

SKILL.md 是规则入口，references 只按具体任务读取。现有仓库 policy 与本包不一致时，不应自动改 policy；先核实哪个版本/决策适用。

## 安装后的检查

- `SKILL.md` YAML frontmatter 存在 `name`、`description`。
- 保留完整 references/assets，不只复制主文件。
- 在 Codex skill 列表或显式调用中确认加载。
- 按 `references/skill-smoke-tests.md` 抽测行为。
- Skill 生效不等于新 proof/validator 自动通过；必须继续运行已有 pipeline。

本包只创建在对话附件中，未写入 GitHub。附带代码示例未在固定 Lean/Rocq 工具链中编译；它们是说明性材料，不是认证 evidence。
