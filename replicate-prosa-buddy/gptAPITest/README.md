# gptAPITest

A minimal OpenAI Python SDK (Responses API) experiment against a local
[CLIProxyAPI](https://github.com/router-for-me/CLIProxyAPI) proxy, which forwards
requests to the ChatGPT/Codex backend using a Codex OAuth login.

Verified on 2026-10-05 with CLIProxyAPI 8.0.15 (Homebrew), `openai` 3.24.0, Python 3.13.7,
model `gpt-6-luna`.

## Files

| File | Purpose |
|---|---|
| `test_api.py` | Lists models, picks `gpt-6-luna` (or falls back to another `gpt-*`), sends one prompt via `client.responses.create` |
| `requirements.txt` | `openai` SDK |
| `.env` | `CLIPROXY_BASE_URL` and `CLIPROXY_API_KEY`: the **local proxy key** from CLIProxyAPI's `api-keys`, not an OpenAI key. `chmod 600`, git-ignored |
| `.venv/` | Virtual environment (git-ignored) |

## Run

```bash
cd "/Users/shunqiwang/CityuHK/Research/Lean/TranslationProof/replicate-prosa-buddy/gptAPITest"
.venv/bin/python test_api.py                                                    # "Reply with exactly: CLIProxyAPI works"
.venv/bin/python test_api.py "Explain in two sentences what a theorem prover is."
MODEL=gpt-6-sol .venv/bin/python test_api.py                                    # another model
```

Recreate the environment: `python3 -m venv .venv && .venv/bin/pip install -r requirements.txt`.

## CLIProxyAPI service

| | |
|---|---|
| Binary | `/opt/homebrew/opt/cliproxyapi/bin/cliproxyapi` (Homebrew formula `cliproxyapi`) |
| Config | `/opt/homebrew/etc/cliproxyapi.conf` (original example backed up as `cliproxyapi.conf.example.bak.*`) |
| OAuth credentials | `~/.cli-proxy-api/codex-*.json` (secret; auto-refreshed by the proxy) |
| Endpoint | `http://127.0.0.1:8317/v1` (localhost only; requires `Authorization: Bearer <local key>`) |
| Start | `brew services start cliproxyapi`, then if `brew services info cliproxyapi` shows `Running: false`: `launchctl kickstart gui/$(id -u)/sh.brew.cliproxyapi` |
| Stop | `brew services stop cliproxyapi` (also removes the login item) |
| Logs | `brew services` defines no log file; for debugging, stop the service and run the binary in the foreground |
| Re-login | `cliproxyapi -codex-login -no-browser` (open the printed URL; callback on port 1455) |

The proxy sends its upstream traffic through the local HTTP proxy `127.0.0.1:7897` (`proxy-url` in the config).
That proxy app must be running. A direct connection from this network gets a 403
"Unable to load site" from chatgpt.com, which CLIProxyAPI mislabels as `insufficient_quota`.

## Troubleshooting

```bash
curl -s -o /dev/null -w '%{http_code}\n' http://127.0.0.1:8317/v1/models    # 401 = running (no key sent)
set -a; . ./.env; set +a; curl -s -H "Authorization: Bearer $CLIPROXY_API_KEY" $CLIPROXY_BASE_URL/models
```
