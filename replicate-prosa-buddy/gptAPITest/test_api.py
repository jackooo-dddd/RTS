"""Minimal OpenAI Python SDK test against a local CLIProxyAPI endpoint.

Reads the base URL and the *local* proxy key (from CLIProxyAPI's `api-keys`, not an
OpenAI key) from environment variables or the `.env` file next to this script.

Usage:
    .venv/bin/python test_api.py                      # simple check
    .venv/bin/python test_api.py "Your prompt here"   # custom prompt
    MODEL=gpt-6-sol .venv/bin/python test_api.py      # override the model
"""

import os
import sys
from pathlib import Path

from openai import OpenAI

DEFAULT_PROMPT = "Reply with exactly: CLIProxyAPI works"
PREFERRED_MODEL = "gpt-6-luna"


def load_dotenv(path: Path) -> None:
    """Tiny .env loader (KEY=VALUE lines); existing env vars take precedence."""
    if not path.is_file():
        return
    for line in path.read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            key, value = line.split("=", 1)
            os.environ.setdefault(key.strip(), value.strip())


def main() -> int:
    load_dotenv(Path(__file__).with_name(".env"))
    base_url = os.environ.get("CLIPROXY_BASE_URL", "http://127.0.0.1:8317/v1")
    api_key = os.environ.get("CLIPROXY_API_KEY")
    if not api_key:
        sys.exit("CLIPROXY_API_KEY is not set (expected in .env or the environment).")

    client = OpenAI(base_url=base_url, api_key=api_key)

    available = sorted(m.id for m in client.models.list().data)
    model = os.environ.get("MODEL", PREFERRED_MODEL)
    if model not in available:
        gpt = [m for m in available if m.startswith("gpt-")]
        print(f"Model {model!r} not available. GPT models exposed: {gpt}")
        if not gpt:
            return 1
        model = gpt[0]
        print(f"Falling back to {model!r}")

    prompt = " ".join(sys.argv[1:]) or DEFAULT_PROMPT
    print(f"Endpoint: {base_url}\nModel:    {model}\nPrompt:   {prompt}\n")

    response = client.responses.create(model=model, input=prompt)
    print("Response:", response.output_text)
    if response.usage:
        print(f"(tokens: in={response.usage.input_tokens}, out={response.usage.output_tokens})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
