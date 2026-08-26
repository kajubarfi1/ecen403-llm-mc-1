"""
LLM Client with Automatic Fallback
=====================================
Tries TAMU AI first. If TAMU quota/rate-limit is hit, falls back to your
personal Anthropic API key seamlessly.

Environment Variables:
    TAMU_AI_API_KEY       –TAMU AI key (required for TAMU endpoint)
    ANTHROPIC_API_KEY     – personal Anthropic key (fallback)
    LLM_PROVIDER          – Force a provider: "tamu", "anthropic", or "auto" (default)
    ANTHROPIC_MODEL       – Model for direct Anthropic calls (default: claude-sonnet-4-20250514)

"""

import json
import os
import re
import requests
from typing import Dict, List, Optional
try:
    from dotenv import load_dotenv
    load_dotenv("setup.env")
except ImportError:
    pass

# =============================================================================
# Configuration
# =============================================================================

_config = {
    # TAMU AI (OpenAI-compatible)
    "tamu_base_url": "https://chat-api.tamu.ai",
    "tamu_endpoint": "/openai/chat/completions",
    "tamu_api_key": os.environ.get("TAMU_AI_API_KEY", ""),
    "tamu_model": "protected.Claude Opus 4.5",

    # Personal Anthropic (Messages API)
    "anthropic_base_url": "https://api.anthropic.com",
    "anthropic_endpoint": "/v1/messages",
    "anthropic_api_key": os.environ.get("ANTHROPIC_API_KEY", ""),
    "anthropic_model": os.environ.get("ANTHROPIC_MODEL", "claude-sonnet-4-20250514"),
    "anthropic_api_version": "2023-06-01",

    # "auto" = try TAMU first, fallback to Anthropic
    # "tamu" = TAMU only
    # "anthropic" = Anthropic only
    "provider": os.environ.get("LLM_PROVIDER", "auto"),
}

# Errors that trigger fallback (quota exceeded, rate limited, auth issues)
_FALLBACK_STATUS_CODES = {429, 402, 403, 503}

# Content patterns that indicate TAMU returned an error page (HTTP 200 but no real output)
_ERROR_CONTENT_PATTERNS = [
    "🚫",
    "Unexpected Error",
    "quota exceeded",
    "rate limit",
    "billing",
    "insufficient_quota",
    "You have exceeded",
    "tokens have been exhausted",
    "capacity",
]


def configure(**kwargs):
    """Override any config at runtime.

    Examples:
        configure(tamu_api_key="sk-...", provider="auto")
        configure(anthropic_api_key="sk-ant-...", anthropic_model="claude-sonnet-4-20250514")
        configure(provider="anthropic")  # skip TAMU entirely
    """
    for k, v in kwargs.items():
        # Accept convenient short names
        alias_map = {
            "tamu_key": "tamu_api_key",
            "anthropic_key": "anthropic_api_key",
            "model": "tamu_model",
        }
        key = alias_map.get(k, k)
        if key in _config:
            _config[key] = v
        else:
            raise ValueError(f"Unknown config key: {k}")


# =============================================================================
# TAMU AI (OpenAI-compatible format)
# =============================================================================

class _QuotaError(Exception):
    """Internal: signals TAMU quota/rate-limit so we can fall back."""
    pass


def _call_tamu(messages: List[Dict[str, str]], max_tokens: int = 20000,
               temperature: float = 1.0) -> str:
    """Call TAMU AI chat-completions endpoint with SSE streaming."""
    url = _config["tamu_base_url"].rstrip("/") + _config["tamu_endpoint"]
    headers = {
        "Authorization": f"Bearer {_config['tamu_api_key']}",
        "Content-Type": "application/json",
        "Accept": "application/json",
    }
    payload = {
        "model": _config["tamu_model"],
        "messages": messages,
        "temperature": temperature,
        "max_tokens": max_tokens,
        "stream": True,
    }

    r = requests.post(url, headers=headers, json=payload, stream=True, timeout=300)

    # Let the caller handle fallback-worthy errors
    if r.status_code in _FALLBACK_STATUS_CODES:
        raise _QuotaError(f"TAMU returned {r.status_code}: {r.text[:200]}")

    r.raise_for_status()

    ctype = (r.headers.get("content-type") or "").lower()
    if "text/event-stream" not in ctype:
        content = r.json()["choices"][0]["message"]["content"]
        _check_content_for_errors(content)
        return content

    out = []
    for line in r.iter_lines(decode_unicode=True):
        if not line or not line.startswith("data: "):
            continue
        data = line[6:].strip()
        if data == "[DONE]":
            break
        try:
            chunk = json.loads(data)
            out.append(chunk["choices"][0]["delta"].get("content", ""))
        except Exception:
            pass
    result = "".join(out)
    _check_content_for_errors(result)
    return result


def _check_content_for_errors(content: str):
    """Raise _QuotaError if TAMU returned an error message instead of real output."""
    if not content or len(content.strip()) < 20:
        raise _QuotaError(f"TAMU returned empty/tiny response ({len(content)} chars)")
    # Check first 500 chars for error patterns (errors show up at the start)
    snippet = content[:500].lower()
    for pattern in _ERROR_CONTENT_PATTERNS:
        if pattern.lower() in snippet:
            raise _QuotaError(
                f"TAMU returned error content (matched '{pattern}'): "
                f"{content[:150]}"
            )


# =============================================================================
# Anthropic Messages API (direct)
# =============================================================================

def _call_anthropic(messages: List[Dict[str, str]], max_tokens: int = 16000,
                    temperature: float = 1.0) -> str:
    """Call Anthropic Messages API directly with your personal key.

    Converts OpenAI-style messages to Anthropic format automatically:
      - Extracts 'system' messages into the top-level `system` param
      - Keeps user/assistant messages in order
    """
    url = _config["anthropic_base_url"].rstrip("/") + _config["anthropic_endpoint"]
    headers = {
        "x-api-key": _config["anthropic_api_key"],
        "anthropic-version": _config["anthropic_api_version"],
        "Content-Type": "application/json",
    }

    # Separate system prompt from conversation messages
    system_parts = []
    api_messages = []
    for msg in messages:
        if msg["role"] == "system":
            system_parts.append(msg["content"])
        else:
            api_messages.append({"role": msg["role"], "content": msg["content"]})

    payload = {
        "model": _config["anthropic_model"],
        "max_tokens": max_tokens,
        "temperature": temperature,
        "messages": api_messages,
    }
    if system_parts:
        payload["system"] = "\n\n".join(system_parts)

    r = requests.post(url, headers=headers, json=payload, timeout=300)
    r.raise_for_status()

    data = r.json()
    # Anthropic returns content as a list of blocks
    return "".join(
        block.get("text", "")
        for block in data.get("content", [])
        if block.get("type") == "text"
    )


# =============================================================================
# Unified call_llm with fallback
# =============================================================================


def call_llm(messages: List[Dict[str, str]], max_tokens: int = 16000,
             temperature: float = 1.0) -> str:
    """Call an LLM and return the text response.

    Behavior depends on `provider` config:
      - "tamu":      TAMU only, raise on failure
      - "anthropic": Anthropic only, raise on failure
      - "auto":      Try TAMU first, fall back to Anthropic on quota/rate errors
    """
    provider = _config["provider"]

    if provider == "anthropic":
        _check_key("anthropic_api_key", "ANTHROPIC_API_KEY")
        print("[LLM] Using Anthropic API directly")
        return _call_anthropic(messages, max_tokens, temperature)

    if provider == "tamu":
        _check_key("tamu_api_key", "TAMU_AI_API_KEY")
        return _call_tamu(messages, max_tokens, temperature)

    # --- auto mode: try TAMU, fall back to Anthropic ---
    if _config["tamu_api_key"]:
        try:
            return _call_tamu(messages, max_tokens, temperature)
        except _QuotaError as e:
            print(f"[LLM] TAMU quota/rate-limit hit: {e}")
            if _config["anthropic_api_key"]:
                print("[LLM] Falling back to personal Anthropic API key...")
                return _call_anthropic(messages, max_tokens, temperature)
            else:
                raise RuntimeError(
                    "TAMU quota exceeded and no ANTHROPIC_API_KEY set. "
                    "Set ANTHROPIC_API_KEY in your .env or environment to enable fallback."
                ) from e
        except requests.exceptions.RequestException as e:
            # Network errors, timeouts, etc.
            print(f"[LLM] TAMU request failed: {e}")
            if _config["anthropic_api_key"]:
                print("[LLM] Falling back to personal Anthropic API key...")
                return _call_anthropic(messages, max_tokens, temperature)
            raise

    # No TAMU key — go straight to Anthropic
    if _config["anthropic_api_key"]:
        print("[LLM] No TAMU key set, using Anthropic API directly")
        return _call_anthropic(messages, max_tokens, temperature)

    raise RuntimeError(
        "No API keys configured. Set TAMU_AI_API_KEY and/or ANTHROPIC_API_KEY "
        "in your .env file or environment."
    )


def _check_key(config_key: str, env_name: str):
    if not _config[config_key]:
        raise RuntimeError(
            f"Provider requires {env_name} but it is not set. "
            f"Add it to your .env file or export it."
        )


# =============================================================================
# Convenience: drop-in sse_chat replacement
# =============================================================================

def sse_chat(messages: List[Dict[str, str]], max_tokens: int = 16000) -> str:
    """Drop-in replacement for the sse_chat() function in existing agents."""
    return call_llm(messages, max_tokens=max_tokens)


# =============================================================================
# Utility
# =============================================================================

def strip_fences(text: str) -> str:
    """Remove markdown code fences, <think> blocks, and preamble."""
    text = re.sub(r'<think>.*?</think>', '', text, flags=re.DOTALL)
    text = text.strip()
    fence_markers = ["```python", "```systemverilog", "```sv", "```json", "```"]
    for marker in fence_markers:
        start_idx = text.find(marker)
        if start_idx >= 0:
            code_start = start_idx + len(marker)
            end_idx = text.find("```", code_start)
            if end_idx >= 0:
                return text[code_start:end_idx].strip()
            else:
                return text[code_start:].strip()
    return text


def status() -> dict:
    """Return current config status (safe — no keys printed in full)."""
    def mask(key: str) -> str:
        v = _config.get(key, "")
        if not v:
            return "(not set)"
        return v[:8] + "..." + v[-4:] if len(v) > 16 else "****"

    return {
        "provider": _config["provider"],
        "tamu_key": mask("tamu_api_key"),
        "tamu_model": _config["tamu_model"],
        "anthropic_key": mask("anthropic_api_key"),
        "anthropic_model": _config["anthropic_model"],
    }