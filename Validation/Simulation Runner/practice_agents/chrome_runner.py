#!/usr/bin/env python3
import json
import requests
import subprocess
from typing import Any, Dict, List

BASE_URL = "https://chat-api.tamu.ai"
API_KEY  = "sk-9f7d56e5a44f4abd8291ba2af14d35cd"
MODEL_ID = "protected.gemini-2.5-pro"
ENDPOINT = "/openai/chat/completions"

INSTRUCTION = "open google chrome"  # <-- hard-coded


def strip_fences(text: str) -> str:
    text = text.strip()
    if text.startswith("```json"):
        text = text[len("```json"):].lstrip()
    elif text.startswith("```"):
        text = text[len("```"):].lstrip()
    if text.endswith("```"):
        text = text[:-3].rstrip()
    return text.strip()

def extract_first_object(text: str) -> str:
    text = strip_fences(text)
    start = text.find("{")
    if start < 0:
        return text

    depth, in_str, esc = 0, False, False
    for i in range(start, len(text)):
        ch = text[i]
        if in_str:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
        else:
            if ch == '"':
                in_str = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    return text[start:i+1]
    return text

def sse_chat(messages: List[Dict[str, str]], temperature=0.0, max_tokens=200) -> str:
    url = BASE_URL.rstrip("/") + ENDPOINT
    headers = {
        "accept": "application/json",
        "content-type": "application/json",
        "Authorization": f"Bearer {API_KEY}",
    }
    payload = {
        "model": MODEL_ID,
        "messages": messages,
        "temperature": temperature,
        "max_tokens": max_tokens,
    }

    r = requests.post(url, headers=headers, json=payload, stream=True, timeout=120)
    r.raise_for_status()
    ctype = (r.headers.get("content-type") or "").lower()

    if "text/event-stream" not in ctype:
        return r.json()["choices"][0]["message"]["content"]

    out: List[str] = []
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

    return "".join(out)

def call_json(messages: List[Dict[str, str]], retries: int = 1) -> Any:
    last_text = ""
    for _ in range(retries + 1):
        last_text = sse_chat(messages, temperature=0.0, max_tokens=200)
        try:
            return json.loads(extract_first_object(last_text))
        except Exception:
            messages = messages + [{
                "role": "user",
                "content": (
                    "Return ONLY strict JSON.\n"
                    "Schema EXACTLY: {\"action\":\"open_chrome\"|\"noop\",\"reason\":\"string\"}\n"
                    "No markdown. No extra text."
                )
            }]

    with open("last_model_output.txt", "w", encoding="utf-8") as f:
        f.write(last_text)

    raise RuntimeError("Failed to parse JSON from model output. See last_model_output.txt")


def open_chrome() -> None:
    subprocess.run(["open", "-a", "Google Chrome"], check=True)


def main():

    try:
        decision = call_json([
            {"role": "system", "content": (
                "You are an action router on macOS.\n"
                "Return ONLY strict JSON.\n"
                "Allowed actions: open_chrome, noop.\n"
                "Schema: {\"action\":\"open_chrome\"|\"noop\",\"reason\":\"string\"}\n"
                "If the user asks to open Chrome or a browser, action=open_chrome. Otherwise noop."
            )},
            {"role": "user", "content": INSTRUCTION}
        ], retries=1)

        action = str(decision.get("action", "noop"))
        reason = str(decision.get("reason", ""))

    except Exception:
        action = "open_chrome" if ("chrome" in INSTRUCTION.lower() or "browser" in INSTRUCTION.lower()) else "noop"

    if action == "open_chrome":
        open_chrome()
        print("[OK] Opened Google Chrome.")
    else:
        print("[NOOP]", reason or "No permitted action requested.")


if __name__ == "__main__":
    main()
