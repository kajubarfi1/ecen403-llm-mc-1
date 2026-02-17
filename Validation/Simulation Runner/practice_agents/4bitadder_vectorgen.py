import argparse
import json
import requests
from typing import Any, Dict, List

BASE_URL = "https://chat-api.tamu.ai"
API_KEY  = "sk-9f7d56e5a44f4abd8291ba2af14d35cd"
MODEL_ID = "protected.gemini-2.5-pro"
ENDPOINT = "/openai/chat/completions"

VECTOR_COUNT = 10  


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

def sse_chat(messages: List[Dict[str, str]], temperature=0.2, max_tokens=2000) -> str:
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

    # SSE streaming
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

    return "".join(out)

def call_json(messages: List[Dict[str, str]], temperature: float, max_tokens: int, retries: int = 1) -> Any:
    for _ in range(retries + 1):
        text = sse_chat(messages, temperature=temperature, max_tokens=max_tokens)
        try:
            return json.loads(extract_first_object(text))
        except Exception:
            messages = messages + [{
                "role": "user",
                "content": "Return ONLY strict JSON (double quotes, no trailing commas, no markdown, no extra text)."
            }]
    raise RuntimeError("Failed to parse JSON from model output.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rtl-file", required=True)
    ap.add_argument("--no-expected", action="store_true", help="Generate stimulus-only vectors")
    args = ap.parse_args()

    rtl = open(args.rtl_file, "r", encoding="utf-8").read()

    # Phase A: infer interface
    iface = call_json([
        {"role": "system", "content": "Return ONLY valid JSON. No markdown."},
        {"role": "user", "content":
            "Infer interface from RTL. Return JSON keys: module_name, ports[{name,dir,width}], notes.\n\nRTL:\n" + rtl
        }
    ], temperature=0.0, max_tokens=1500)

    with open("interface.json", "w", encoding="utf-8") as f:
        json.dump(iface, f, indent=2)
    print("[OK] interface.json")

    # Phase B: generate vectors
    expected_note = "Stimulus-only." if args.no_expected else "Include exp_sum/exp_cout if outputs exist."
    vectors = call_json([
        {"role": "system", "content": "Return ONLY valid JSON. No markdown."},
        {"role": "user", "content":
            f"Generate EXACTLY {VECTOR_COUNT} vector-based tests for a 4-bit adder from this interface. "
            f"{expected_note}\n"
            "Return STRICT JSON keys: vector_schema, vectors, rationale.\n"
            "Use integers only. Keep it compact.\n\nINTERFACE:\n" + json.dumps(iface)
        }
    ], temperature=0.2, max_tokens=2500)

    with open("vectors.json", "w", encoding="utf-8") as f:
        json.dump(vectors, f, indent=2)
    print("[OK] vectors.json")


if __name__ == "__main__":
    main()
