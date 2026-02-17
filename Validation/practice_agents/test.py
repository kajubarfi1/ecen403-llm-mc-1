import requests, json

BASE_URL = "https://chat-api.tamu.ai"
API_KEY = "sk-cebfc2b3d2724329914952d75ba52943"

resp = requests.get(
    f"{BASE_URL}/openai/models",
    headers={"accept":"application/json", "Authorization": f"Bearer {API_KEY}"},
    timeout=30
)
print(resp.status_code)
print(resp.text[:300])
