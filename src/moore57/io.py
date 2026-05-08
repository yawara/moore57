from __future__ import annotations

import base64
import json
from pathlib import Path
from typing import Any


def _read_chunked_b64(path: Path) -> Any:
    parts = sorted(path.parent.glob(path.name + ".b64.*"))
    if not parts:
        raise FileNotFoundError(path)
    payload = "".join(p.read_text(encoding="utf-8").strip() for p in parts)
    raw = base64.b64decode(payload.encode("ascii"))
    return json.loads(raw.decode("utf-8"))


def read_json(path: str | Path) -> Any:
    path = Path(path)
    if path.exists():
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    return _read_chunked_b64(path)


def write_json(data: Any, path: str | Path, *, indent: int = 2) -> None:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=indent, sort_keys=False)
        f.write("\n")
