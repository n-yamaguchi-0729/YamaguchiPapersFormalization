#!/usr/bin/env python3
"""Keep diagnostics visible; recognize exactly one explicitly authorized unproved theorem.

Copyright 2026 Naganori Yamaguchi.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
"""
from pathlib import Path
import json
import re
import sys

SOURCE = "Lean4/AnabelianGeometry/GeometricFundamentalGroup/CharZeroPresentation.lean"
THEOREM = "exists_surfacePresentation_charZero"
NAMESPACE = "AnabelianGeometry.GeometricFundamentalGroup"


def authorized_location(root):
    """Fail closed if the source no longer has the reviewed single unfinished proof."""
    path = root / SOURCE
    if not path.is_file():
        return None
    text = path.read_text()
    # Strip nested Lean comments and strings while preserving line/column positions.
    output = list(text)
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                output[i:i+2] = "  "
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                output[i:i+2] = "  "
                i += 2
                continue
            if text[i] != "\n":
                output[i] = " "
        elif quoted:
            if text[i] == "\\" and i + 1 < len(text):
                output[i:i+2] = "  "
                i += 2
                continue
            if text[i] == '"':
                quoted = False
            if text[i] != "\n":
                output[i] = " "
        elif text.startswith("/-", i):
            depth = 1
            output[i:i+2] = "  "
            i += 2
            continue
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            output[i:end] = " " * (end-i)
            i = end
            continue
        elif text[i] == '"':
            quoted = True
            output[i] = " "
        i += 1
    code = "".join(output)
    declarations = list(re.finditer(r"(?m)^theorem " + THEOREM + r"\b", code))
    if len(declarations) != 1 or re.findall(r"\b(?:sorry|admit|sorryAx)\b", code) != ["sorry"]:
        return None
    start = declarations[0].start()
    if not re.search(r":= by\s+sorry\s+end " + re.escape(NAMESPACE) + r"\s*\Z", code[start:]):
        return None
    return code[:start].count("\n") + 1


def classify(root, content):
    line = authorized_location(root)
    diagnostics = [s for s in content.splitlines() if re.match(r"^(warning|error):", s)]
    allowed = []
    unexpected = []
    expected = f"warning: {SOURCE}:{line}:8: declaration uses `sorry`"
    for diagnostic in diagnostics:
        if line is not None and diagnostic == expected and not allowed:
            allowed.append(diagnostic)
        else:
            unexpected.append(diagnostic)
    return {"authorized_unproved_count": len(allowed), "unexpected_count": len(unexpected),
            "authorized_unproved": allowed, "unexpected": unexpected,
            "proof_status": ("one user-authorized theorem remains unproved" if line is not None else "no authorized unproved theorem in this package")}


if __name__ == "__main__":
    log = Path(sys.argv[1])
    result = classify(Path(__file__).resolve().parents[2], log.read_text(errors="replace"))
    print(json.dumps(result, ensure_ascii=False))
    sys.exit(1 if result["unexpected_count"] else 0)
