#!/usr/bin/env python3
"""List explicit Mathlib imports needed by the canonical local source closure."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
seen = set()
mathlib = set()

def visit(module):
    if module in seen:
        return
    seen.add(module)
    path = root / (module.replace(".", "/") + ".lean")
    for name in re.findall(r"^(?:(?:public|private|meta) )*import ([A-Za-z0-9_.]+)", path.read_text(), re.M):
        local = root / (name.replace(".", "/") + ".lean")
        if local.is_file():
            visit(name)
        elif name.startswith("Mathlib."):
            mathlib.add(name)
        elif name == "Mathlib":
            raise SystemExit("Unbounded Mathlib import: request explicit modules instead.")

visit("Erdos539.Audit")
print("\n".join(sorted(mathlib)))
