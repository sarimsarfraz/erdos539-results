#!/usr/bin/env python3
"""Check project and vendored sources serially; never compile Mathlib."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
os.chdir(ROOT)
lock_path = ROOT / ".lake/verification.lock"
lock_path.parent.mkdir(exist_ok=True)
lock = lock_path.open("w")
try:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
except BlockingIOError:
    sys.exit("Another project verification or cache download is active; refusing concurrency.")
toolchain = (ROOT / "lean-toolchain").read_text().strip()
try:
    memory_mb = int(os.environ.get("LEAN_MAX_MEMORY_MB", "4096"))
except ValueError:
    sys.exit("LEAN_MAX_MEMORY_MB must be a positive integer (megabytes).")
if memory_mb <= 0:
    sys.exit("LEAN_MAX_MEMORY_MB must be positive; unlimited builds are disabled.")
elan_root = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan")))
lake = elan_root / "toolchains" / toolchain.replace("/", "--").replace(":", "---") / "bin/lake"
if not lake.is_file():
    sys.exit("Pinned toolchain is not installed; refusing an automatic download.")
for name in ["IsCofactorLowerBound", "cofactorThreshold"]:
    pattern = r"(?:noncomputable )?def " + name + r"\b.*?(?=\n\n)"
    upstream = re.search(pattern, (ROOT / "docs/formal-conjectures-539-source.txt").read_text(), re.S)
    local = re.search(pattern, (ROOT / "Erdos539/Threshold.lean").read_text(), re.S)
    if not upstream or not local or upstream.group(0) != local.group(0):
        sys.exit(f"Exact Formal Conjectures definition drift: {name}")
build = ROOT / ".lake/build/lib/lean"
build.mkdir(parents=True, exist_ok=True)
seen = set()
order = []
dependencies = {}

def visit(module):
    if module in seen:
        return
    seen.add(module)
    src = ROOT / (module.replace(".", "/") + ".lean")
    dependencies[module] = []
    for imported in re.findall(r"^(?:(?:public|private|meta) )*import ([A-Za-z0-9_.]+)", src.read_text(), re.M):
        local = ROOT / (imported.replace(".", "/") + ".lean")
        if local.exists():
            dependencies[module].append(imported)
            visit(imported)
    order.append((module, src))

for target in sys.argv[1:] or ["Erdos539.Audit"]:
    visit(target)

# The unconditional FC endpoint must keep its elementary dependency boundary.
# This checks actual local imports, independently of the larger canonical root
# which intentionally retains historical PFR proofs and conditional results.
elementary_modules = set()

def visit_elementary(module):
    if module in elementary_modules:
        return
    if module == "PFR" or module.startswith("PFR.") or module in {
        "Erdos539.PFR", "Erdos539.Dimension", "Erdos539.IntegerGrowth"
    }:
        sys.exit(f"Elementary lower bound imported a PFR dependency: {module}")
    src = ROOT / (module.replace(".", "/") + ".lean")
    if not src.exists():
        return
    elementary_modules.add(module)
    for imported in re.findall(r"^(?:(?:public|private|meta) )*import ([A-Za-z0-9_.]+)", src.read_text(), re.M):
        visit_elementary(imported)

visit_elementary("Erdos539.SuperSqrt")

logdir = ROOT / "build-logs"
logdir.mkdir(exist_ok=True)
records = []
keys = {}
manifest_hash = hashlib.sha256((ROOT / "lake-manifest.json").read_bytes()).hexdigest()
for module, src in order:
    out = build / (module.replace(".", "/") + ".olean")
    out.parent.mkdir(parents=True, exist_ok=True)
    source_hash = hashlib.sha256(src.read_bytes()).hexdigest()
    key = hashlib.sha256(json.dumps([source_hash, manifest_hash, toolchain,
        [keys[d] for d in dependencies[module]]]).encode()).hexdigest()
    keys[module] = key
    statefile = out.with_suffix(".checked.json")
    if module != "Erdos539.Audit" and out.exists() and statefile.exists():
        state = json.loads(statefile.read_text())
        if state["key"] == key and state["olean_sha256"] == hashlib.sha256(out.read_bytes()).hexdigest():
            print(f"Unchanged verified module: {module}", flush=True)
            records.append({"module": module, "sha256": source_hash, "exit_code": 0,
                            "reused_verified_artifact": True})
            continue
    command = [str(lake), "env", "lean", "-j1", f"-M{memory_mb}",
               "-DElab.async=false", "-DwarningAsError=true", "-o", str(out), str(src)]
    print(f"Checking {module}", flush=True)
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end="", flush=True)
    (logdir / (module + ".log")).write_text(result.stdout)
    records.append({"module": module, "sha256": source_hash,
                    "exit_code": result.returncode})
    if result.returncode:
        sys.exit(result.returncode)
    statefile.write_text(json.dumps({"key": key,
        "olean_sha256": hashlib.sha256(out.read_bytes()).hexdigest()}))

receipt = {
    "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "toolchain": toolchain,
    "manifest_sha256": hashlib.sha256((ROOT / "lake-manifest.json").read_bytes()).hexdigest(),
    "method": "Serial lake env lean -j1 -DElab.async=false; Mathlib loaded from compiled cache",
    "lean_memory_limit_mb": memory_mb,
    "elementary_lower_bound_boundary": {
        "root": "Erdos539.SuperSqrt",
        "status": "no PFR imports in transitive local dependency closure",
        "modules": sorted(elementary_modules),
    },
    "modules": records,
    "axiom_audit_output": (logdir / "Erdos539.Audit.log").read_text()
        if any(m == "Erdos539.Audit" for m, _ in order) else None,
}
receipt_path = ROOT / "docs/verification.json" if any(
    m == "Erdos539.Audit" for m, _ in order) else logdir / "partial-verification.json"
receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
print(f"Passed: {len(records)} local modules. Receipt: {receipt_path.relative_to(ROOT)}")
