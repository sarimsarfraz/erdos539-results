#!/usr/bin/env python3
"""Fetch selected Mathlib caches in the single project, under its build lock."""
from pathlib import Path
import fcntl
import os
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
os.chdir(root)
if not sys.argv[1:] or any(not x.startswith("Mathlib.") for x in sys.argv[1:]):
    sys.exit("Supply explicit Mathlib module names; an unbounded full download is disabled.")
(root / ".lake").mkdir(exist_ok=True)
lock = (root / ".lake/verification.lock").open("w")
try:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
except BlockingIOError:
    sys.exit("Another project verification or cache download is active; refusing concurrency.")
subprocess.run(["df", "-h", str(root)], check=True)
toolchain = (root / "lean-toolchain").read_text().strip()
elan_root = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan")))
lake = elan_root / "toolchains" / toolchain.replace("/", "--").replace(":", "---") / "bin/lake"
if not lake.is_file():
    sys.exit("Pinned toolchain is absent; refusing automatic toolchain installation.")
env = dict(os.environ, MATHLIB_CACHE_DIR=str(root / ".cache/mathlib"))
sys.exit(subprocess.run([str(lake), "exe", "cache", "get", *sys.argv[1:]], env=env).returncode)
