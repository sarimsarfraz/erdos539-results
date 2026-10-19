# Reproducing the formal proofs

## Environment

Use the versions in `lean-toolchain` and `lake-manifest.json`. The release derives from `53b83d4e81b4f3a80b3c55b44f945c714f1c7cff`, with generated reflection certificates repartitioned for bounded memory; their public statements are unchanged. See `docs/RELEASE_BUILD.json` and the release manifest for source derivation and file hashes. Do not replace the proof project's pins with Formal Conjectures' newer toolchain.

Install the exact pinned Lean toolchain using the normal official elan workflow if it is not already installed. Python 3 and Git are also required. Dependency downloads need network access; proof checking can run offline once the required dependencies and compiled caches are present.

## Dependency cache

The project includes a bounded cache helper. From the repository root, fetch only the explicitly imported Mathlib modules and their dependencies:

```sh
python3 scripts/cache.py $(python3 scripts/cache-imports.py)
```

The cache helper checks that the pinned toolchain is already installed and holds the same build lock as the verifier. Lake resolves the pinned dependencies from the committed manifest. Cache retrieval may need substantial disk space; it does not mean Mathlib has been rebuilt from source.

## Serial verification

```sh
LEAN_MAX_MEMORY_MB=4096 python3 scripts/check.py
```

The checker uses one Lean worker, disables asynchronous elaboration (`-DElab.async=false`), and defaults to a 4096 MB Lean memory limit; the full-check command above states that ceiling explicitly. A 2048 MB ceiling is insufficient for this proof environment. It refuses a non-positive or invalid `LEAN_MAX_MEMORY_MB`. If a proof exceeds the limit, the process fails and the full check is incomplete. Choose a larger positive ceiling only when appropriate for the machine; the checker never increases it automatically. This is Lean's memory control, not a limit on the total memory of other applications or every operating-system allocation.

The default target is `Erdos539.Audit`, importing the canonical release umbrella. It verifies all reachable local/vendored proofs, checks the exact upstream threshold definitions, ensures the unrestricted lower-bound import closure has no PFR dependencies, and rejects any transitive axiom outside `propext`, `Classical.choice`, and `Quot.sound`.

For focused checks, pass a module name, for example:

```sh
python3 scripts/check.py Erdos539.AllDimensionBounds
```

A focused check is not a replacement for the full canonical audit.

## Clean project build

Extract the approved source archive into a fresh directory. Its local `.lake/build` must initially be absent or empty. Fetch the required dependency cache, then run the verifier. Do not copy compiled `Erdos539` or vendored `PFR` artifacts from another project build. It is valid to reuse the pinned external dependency cache; this must be reported separately from project-source compilation.

The release audit used an isolated source extraction and shared the already installed dependency cache, verified against all nine manifest revisions. An interrupted run may resume using only matching artifacts built inside that initially empty extraction. Such a resumed run remains a project-source rebuild, but its interruption, reuse and completion status must be recorded.

## Receipts

The full checker writes `docs/verification.json` only after its target passes. An earlier receipt may still exist after a failed run: check the dated release status and process exit code, not merely the presence of that file. Focused checks write `build-logs/partial-verification.json`. Logs and the release manifest identify the exact source revision and what was actually executed.

The current release review's status is in `docs/RELEASE_AUDIT.md`. No receipt certifies untracked drafts, newly added proofs, or the manuscript's English exposition unless those are separately checked.

## Finite-certificate generators

The optional certificate generators read the captured inputs in `data/`. All generated proof sources are included already. Generation is not part of the trusted verification step; every generated claim still requires Lean checking. Use a separate working copy to regenerate files.
