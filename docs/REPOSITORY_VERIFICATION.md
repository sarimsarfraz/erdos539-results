# Private repository verification

This repository starts from the 882-file audited release tree. It has a fresh Git history. The reviewed PDF, paper license, citation details, repository-integrity verifier, and GitHub workflow are added for distribution. No Lean source, mathematical statement, dependency revision or proof-checker behavior is changed.

## Two distinct checks

- `python3 scripts/verify-release.py` checks the complete source inventory against `docs/release-files.json`, verifies every Lean source against the dated kernel-check receipt, verifies toolchain/manifest and paper hashes, checks local documentation links, and independently regenerates all packaged finite certificates in a temporary directory. It needs only Python 3 and runs on GitHub Actions with a read-only token. It is an integrity check, not a new Lean proof check.
- `LEAN_MAX_MEMORY_MB=4096 python3 scripts/check.py` runs the canonical Lean audit, one synchronous compiler process at a time. The private repository setup reused only hash-matched artifacts from the audited release and ran a fresh transitive axiom audit. See `REPOSITORY_SETUP.json`. This is revalidation, not a second clean rebuild.

The clean rebuild of 14–15 October and the earlier upstream checks remain recorded in `RELEASE_BUILD.json`. The current receipt is `verification.json`; all encoded project declarations must use only `propext`, `Classical.choice`, and `Quot.sound`.

## Maintaining the inventory

After reviewing intentional changes, update the inventory explicitly with:

```sh
python3 scripts/verify-release.py --write-manifest
python3 scripts/verify-release.py
```

The manifest is an inventory, not a signature or independent attestation. It excludes only itself and ignored runtime directories. Changing a Lean proof requires a fresh successful Lean check and corresponding receipt before the integrity check can pass. Never treat regeneration of hashes as verification of a changed proof.

Private build caches and logs are ignored by Git. The GitHub workflow does not install Lean, download dependencies, publish releases, or change repository visibility. Public release and the two upstream submissions remain subject to the author's approval.
