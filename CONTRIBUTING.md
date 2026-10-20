# Contributing

This public repository distributes the paper and Lean development for the Erdős #539 results. Publishing new releases, changing repository visibility, and submitting upstream contributions require the repository owner's approval.

Keep the Lean and dependency pins unchanged unless a toolchain migration is explicitly intended. Check changed proofs with the serial verifier documented in [REPRODUCING.md](docs/REPRODUCING.md); use one Lean process at a time and the 4096 MB limit. Do not introduce `sorry`, extra axioms or unchecked native-evaluation claims. Preserve third-party attribution.

Describe the mathematical statement and its hypotheses precisely. Distinguish unconditional theorems, conditional statements and open questions. Include the relevant successful verification receipt in proof changes; update the release inventory only after reviewing those changes. Disclose AI assistance and take responsibility for the contribution.

See [repository verification](docs/REPOSITORY_VERIFICATION.md) for the fast integrity check and [the theorem map](docs/PAPER_THEOREMS.md) for the paper's formal endpoints.
