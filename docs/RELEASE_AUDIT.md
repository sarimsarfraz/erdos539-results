# Release audit — 19 October 2026

**The canonical release-source rebuild passed: 844 modules and 12,917 project declarations. This records the verified source snapshot for version 0.1.0.** The clean rebuild completed on 14–15 October. On 19 October, source/artifact hash validation and a fresh transitive axiom audit passed again, reusing unchanged verified artifacts; this later check is not a second clean rebuild.

## What passed

The canonical imported development was rebuilt in an isolated source extraction that began with zero local compiled artifacts. Interrupted attempts resumed only matching artifacts generated there; no old project artifacts were copied from the working repository. The nine external dependency revisions and their clean tracked sources were checked against the manifest. Their compiled cache was reused; Mathlib itself was not rebuilt.

The final axiom audit allows only `propext`, `Classical.choice`, and `Quot.sound`. The final 12,917 declarations include definitions and generated helpers, not just theorems. The preceding full pass counted 12,934; re-elaboration changed the helper count while the source statements remained unchanged. The final receipt is authoritative. Five preserved upstream Lean reference files under `vendor-sources/` are outside the compiled closure; their original source hashes and attribution are retained.

Every current canonical module has now been checked with a Lean ceiling of at most 4096 MB. Checks run one Lean process at a time. The earliest 88 artifacts, created before that ceiling was agreed, were explicitly rebuilt under the cap, followed by the full axiom audit. The source-build phases, source derivation, memory measurements and receipt hash are recorded in [RELEASE_BUILD.json](RELEASE_BUILD.json); the final per-module source hashes and axiom output are in [verification.json](verification.json).

## Why the source layout changed

The baseline at `53b83d4e81b4f3a80b3c55b44f945c714f1c7cff` contained 747 canonical modules and its prior audit covered 8,904 declarations. Initial 2048 MB checks and later 4096 MB checks exceeded their limits. Synchronous elaboration alone did not fix every reflection certificate.

The release refactors 25 generated reflection wrappers into 97 additional small imported parts and checks large finite energy sums in kernel-checked chunks. All 874 public certificate theorem statements and all 387 digit lists are unchanged. No native-evaluation axiom, new hypothesis or stronger mathematical claim was introduced. The higher module/declaration counts reflect proof organization, not additional mathematical results. The original working tree's unfinished five-mask import and drafts are preserved and excluded from the release source tree.

## Paper and upstream correspondence

Both headline bounds and their supporting estimates were checked against actual Lean statements, including constants, quantifiers, zero handling and hypotheses. The paper now explicitly requires positive integers in the valuation dictionary and positive dimensions in the relevant bounds, and translates exchange competitors before invoking minimality. The updated source compiles with the existing editor's built-in compiler. Completion/exchange propositions remain written mathematics outside the completed formalization; the unrestricted problem remains open.

The exact proposed DeepMind proposition passed against the freshly rebuilt release artifacts, using only the permitted standard axioms. The patch applies to the pinned upstream source. The actual upstream v4.33.1 changed-module build and configured custom linters now pass with warnings treated as errors, one Lean process at a time and a 4096 MB ceiling. The external proof stays on its own pinned v4.29.0-rc8 toolchain.

## Pre-publication review, repository setup and release

The manuscript, theorem correspondence, proof sources, citation information and both upstream PR candidates have been checked. The source and matching 17-page PDF include Sarim Sarfraz (University of Toronto) and Wali Ahmed (Columbia University). The paper and software licenses have been approved. The authors authorized the coordinated public release and both upstream submissions on 19 October 2026. Their publication and review status is tracked separately from these proof-checking receipts.

The reviewed source tree is published in the dedicated release repository `sarimsarfraz/erdos539-results`. Its isolated history does not include the original research repository's history, private working notes or unfinished proofs. [Repository verification](REPOSITORY_VERIFICATION.md) records its separate setup checks and links to the published records and submitted PRs. The Google CLA check passed on both [PR #7457](https://github.com/google-deepmind/formal-conjectures/runs/118315269075) and [PR #7458](https://github.com/google-deepmind/formal-conjectures/runs/118315359499), as verified on 19 October 2026; this is separate from mathematical review or acceptance.

The final upstream patches, including their paper references and immutable proof links, passed focused checks on 19 October 2026, individually and together. The ten supporting API lemmas and both exact-statement bridges also passed. These checks ran serially under the 4096 MiB limit. The current AI disclosure credits OpenAI GPT-6 Astra through Codex as the primary AI tool, with additional assistance from Anthropic Claude. The submitting author remains responsible for understanding the formalization and writing reviewer responses. Hosted CI and maintainer review are separate from these local checks.

## Final editorial revision

The approved title is *Gcd quotients: a quantitative lower bound and sharp fixed-dimensional orders*. The introduction and construction section now distinguish the earlier planar exponent and layering construction from the matching all-dimension theorem. The comparison explicitly limits claims concerning unpublished Bollobás–Leader work. This revision changes no theorem, lemma, proposition, corollary, conjecture or proof environment, and no Lean source. The PDF compiles with no overfull boxes or undefined references.

## Author attribution revision, 19 October 2026

The author identifies GPT-6 Astra through Codex as the primary AI tool, with additional assistance from Anthropic Claude. The current disclosure reflects that attribution. This editorial change alters no mathematical statement or Lean source.
