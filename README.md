# Gcd quotients and positive differences — Lean formalization

Lean 4 proofs accompanying **Gcd quotients: a quantitative lower bound and sharp fixed-dimensional orders**, by Sarim Sarfraz and Wali Ahmed.

This development establishes an improved quantitative lower bound for Erdős problem 539 and the sharp order of the corresponding minimum for every fixed prime support. **The unrestricted order remains open.**

This is the private release candidate. Public publication, Zenodo records, and upstream pull requests await author approval.

## Main results

For an n-element set A of positive integers, let

$$
Q(A)=\{a/\gcd(a,b):a,b\in A\},\qquad h(n)=\min_{|A|=n}|Q(A)|.
$$

The principal results are:

1. **Unrestricted lower bound.** For all sufficiently large n,
   $$
   h(n)\ge\sqrt n\exp\!\left(\frac1{16000}\sqrt{\frac{\log n}{\log\log n}}\right).
   $$
   The same eventual bound is proved for the exact, zero-inclusive `Erdos539.cofactorThreshold` definition used by Formal Conjectures. These two arithmetic functions are compared by proved lemmas; they are not identified.
2. **Sharp order for every fixed prime support.** For every d > 0 and any d fixed distinct primes,
   $$
   h_d(n)=\Theta_d(n^{u_d}),\qquad
   u_1=1,\quad u_d=\min_{p+s=d\atop p,s\ge1}\frac{u_p+u_s}{1+u_p+u_s}.
   $$
   Both bounds are proved, including a Mathlib `IsTheta` statement. In particular, the exponents in dimensions three and four are 5/8 and 4/7.
3. **Geometric and structural estimates.** The development includes positive-difference and anchored-fan bounds for real point sets, elementary extraction onto original coordinates, fiber-regularity estimates, sharp constructions, and estimates for midpoint-closed sets and ordered layers.

The unrestricted proof uses elementary extraction. Its 38-module local import closure contains no PFR imports. The larger library retains a historical PFR route and supporting energy and entropy results.

## Read the paper and proofs

- [Paper PDF — 17 pages](paper/main.pdf)
- [Manuscript source](paper/main.tex)
- [Paper-to-theorem correspondence](docs/PAPER_THEOREMS.md)
- [Release verification and scope](docs/RELEASE_AUDIT.md)
- [Third-party provenance](THIRD_PARTY_NOTICES.md)

| Result | Principal source | Endpoint |
| --- | --- | --- |
| Exact upstream threshold bound | [SuperSqrt.lean](Erdos539/SuperSqrt.lean) | `Erdos539.cofactorThreshold_super_sqrt_explicit` |
| Positive-integer minimum bound | [PositiveMinimum.lean](Erdos539/PositiveMinimum.lean) | `Erdos539Geometry.positiveCofactorMinimum_super_sqrt_explicit` |
| All fixed dimensions | [AllDimensionBounds.lean](Erdos539/AllDimensionBounds.lean) | `fixedDimensionalMinimum_all_dimension_isTheta`, `primeSupportedMinimum_all_dimension_isTheta` |
| Universal real fan bound | [CornerFanBound.lean](Erdos539/CornerFanBound.lean) | `all_dimension_fan_lower_bound` |
| Fiber regularity | [SharpRegularityBounds.lean](Erdos539/SharpRegularityBounds.lean) | `sharp_regularity_fan_lower_bound` |
| Original-coordinate extraction | [ElementaryExtraction.lean](Erdos539/ElementaryExtraction.lean) | `exists_prefixUniform_extraction` |
| Conditional stronger bound | [QuadraticCoreThreshold.lean](Erdos539/QuadraticCoreThreshold.lean) | `Erdos539.cofactorThreshold_strong_bound_of_quadratic_core` |

Unqualified endpoint names in the table belong to `Erdos539Geometry`.

## Verification

The environment is pinned:

- Lean: `leanprover/lean4:v4.29.0-rc8`
- Mathlib: `698d2b68b870f1712040ab0c233d34372d4b56df`
- Other dependencies: [lake-manifest.json](lake-manifest.json)

The clean source audit of 14–15 October, revalidated on 19 October 2026, covers **844 canonical local and vendored modules and 12,917 project declarations**. Declarations include definitions and generated declarations; this is not a theorem count. The audit allows only `propext`, `Classical.choice`, and `Quot.sound` in the transitive axiom closure. See [the current release audit](docs/RELEASE_AUDIT.md) for the clean-build evidence, source refactor and remaining publication checks. The five Lean files in [the upstream reference snapshots](vendor-sources/README.md) are retained for attribution and are outside the compiled import closure.

With the pinned toolchain installed and dependency caches available, run:

```sh
LEAN_MAX_MEMORY_MB=4096 python3 scripts/check.py
```

The checker compiles project and vendored proofs serially with synchronous elaboration, treats warnings as errors, checks exact upstream threshold definitions, verifies the elementary import boundary, and runs the transitive axiom audit. It never compiles Mathlib from source. The default Lean memory limit is 4 GB; the command above states that ceiling explicitly. A 2 GB ceiling is insufficient for this proof environment. `LEAN_MAX_MEMORY_MB` must be positive. A memory-limit failure is a failed check, not a successful audit.

An incremental run reuses only artifacts whose recorded source, dependency and compiled-file hashes match. For a clean project build, use a fresh source extraction with an empty local `.lake/build`; dependency caches can still be reused. The [reproduction guide](docs/REPRODUCING.md) gives the full procedure and distinguishes project proof compilation from dependency-cache reuse.

### Repository integrity check

```sh
python3 scripts/verify-release.py
```

The GitHub Actions workflow checks file hashes, proof-source correspondence to the checked receipt, paper metadata, and reproduction of the finite certificates. It does not rerun Lean. The separate serial command above performs the full Lean audit. See [repository verification](docs/REPOSITORY_VERIFICATION.md).

## Scope and open questions

The conjectural unrestricted scale

$$
h(n)=\sqrt n\exp(\Theta(\sqrt{\log n}))
$$

is not proved here. Universal compatible-cut and quadratic-core bounds remain explicit hypotheses in the conditional theorems. Verified small-cover cases and counterexamples to intermediate proof strategies do not resolve this gap.

The manuscript's completion and exchange propositions have written proofs but are outside the completed Lean proof closure. Experimental five-mask work is excluded from the release candidate. Historical research notes are not a substitute for the theorem statements or verification receipt.

## Citation and attribution

Use [CITATION.cff](CITATION.cff) for software attribution. The paper and software have distinct citation metadata; permanent publication identifiers will be added when the approved versions are released.

The work builds on mathematical and formal contributions by Granville and Roesler, Holzman, Lev and Pinchasi, Schmitt and collaborators, Pham, Kitamura, Mathlib contributors, and the PFR project. Source adaptations and retained licenses are documented in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

OpenAI GPT-6 Astra, used through Codex, was the primary AI tool for the research, Lean development, and exposition; Anthropic Claude provided additional assistance. The authors are responsible for the mathematical claims and presentation. Formal checking establishes the encoded propositions; it does not establish novelty or replace independent review of the exposition.

## License

The Lean source and verification scripts are distributed under [Apache-2.0](LICENSE), subject to the retained third-party notices. The manuscript source and PDF are licensed under [CC BY 4.0](paper/LICENSE.md), as approved by the authors.
