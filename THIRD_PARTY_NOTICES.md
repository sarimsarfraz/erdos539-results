# Third-party sources

* **Kenta Kitamura**, `KitaKen1/erdos-539-sqrt-disproof`, commit
  `78e0a02a462321e110c182b58e48dbbb8280ad4b`, Apache-2.0.
  Original source snapshots and hashes are in `vendor-sources/kitamura-sqrt/`.
  `Erdos539/Factorization.lean` and `Erdos539/PositiveDiff.lean` adapt imports;
  `Erdos539/Dimension.lean` ports the coordinate-selection proof and strengthens
  its final theorem with an ordinary-difference cardinality bound;
  `Erdos539/Threshold.lean` adapts the finite minimum and positive-subset lemmas.
  The original license is retained in `LICENSES/Kitamura-Apache-2.0.txt`.
* **The Formal Conjectures Authors**, Apache-2.0: the definitions
  `Erdos539.IsCofactorLowerBound` and `Erdos539.cofactorThreshold` are retained
  verbatim from `FormalConjectures/ErdosProblems/539.lean`.
  We do not import or reuse any upstream conjecture proof placeholder.
* **Mathlib contributors**, Apache-2.0: pinned source and compiled cache are
  external dependencies. Their notices and license stay with the dependency.
* **PFR contributors**, `teorth/pfr`, commit
  `346ef5b0609538f3fb49dc36c8adc52a0b2db4bb`, Apache-2.0:
  the 49-file transitive source closure of `PFR.WeakPFR` is in `PFR/`.
  Original source hashes are in `vendor-sources/pfr/SOURCE.json`; license in
  `LICENSES/PFR-Apache-2.0.txt`. `compatibility.patch` removes only the four
  measure default-argument annotations in `PFR/WeakPFR.lean`, following the
  upstream fix described in commit `650910e5fdeda1374faea9850e30f8dbcd02ff49`.
  This prevents generated syntax holes; `weak_PFR_int` retains its statement.

Downloaded source candidates are not marked verified until compiled and audited.

## Mathematical sources for original formal proofs

`OrthantTrimming.lean`, `OrthantExpansion.lean`, and `OrthantAnchor.lean`
formalize the argument of Holzman, Lev and Pinchasi, Lemma 2.2,
[Projecting Difference Sets on the Positive Orthant (2008)](https://holzman.net.technion.ac.il/files/2012/09/project.pdf).
These are newly written Lean proofs; no third-party Lean source was copied
for this lemma. The original paper was consulted for the mathematical argument.
