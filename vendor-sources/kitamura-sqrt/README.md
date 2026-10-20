# A Lean disproof of the square-root variants in Erdős Problem 539

> **Local reference copy.** The text below is Kenta Kitamura's [upstream README](https://github.com/KitaKen1/erdos-539-sqrt-disproof/blob/78e0a02a462321e110c182b58e48dbbb8280ad4b/README.md) at revision `78e0a02a462321e110c182b58e48dbbb8280ad4b`. It describes the upstream project; this directory contains only selected reference files. Local changes add this note and point source links to that pinned upstream revision. The mathematical text, author attribution and [license](LICENSE) are unchanged. Original hashes and the local adaptation are recorded in [SOURCE.json](SOURCE.json).

This repository gives negative answers to the exact declarations
`Erdos539.erdos_539.variants.isBigO_sq` and
`Erdos539.erdos_539.variants.sq` in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/27f7d5b62fb86f586a5432bf2de56f99dc9b0aa6/FormalConjectures/ErdosProblems/539.lean).
They ask whether the cofactor threshold satisfies `h(n) = O(√n)` or
`h(n) = Θ(√n)`. We prove the stronger conclusion

```text
h(n) / √n → ∞.
```

**Try it in Lean4Web:** [open the Latest editor](https://live.lean-lang.org/#project=MathlibDemo)
and paste the [standalone proof](https://github.com/KitaKen1/erdos-539-sqrt-disproof/blob/78e0a02a462321e110c182b58e48dbbb8280ad4b/lean4web/Erdos539SqrtLean4Web.lean).
Select **Latest Mathlib with Lean v4.34.0-rc2** and allow checking to reach the
end of the file.

These results settle the two square-root questions. The exact growth order
requested by Erdős Problem 539 as a whole remains undetermined.

## Formal Conjectures target

The entry point in `lean/` imports the pinned original module. In namespace
`Erdos539Sqrt`, it proves the following explicit negative-answer forms:

```lean
theorem isBigO_sq_answer_false :
    answer(False) ↔
      ((fun n ↦ (Erdos539.cofactorThreshold n : ℝ)) =O[atTop]
        fun n ↦ √n)

theorem sq_answer_false :
    answer(False) ↔
      ((fun n ↦ (Erdos539.cofactorThreshold n : ℝ)) =Θ[atTop]
        fun n ↦ √n)
```

**Neither theorem has an additional hypothesis.** The proof uses the original
zero-inclusive definition of `cofactorThreshold`. Its internal threshold is
definitionally equal to that definition, proved by `rfl`.

At the pinned revision, both targets are marked `research open` and are stated
as positive propositions. The theorems above provide their solved negative
forms, `answer(False) ↔ P`. Updating the upstream declarations would require
recording these negative answers; no upstream update is claimed here.

## Mathematical explanation (AI generated)

For a finite set `A` of positive integers, write

```text
Q(A) = { a / gcd(a,b) : a,b ∈ A },
q = |Q(A)|.
```

Prime factorization maps `A` injectively to a set `F` of integer exponent
vectors. A reduced cofactor corresponds to taking the positive part of each
coordinate difference. Thus, with

```text
D(F) = { (x − y)₊ : x,y ∈ F },
```

we have `|F| = |A|` and `|D(F)| = q`. Every ordinary difference is determined
by its positive and negative parts, so

```text
|F − F| ≤ q².
```

Fix `K > 0` and suppose `q² ≤ K|A|`. The proved weak PFR theorem supplies a
subset of `F` of size at least `K⁻¹⁷|A|` and affine rank at most
`(40 / log 2) log K`. Restriction to suitable original coordinates is injective
on that subset. It gives a real vector set `B` whose positive-difference count
does not exceed `q`.

The geometric part of the proof establishes, in every fixed dimension `d`,
constants `c_d > 0` and `a_d > 1/2` such that

```text
|D(B)| ≥ c_d |B|^a_d.
```

This uses induction on dimension, finite dependent random choice, and disjoint
counting of positive differences. Here `d`, `c_d`, and `a_d` depend only on `K`.
Consequently,

```text
c_d (K⁻¹⁷|A|)^a_d ≤ q ≤ √(K|A|).
```

Since `a_d > 1/2`, these inequalities bound `|A|` in terms of `K`. In particular,
positive integer sets satisfying `q² ≤ K|A|` cannot have arbitrarily large size.

Finally, the original threshold is an attained minimum. For `n ≥ 1`, an attaining
set of `n` natural numbers contains `n−1` positive integers. Passing to that subset
cannot increase the cofactor count. The preceding bound forces
`h(n)/√n → ∞`, which rules out both square-root claims.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| [`lean/`](https://github.com/KitaKen1/erdos-539-sqrt-disproof/tree/78e0a02a462321e110c182b58e48dbbb8280ad4b/lean) | `v4.33.1` | Modular proof importing the original Formal Conjectures target |
| [`lean4web/`](https://github.com/KitaKen1/erdos-539-sqrt-disproof/tree/78e0a02a462321e110c182b58e48dbbb8280ad4b/lean4web) | `v4.34.0-rc2` | Standalone Mathlib-only proof for the public Latest editor |
| [`vendor/pfr/`](https://github.com/KitaKen1/erdos-539-sqrt-disproof/tree/78e0a02a462321e110c182b58e48dbbb8280ad4b/vendor/pfr) | `v4.33.1` | Proved PFR source dependency used by `lean/` |

The entry points are [`Erdos539SqrtFC.lean`](https://github.com/KitaKen1/erdos-539-sqrt-disproof/blob/78e0a02a462321e110c182b58e48dbbb8280ad4b/lean/Erdos539SqrtFC.lean) and
[`Erdos539SqrtLean4Web.lean`](https://github.com/KitaKen1/erdos-539-sqrt-disproof/blob/78e0a02a462321e110c182b58e48dbbb8280ad4b/lean4web/Erdos539SqrtLean4Web.lean).
Both projects include `lakefile.toml`, `lean-toolchain`, and `lake-manifest.json`.
The `lean4web/compat/` sources record the adaptations for Mathlib 4.34; the
standalone file already includes the required PFR proofs.

## Verification

For the Formal Conjectures project:

```bash
cd lean
lake exe cache get
lake build
```

For the standalone project:

```bash
cd lean4web
lake exe cache get
lake build
```

The dependency revisions are fixed:

| Dependency | Revision |
|---|---|
| Formal Conjectures | `27f7d5b62fb86f586a5432bf2de56f99dc9b0aa6` |
| Mathlib for `lean/` | `0df444a360eaa60ab8c11dca51a86af692955474` |
| Mathlib for `lean4web/` | `c99c5c46fffb23d515368bb1d1b80ead407d8657` |

Both projects passed local `lake build` on **2026-09-05**, with **0 errors and
0 warnings**. The standalone environment matches the public Latest configuration
observed on that date. The public project can advance; the local dependency
pins preserve the checked version. Full remote-server verification is not claimed.

The FC entry point compares each entire answer type with the corresponding
imported target and checks that no extra parameters have been added. The
upstream conjecture proof terms are not used. Both entry points run
`assert_no_sorry` and axiom checks. The final declarations
`threshold_div_sqrt_tendsto`, `isBigO_sq_answer_false`, and
`sq_answer_false` in namespace `Erdos539Sqrt` report exactly

```text
[propext, Classical.choice, Quot.sound]
```

## Status boundary

The result proved here is

```text
For the original Formal Conjectures threshold h,
h(n)/√n → ∞; hence h(n) is neither O(√n) nor Θ(√n).
```

The exact asymptotic order in `Erdos539.erdos_539` remains open in this work.
The proof gives a qualitative improvement over every constant multiple of
`√n`; it does not establish the earlier proposed explicit `√(n log log n)`
or `√n (log n)^(1/480)` bounds.

The pinned FC source already marks `variants.sq_isBigO`,
`variants.sq_cube_root`, `variants.isBigO_sq_cube_root`,
`variants.sq_cube_root_isBigO`, and `variants.limit` as `research solved`.
Those are not presented as new results here. Publication, independent novelty
review, and changes to upstream status records are separate from the local
formal verification reported above.

## Sources

- [Erdős Problem 539](https://www.erdosproblems.com/539).
- [Pinned Formal Conjectures target](https://github.com/google-deepmind/formal-conjectures/blob/27f7d5b62fb86f586a5432bf2de56f99dc9b0aa6/FormalConjectures/ErdosProblems/539.lean).
- [PFR source at 7d6404b79b11b1a89dd1b6f997a10b14c208c4ed](https://github.com/teorth/pfr/tree/7d6404b79b11b1a89dd1b6f997a10b14c208c4ed).

The 49 vendored PFR files retain their original notices and license. The
[source manifest](https://github.com/KitaKen1/erdos-539-sqrt-disproof/blob/78e0a02a462321e110c182b58e48dbbb8280ad4b/vendor/pfr/SOURCE-MANIFEST.json) and
[patch](https://github.com/KitaKen1/erdos-539-sqrt-disproof/blob/78e0a02a462321e110c182b58e48dbbb8280ad4b/vendor/pfr/upstream.patch) record compatibility changes, including
removal of default-argument annotations that generated syntax holes and
resolution of names already supplied by Mathlib. The statement of
`weak_PFR_int` is unchanged.

The [4.34 compatibility patch](https://github.com/KitaKen1/erdos-539-sqrt-disproof/blob/78e0a02a462321e110c182b58e48dbbb8280ad4b/lean4web/compat/changes.patch) adapts the measure
APIs and deprecated names. Two internal finite-range helpers now require
measurability because Mathlib changed the fallback for nonmeasurable maps;
every caller supplies that proof. The final Erdős 539 statements have no added
hypotheses. This port was also compared with
[PFR at 07839bdd](https://github.com/teorth/pfr/tree/07839bddb1395c8808fa47db821ce2e4fff9362e).

The source is Apache-2.0; see [LICENSE](LICENSE) and
[vendor/pfr/LICENSE](https://github.com/KitaKen1/erdos-539-sqrt-disproof/blob/78e0a02a462321e110c182b58e48dbbb8280ad4b/vendor/pfr/LICENSE).

## AI usage disclosure

OpenAI Codex (GPT-6 Astra) assisted with the proof development, formalization, and exposition.
