# Paper-to-Lean correspondence

This map accompanies `paper/main.tex`. Names without a namespace are in `Erdos539Geometry`. Statements must be read with their actual hypotheses; the source files are authoritative.

| Paper result | Source / endpoint | Scope |
| --- | --- | --- |
| Unrestricted lower bound | `SuperSqrt.lean`: `Erdos539.cofactorThreshold_super_sqrt_explicit`; `PositiveMinimum.lean`: `positiveCofactorMinimum_super_sqrt_explicit` | Eventual, c = 1/16000, no unproved cut/core hypothesis; positive and zero-inclusive minima are separate |
| Sharp fixed-dimensional orders | `AllDimensionBounds.lean`: `fixedDimensionalMinimum_all_dimension_isTheta`, `primeSupportedMinimum_all_dimension_isTheta` | Every d > 0; both bounds; arbitrary d distinct primes |
| Real fan bound | `CornerFanBound.lean`: `all_dimension_fan_lower_bound` | Actual forward fan, constant 2^(-2^(d+1)), finite nonempty sets |
| Exponents and construction | `SharpExponents.lean`, `SharpPowerTwo.lean`, `SharpUpperConstruction.lean` | Exact rational recursion, power-of-two values, actual integer examples for every n > 0 |
| Exact gluing | `GluingExactDifferences.lean`, `GluingExactPositive.lean` | Both cardinality identities under separation M > 2L |
| Two-corner selection | `SharpCornerSelection.lean`: `exists_large_corner_slice_sharp` | Actual corners; coordinate ties included |
| Fiber regularity | `SharpRegularityBounds.lean`: `sharp_regularity_fan_lower_bound` | Positive dimension, actual fan, irregularity cost explicit |
| Uniform dimension bound | `SharpUniformCorollary.lean`: `explicit_uniform_difference_bound` | Gain of order 1/(d log d) |
| Original-coordinate extraction | `ElementaryExtraction.lean`: `exists_prefixUniform_extraction`; `PrefixUniform.lean` | Actual subset of size at least N/(1024 K^10), injectivity on at most ceil(log2(2 K^2)) original coordinates |
| Structured sets | `MidpointBound.lean`, `ConvexLattice.lean`, `LayerConstructible.lean` | The specified midpoint/convex-lattice/ordered-layer hypotheses are essential |
| Constants through dimension 15 | `SmallSevenBounds.lean`, `SmallFifteenBounds.lean` | Two-sided fan through 7; positive differences through 15; constant 8^(-d) |
| Weighted optimizer and critical core | `EnergyMaximizer.lean`, `CriticalCoreTheorem.lean` | Actual norm/optimizer and projected-subset selection |
| Stronger-bound implication | `QuadraticCoreThreshold.lean`: `Erdos539.cofactorThreshold_strong_bound_of_quadratic_core` | Conditional on the explicit universal quadratic-core hypothesis |
| Four-mask compatible cuts | `SmallFourCoverCut.lean`: `IsProjectionCriticalCore.small_four_cover_compatible_cut` | Requires a proper exposed cover of weight at most two with at most four masks |
| Completion, exchange and lifted-cover criterion | Written proofs in the manuscript | Outside the completed Lean receipt; universal cover existence remains open |

The release correspondence review corrected the arithmetic dictionary to require positive integers, made positive dimension explicit where needed, and explained translation of exchange competitors. These are exposition corrections; no new unconditional bound follows from them.

Formal verification checks the encoded propositions and their proofs. This mapping and the manuscript prose require mathematical review independently of the kernel check. The full unrestricted problem remains open.
