/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FixedDimension
import Erdos539.PrimeDecoding

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

/-- The cofactor minimum over n positive integers supported on the specified
list of distinct primes. The embedding records distinctness. -/
def primeSupportedMinimum {d : ℕ} (p : Fin d ↪ ℕ) (n : ℕ) : ℕ :=
  sInf {q : ℕ | ∃ A : Finset ℕ, A.card = n ∧
    (∀ a ∈ A, SupportedOnPrimes p a) ∧ (cofactors A).card = q}

/-- The integer-vector and fixed-prime formulations have the same attainable
cofactor counts, including n = 0 and dimension zero. -/
theorem primeSupportedMinimum_eq_fixedDimensionalMinimum {d n : ℕ}
    (p : Fin d ↪ ℕ) (hp : ∀ i, (p i).Prime) :
    primeSupportedMinimum p n = fixedDimensionalMinimum d n := by
  unfold primeSupportedMinimum fixedDimensionalMinimum
  congr 1
  ext q
  constructor
  · rintro ⟨A, hA, hsupport, hq⟩
    obtain ⟨F, hF, hD⟩ := exists_integer_model_on_primes p hp hsupport
    exact ⟨F, hF.trans hA, hD.trans hq⟩
  · rintro ⟨F, hF, hq⟩
    obtain ⟨A, hA, hD, hsupport⟩ := exists_prime_realization p hp F
    exact ⟨A, hA.trans hF, hsupport, hD.trans hq⟩

/-- Explicit matching bounds for integers supported on any three fixed
pairwise distinct primes. -/
theorem primeSupportedMinimum_three_bounds (p : Fin 3 ↪ ℕ) (hp : ∀ i, (p i).Prime)
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (5 / 8 : ℝ) / 16 ≤ primeSupportedMinimum p n ∧
      (primeSupportedMinimum p n : ℝ) ≤ 480 * (n : ℝ) ^ (5 / 8 : ℝ) := by
  rw [primeSupportedMinimum_eq_fixedDimensionalMinimum p hp]
  exact fixedDimensionalMinimum_three_bounds hn

/-- The sharp Theta theorem, in the arithmetic fixed-prime formulation. -/
theorem primeSupportedMinimum_three_isTheta (p : Fin 3 ↪ ℕ) (hp : ∀ i, (p i).Prime) :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ ↦ (primeSupportedMinimum p n : ℝ))
      (fun n : ℕ ↦ (n : ℝ) ^ (5 / 8 : ℝ)) := by
  simpa only [primeSupportedMinimum_eq_fixedDimensionalMinimum p hp] using
    fixedDimensionalMinimum_three_isTheta

end
end Erdos539Geometry
