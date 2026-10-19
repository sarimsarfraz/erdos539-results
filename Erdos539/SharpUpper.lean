/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpUpperConstruction
import Erdos539.PrimeSupportedMinimum

namespace Erdos539Geometry
noncomputable section

/-- The all-fixed-dimensional sharp upper bound in the arithmetic formulation. -/
theorem primeSupportedMinimum_sharp_upper {d : ℕ} (hd : 0 < d)
    (p : Fin d ↪ ℕ) (hp : ∀ i, (p i).Prime) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (primeSupportedMinimum p n : ℝ) ≤ C * (n : ℝ) ^ (sharpExponent d : ℝ) := by
  simpa only [primeSupportedMinimum_eq_fixedDimensionalMinimum p hp] using
    fixedDimensionalMinimum_sharp_upper hd

end
end Erdos539Geometry
