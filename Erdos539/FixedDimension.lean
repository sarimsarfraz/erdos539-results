/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PowerInterpolation
import Erdos539.ThreeDimensionalFans
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.Asymptotics.Defs

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

/-- The manuscript's h_d(n), defined in its integer-vector formulation.
The infimum is attained whenever an n-point set in dimension d exists. -/
def fixedDimensionalMinimum (d n : ℕ) : ℕ :=
  sInf {q : ℕ | ∃ F : Finset (Fin d → ℤ), F.card = n ∧ (integerPositiveDifferences F).card = q}

theorem fixedDimensionalMinimum_le {d n : ℕ} (F : Finset (Fin d → ℤ)) (hF : F.card = n) :
    fixedDimensionalMinimum d n ≤ (integerPositiveDifferences F).card :=
  Nat.sInf_le ⟨F, hF, rfl⟩

theorem fixedDimensionalMinimum_attained {d n : ℕ}
    (hex : ∃ F : Finset (Fin d → ℤ), F.card = n) :
    ∃ F : Finset (Fin d → ℤ), F.card = n ∧
      (integerPositiveDifferences F).card = fixedDimensionalMinimum d n := by
  have hne : {q : ℕ | ∃ F : Finset (Fin d → ℤ),
      F.card = n ∧ (integerPositiveDifferences F).card = q}.Nonempty := by
    obtain ⟨F, hF⟩ := hex
    exact ⟨(integerPositiveDifferences F).card, F, hF, rfl⟩
  exact Nat.sInf_mem hne

theorem integer_three_dimensional_lower_bound {F : Finset (Fin 3 → ℤ)} (hF : F.Nonempty) :
    (F.card : ℝ) ^ (5 / 8 : ℝ) / 16 ≤ (integerPositiveDifferences F).card := by
  letI : DecidableEq (Fin 3 → ℝ) := Classical.decEq _
  have h := three_dimensional_posDiff_lower_bound (by simp : Fintype.card (Fin 3) = 3)
    (hF.image integerToReal)
  rw [integerToReal_image_card, posDiff_integerToReal_card] at h
  exact h

/-- Both sides of the sharp three-dimensional integer-vector minimum,
with explicit constants and no asymptotic exceptional range. -/
theorem fixedDimensionalMinimum_three_bounds {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (5 / 8 : ℝ) / 16 ≤ fixedDimensionalMinimum 3 n ∧
      (fixedDimensionalMinimum 3 n : ℝ) ≤ 480 * (n : ℝ) ^ (5 / 8 : ℝ) := by
  obtain ⟨A, hA, hD⟩ := exists_three_dimensional_construction hn
  constructor
  · obtain ⟨F, hF, hq⟩ := fixedDimensionalMinimum_attained ⟨A, hA⟩
    have hFn : F.Nonempty := Finset.card_pos.mp (by omega)
    have h := integer_three_dimensional_lower_bound hFn
    rwa [hF, hq] at h
  · have hmin : (fixedDimensionalMinimum 3 n : ℝ) ≤ (integerPositiveDifferences A).card := by
      exact_mod_cast fixedDimensionalMinimum_le A hA
    exact hmin.trans hD

/-- h_3(n) = Theta(n^(5/8)) in the integer-vector formulation. -/
theorem fixedDimensionalMinimum_three_isTheta :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ ↦ (fixedDimensionalMinimum 3 n : ℝ))
      (fun n : ℕ ↦ (n : ℝ) ^ (5 / 8 : ℝ)) := by
  have he : ∀ᶠ n : ℕ in Filter.atTop, 0 < n := Filter.eventually_gt_atTop 0
  constructor
  · apply Asymptotics.IsBigO.of_bound 480
    filter_upwards [he] with n hn
    have hp : 0 ≤ (n : ℝ) ^ (5 / 8 : ℝ) := Real.rpow_nonneg (by positivity) _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp, Nat.abs_cast] using
      (fixedDimensionalMinimum_three_bounds hn).2
  · apply Asymptotics.IsBigO.of_bound 16
    filter_upwards [he] with n hn
    have hp : 0 ≤ (n : ℝ) ^ (5 / 8 : ℝ) := Real.rpow_nonneg (by positivity) _
    have h := (fixedDimensionalMinimum_three_bounds hn).1
    simp only [Real.norm_eq_abs, abs_of_nonneg hp, Nat.abs_cast]
    linarith

end
end Erdos539Geometry
