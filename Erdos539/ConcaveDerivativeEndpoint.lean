/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Linarith

namespace Erdos539Geometry
noncomputable section

/-- If the derivative has the sign of a concave function minus its right
endpoint value, the original function attains its maximum at an endpoint.
This avoids numerical localization of any interior critical point. -/
theorem le_max_endpoints_of_concave_derivative_sign {f g w : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (hg : ConcaveOn ℝ (Set.Icc 0 1) g)
    (hg1 : g 1 = 1)
    (hf' : ∀ x ∈ Set.Ioo 0 1, HasDerivAt f (w x * (g x - 1)) x)
    (hw : ∀ x ∈ Set.Ioo 0 1, 0 ≤ w x)
    {x : ℝ} (hx : x ∈ Set.Icc 0 1) : f x ≤ max (f 0) (f 1) := by
  rcases hx.1.eq_or_lt with he | hx0
  · rw [← he]; exact le_max_left _ _
  rcases hx.2.eq_or_lt with he | hx1
  · rw [he]; exact le_max_right _ _
  by_cases hgx : g x ≤ 1
  · have hanti : AntitoneOn f (Set.Icc 0 x) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 x)
        (hf.mono (Set.Icc_subset_Icc le_rfl hx.2))
      · intro y hy
        rw [interior_Icc] at hy
        exact (hf' y ⟨hy.1, hy.2.trans hx1⟩).hasDerivWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        have hgy := hg.left_le_of_le_right'' ⟨hy.1.le, (hy.2.trans hx1).le⟩
          (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) hy.2.le hx1 (by simpa only [hg1] using hgx)
        exact mul_nonpos_of_nonneg_of_nonpos (hw y ⟨hy.1, hy.2.trans hx1⟩)
          (sub_nonpos.mpr (hgy.trans hgx))
    exact (hanti ⟨le_rfl, hx0.le⟩ ⟨hx0.le, le_rfl⟩ hx0.le).trans (le_max_left _ _)
  · have hmono : MonotoneOn f (Set.Icc x 1) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x 1)
        (hf.mono (Set.Icc_subset_Icc hx.1 le_rfl))
      · intro y hy
        rw [interior_Icc] at hy
        exact (hf' y ⟨hx0.trans hy.1, hy.2⟩).hasDerivWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        have hgy := hg.min_le_of_mem_Icc hx (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
          ⟨hy.1.le, hy.2.le⟩
        rw [hg1, min_eq_right (le_of_not_ge hgx)] at hgy
        exact mul_nonneg (hw y ⟨hx0.trans hy.1, hy.2⟩) (sub_nonneg.mpr hgy)
    exact (hmono ⟨le_rfl, hx1.le⟩ ⟨hx1.le, le_rfl⟩ hx1.le).trans (le_max_right _ _)

end
end Erdos539Geometry
