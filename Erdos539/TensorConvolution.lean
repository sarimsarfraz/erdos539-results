/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarConvolution
import Erdos539.DownsetCells

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]

def boxVolume (a : ι → ℕ) : ℕ := ∏ i, (a i + 1)

def tensorConvolutionWeight (z a : ι → ℕ) : ℝ :=
  ∏ i, scalarConvolutionWeight (z i) (a i)

theorem tensorConvolutionWeight_nonneg (z a : ι → ℕ) :
    0 ≤ tensorConvolutionWeight z a :=
  Finset.prod_nonneg (fun _ _ ↦ scalarConvolutionWeight_nonneg _ _)

theorem tensorConvolutionWeight_eq (z a : ι → ℕ) :
    tensorConvolutionWeight z a =
      1 / Real.sqrt ((boxVolume a : ℝ) * (boxVolume (z - a) : ℝ)) := by
  unfold tensorConvolutionWeight scalarConvolutionWeight boxVolume
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const_one]
  congr 1
  rw [← Real.sqrt_prod _ (fun _ _ ↦ by positivity), Finset.prod_mul_distrib]
  rfl

theorem tensorConvolution_sum_le (z : ι → ℕ) :
    ∑ a ∈ Fintype.piFinset (fun i ↦ Finset.range (z i + 1)), tensorConvolutionWeight z a ≤
      (4 : ℝ) ^ (activeCoordinates z).card := by
  unfold tensorConvolutionWeight
  rw [← Finset.prod_univ_sum]
  calc
    _ ≤ ∏ i, if 0 < z i then (4 : ℝ) else 1 := by
      apply Finset.prod_le_prod
      · intro i _
        exact Finset.sum_nonneg (fun x _ ↦ scalarConvolutionWeight_nonneg _ _)
      · intro i _
        by_cases hi : 0 < z i
        · simpa only [if_pos hi] using scalarConvolution_sum_le_four (z i)
        · simp [show z i = 0 by omega, scalarConvolutionWeight]
    _ = _ := by rw [Finset.prod_ite]; simp [activeCoordinates]

def sumRepresentatives (E : Finset (ι → ℕ)) (z : ι → ℕ) : Finset (ι → ℕ) :=
  E.filter (fun a ↦ a ≤ z ∧ z - a ∈ E)

theorem sumRepresentatives_subset_box (E : Finset (ι → ℕ)) (z : ι → ℕ) :
    sumRepresentatives E z ⊆ Fintype.piFinset (fun i ↦ Finset.range (z i + 1)) := by
  intro a ha
  apply Fintype.mem_piFinset.mpr
  intro i
  have h := (Finset.mem_filter.mp ha).2.1 i
  exact Finset.mem_range.mpr (by change a i ≤ z i at h; omega)

/-- Each representation contributes at least one after weighting by the
largest contained-box volume. No downward-closure hypothesis is needed. -/
theorem one_le_volume_mul_weight {E : Finset (ι → ℕ)} {M : ℝ}
    (hM : ∀ a ∈ E, (boxVolume a : ℝ) ≤ M) {z a : ι → ℕ}
    (ha : a ∈ sumRepresentatives E z) : 1 ≤ M * tensorConvolutionWeight z a := by
  obtain ⟨ha, _haz, hb⟩ := Finset.mem_filter.mp ha
  have hapos : (0 : ℝ) < boxVolume a := by
    unfold boxVolume
    exact_mod_cast Finset.prod_pos (fun i _ ↦ Nat.succ_pos (a i))
  have hbpos : (0 : ℝ) < boxVolume (z - a) := by
    unfold boxVolume
    exact_mod_cast Finset.prod_pos (fun i _ ↦ Nat.succ_pos ((z - a) i))
  have hMa := hM a ha
  have hMb := hM (z - a) hb
  have hMpos : 0 < M := hapos.trans_le hMa
  have hprod : (boxVolume a : ℝ) * boxVolume (z - a) ≤ M ^ 2 := by
    nlinarith [mul_le_mul hMa hMb hbpos.le hMpos.le]
  have hs : Real.sqrt ((boxVolume a : ℝ) * boxVolume (z - a)) ≤ M :=
    (Real.sqrt_le_iff).mpr ⟨hMpos.le, hprod⟩
  rw [tensorConvolutionWeight_eq, ← div_eq_mul_one_div]
  exact (le_div_iff₀ (Real.sqrt_pos.mpr (mul_pos hapos hbpos))).mpr (by simpa using hs)

theorem sumRepresentatives_card_le {E : Finset (ι → ℕ)} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ a ∈ E, (boxVolume a : ℝ) ≤ M) (z : ι → ℕ) :
    ((sumRepresentatives E z).card : ℝ) ≤ M * 4 ^ (activeCoordinates z).card := by
  calc
    _ = ∑ _a ∈ sumRepresentatives E z, (1 : ℝ) := by simp
    _ ≤ ∑ a ∈ sumRepresentatives E z, M * tensorConvolutionWeight z a :=
      Finset.sum_le_sum (fun _ ha ↦ one_le_volume_mul_weight hM ha)
    _ = M * ∑ a ∈ sumRepresentatives E z, tensorConvolutionWeight z a :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ M * ∑ a ∈ Fintype.piFinset (fun i ↦ Finset.range (z i + 1)), tensorConvolutionWeight z a := by
      apply mul_le_mul_of_nonneg_left _ hM0
      exact Finset.sum_le_sum_of_subset_of_nonneg (sumRepresentatives_subset_box E z)
        (fun a _ _ ↦ tensorConvolutionWeight_nonneg z a)
    _ ≤ _ := mul_le_mul_of_nonneg_left (tensorConvolution_sum_le z) hM0

end
end Erdos539Geometry
