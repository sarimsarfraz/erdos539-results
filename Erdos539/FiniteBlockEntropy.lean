/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinateEntropySubmodular

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- Diminishing one-coordinate increments imply diminishing block increments. -/
theorem finite_union_increment_antitone {ι : Type*} (H : Finset ι → ℝ)
    (hinc : ∀ {I J : Finset ι}, I ⊆ J → ∀ i,
      H (insert i J) - H J ≤ H (insert i I) - H I)
    {I J : Finset ι} (hIJ : I ⊆ J) (W : Finset ι) :
    H (J ∪ W) - H J ≤ H (I ∪ W) - H I := by
  induction W using Finset.induction_on with
  | empty => simp
  | @insert i W _hi ih =>
    have hsub : I ∪ W ⊆ J ∪ W := Finset.union_subset_union hIJ (Finset.Subset.refl W)
    have h := hinc hsub i
    simp only [Finset.union_insert] at *
    linarith

theorem finite_submodular_of_increments {ι : Type*} (H : Finset ι → ℝ)
    (hinc : ∀ {I J : Finset ι}, I ⊆ J → ∀ i,
      H (insert i J) - H J ≤ H (insert i I) - H I) (I J : Finset ι) :
    H (I ∪ J) + H (I ∩ J) ≤ H I + H J := by
  have h := finite_union_increment_antitone H hinc (Finset.inter_subset_left : I ∩ J ⊆ I) J
  rw [Finset.union_eq_right.mpr Finset.inter_subset_right] at h
  linarith

/-- Conditional mutual information expressed through actual coordinate masks. -/
def maskCMI {ι : Type*} (H : Finset ι → ℝ) (A B C : Finset ι) : ℝ :=
  H (A ∪ C) + H (B ∪ C) - H C - H (A ∪ B ∪ C)

theorem maskCMI_nonneg {ι : Type*} (H : Finset ι → ℝ) (hmono : Monotone H)
    (hinc : ∀ {I J : Finset ι}, I ⊆ J → ∀ i,
      H (insert i J) - H J ≤ H (insert i I) - H I) (A B C : Finset ι) :
    0 ≤ maskCMI H A B C := by
  have hs := finite_submodular_of_increments H hinc (A ∪ C) (B ∪ C)
  have hc := hmono (show C ⊆ (A ∪ C) ∩ (B ∪ C) from
    Finset.subset_inter Finset.subset_union_right Finset.subset_union_right)
  have he : (A ∪ C) ∪ (B ∪ C) = A ∪ B ∪ C := by
    ext i
    simp only [Finset.mem_union]
    tauto
  rw [he] at hs
  unfold maskCMI
  linarith

theorem coordinate_maskCMI_nonneg {ι : Type*} (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (A B C : Finset ι) :
    0 ≤ maskCMI (coordinateProjectionEntropy S ν) A B C :=
  maskCMI_nonneg _ (fun _ _ h ↦ coordinateProjectionEntropy_mono S ν hν h)
    (fun {_ _} h i ↦ coordinateProjectionEntropy_increment_antitone S ν hν h i) A B C

end
end Erdos539Geometry
