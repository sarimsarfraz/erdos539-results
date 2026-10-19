/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteBlockCover

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι κ : Type*} [Fintype κ]

/-- The general block inequality: the union of all U and V blocks plus
(k-2) times the V entropy is bounded by the k opposite-block observations. -/
theorem general_block_entropy_inequality (H : Finset ι → ℝ)
    (h0 : H ∅ = 0) (hmono : Monotone H)
    (hinc : ∀ {I J : Finset ι}, I ⊆ J → ∀ i,
      H (insert i J) - H J ≤ H (insert i I) - H I)
    (U V : κ → Finset ι) (hk : 2 ≤ Fintype.card κ) :
    H (blockUnion U ∪ blockUnion V) + ((Fintype.card κ : ℝ) - 2) * H (blockUnion V) ≤
      ∑ i, H (U i ∪ blockOthers V i) := by
  have hhan := block_Han H h0 hmono hinc V hk
  have hsub := block_conditional_subadditivity H hinc U (blockUnion V) Finset.univ
  have hpoint (i : κ) :
      H (blockUnion V ∪ U i) - H (blockUnion V) ≤
        H (blockOthers V i ∪ U i) - H (blockOthers V i) :=
    finite_union_increment_antitone H hinc
      (Finset.biUnion_subset_biUnion_of_subset_left V (Finset.erase_subset i Finset.univ)) (U i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hpoint i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.union_comm] at hsum
  change H (blockUnion V ∪ blockUnion U) - H (blockUnion V) ≤ _ at hsub
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.union_comm] at hsub
  nlinarith

theorem general_block_complement_bound (H : Finset ι → ℝ)
    (h0 : H ∅ = 0) (hmono : Monotone H)
    (hinc : ∀ {I J : Finset ι}, I ⊆ J → ∀ i,
      H (insert i J) - H J ≤ H (insert i I) - H I)
    (U V : κ → Finset ι) (hk : 3 ≤ Fintype.card κ)
    (h : ℝ) (hb : ∀ i, H (U i ∪ blockOthers V i) ≤ h) :
    H (blockUnion V) ≤ h + (2 * h - H (blockUnion U ∪ blockUnion V)) /
      ((Fintype.card κ : ℝ) - 2) := by
  have hmain := general_block_entropy_inequality H h0 hmono hinc U V (by omega)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hb i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hkreal : (3 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hk
  have hpos : 0 < (Fintype.card κ : ℝ) - 2 := by linarith
  apply (sub_le_iff_le_add').mp
  apply (le_div_iff₀ hpos).mpr
  nlinarith

def oppositeBlockFractionalGap (H : Finset ι → ℝ) (U V : κ → Finset ι) : ℝ :=
  ((Fintype.card κ : ℝ) - 2) / ((Fintype.card κ : ℝ) - 1) * H (blockUnion U) +
    (1 / ((Fintype.card κ : ℝ) - 1)) * (∑ i, H (U i ∪ blockOthers V i)) -
      H (blockUnion U ∪ blockUnion V)

theorem general_block_mutual_information_bound (H : Finset ι → ℝ)
    (h0 : H ∅ = 0) (hmono : Monotone H)
    (hinc : ∀ {I J : Finset ι}, I ⊆ J → ∀ i,
      H (insert i J) - H J ≤ H (insert i I) - H I)
    (U V : κ → Finset ι) (hk : 3 ≤ Fintype.card κ) :
    H (blockUnion U) + H (blockUnion V) - H (blockUnion U ∪ blockUnion V) ≤
      ((Fintype.card κ : ℝ) - 1) / ((Fintype.card κ : ℝ) - 2) *
        oppositeBlockFractionalGap H U V := by
  have hmain := general_block_entropy_inequality H h0 hmono hinc U V (by omega)
  have hkreal : (3 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hk
  have hpos : 0 < (Fintype.card κ : ℝ) - 2 := by linarith
  have hne : (Fintype.card κ : ℝ) - 1 ≠ 0 := by linarith
  have he : ((Fintype.card κ : ℝ) - 1) / ((Fintype.card κ : ℝ) - 2) *
      oppositeBlockFractionalGap H U V =
      (((Fintype.card κ : ℝ) - 2) * H (blockUnion U) +
        (∑ i, H (U i ∪ blockOthers V i)) -
        ((Fintype.card κ : ℝ) - 1) * H (blockUnion U ∪ blockUnion V)) /
          ((Fintype.card κ : ℝ) - 2) := by
    unfold oppositeBlockFractionalGap
    field_simp [hne, hpos.ne']
  rw [he]
  apply (le_div_iff₀ hpos).mpr
  nlinarith

/-- All observations come from one actual nonnegative probability law. -/
theorem coordinate_general_block_entropy (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1)
    (U V : κ → Finset ι) (hk : 2 ≤ Fintype.card κ) :
    coordinateProjectionEntropy S ν (blockUnion U ∪ blockUnion V) +
      ((Fintype.card κ : ℝ) - 2) * coordinateProjectionEntropy S ν (blockUnion V) ≤
      ∑ i, coordinateProjectionEntropy S ν (U i ∪ blockOthers V i) :=
  general_block_entropy_inequality _ (coordinateProjectionEntropy_empty S ν hν hs)
    (fun _ _ h ↦ coordinateProjectionEntropy_mono S ν hν h)
    (fun {_ _} h i ↦ coordinateProjectionEntropy_increment_antitone S ν hν h i) U V hk

end
end Erdos539Geometry
