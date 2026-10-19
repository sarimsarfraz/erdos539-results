/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinateShearer

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*}
local instance maskedCoordinateShearerDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance maskedCoordinateShearerIndexDecidableEq (I : Finset ι) : DecidableEq I := Classical.decEq _
local instance maskedCoordinateShearerProjectionDecidableEq
    (S : Finset (ι → ℝ)) (I : Finset ι) : DecidableEq (projection S I) := Classical.decEq _

/-- Fractional entropy covering on a retained mask, in the original
ambient labels. Unused ambient coordinates need not be covered. -/
theorem coordinate_fractional_entropy_cover_on_mask {κ : Type*} [Fintype κ]
    (S : Finset (ι → ℝ)) (ν : S → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (J : Finset ι) (A : κ → Finset ι) (hA : ∀ k, A k ⊆ J)
    (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hcover : ∀ i ∈ J, 1 ≤ ∑ k, if i ∈ A k then c k else 0) :
    coordinateProjectionEntropy S ν J ≤ ∑ k, c k * coordinateProjectionEntropy S ν (A k) := by
  have h := finite_fractional_cover (coordinateProjectionEntropy S ν)
    (coordinateProjectionEntropy_empty S ν hν hs)
    (fun _ _ hIJ ↦ coordinateProjectionEntropy_mono S ν hν hIJ)
    (fun {I J} hIJ i _ ↦ coordinateProjectionEntropy_increment_antitone S ν hν hIJ i)
    A c hc J hcover
  simpa only [Finset.inter_eq_left.mpr (hA _)] using h

/-- Codimension-one Shearer on an arbitrary retained coordinate mask,
with all projected laws still coming from the original law. -/
theorem coordinate_mask_codimension_entropy_cover (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) (J : Finset ι) (hd : 2 ≤ J.card) :
    ((J.card : ℝ) - 1) * coordinateProjectionEntropy S ν J ≤
      ∑ i : J, coordinateProjectionEntropy S ν (J.erase i.val) := by
  have hdreal : (2 : ℝ) ≤ J.card := by exact_mod_cast hd
  have hpos : 0 < (J.card : ℝ) - 1 := by linarith
  let c : ℝ := 1 / ((J.card : ℝ) - 1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcover (i : ι) (hi : i ∈ J) : 1 ≤ ∑ k : J, if i ∈ J.erase k.val then c else 0 := by
    let j : J := ⟨i, hi⟩
    have he : (∑ k : J, if i ∈ J.erase k.val then c else 0) =
        ∑ k ∈ Finset.univ.erase j, c := by
      have hset : Finset.univ.erase j =
          Finset.univ.filter (fun k : J ↦ i ∈ J.erase k.val) := by
        ext k
        simp [j, hi, Subtype.ext_iff, eq_comm]
      conv_rhs => rw [hset, Finset.sum_filter]
    rw [he]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_coe, Nat.cast_sub (show 1 ≤ J.card by omega), Nat.cast_one]
    dsimp [c]
    rw [mul_one_div_cancel hpos.ne']
  have h := coordinate_fractional_entropy_cover_on_mask S ν hν hs J
    (fun i : J ↦ J.erase i.val) (fun i ↦ Finset.erase_subset i.val J)
    (fun _ ↦ c) (fun _ ↦ hc) hcover
  rw [← Finset.mul_sum] at h
  have hm := mul_le_mul_of_nonneg_left h hpos.le
  dsimp [c] at hm
  simpa only [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul] using hm

end
end Erdos539Geometry
