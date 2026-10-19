/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinateEntropySubmodular
import Erdos539.FiniteFractionalCover

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
local instance coordinateShearerDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance coordinateShearerProjectionDecidableEq
    (S : Finset (ι → ℝ)) (I : Finset ι) : DecidableEq (projection S I) := Classical.decEq _

/-- Fractional Shearer inequality on literal coordinate projections of
one fixed law. Repeated masks, arbitrary real cover weights and zero atoms
are allowed. -/
theorem coordinate_fractional_entropy_cover (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (A : κ → Finset ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hcover : ∀ i, 1 ≤ ∑ k, if i ∈ A k then c k else 0) :
    finiteEntropy ν ≤ ∑ k, c k * coordinateProjectionEntropy S ν (A k) := by
  have h := finite_fractional_cover (coordinateProjectionEntropy S ν)
    (coordinateProjectionEntropy_empty S ν hν hs)
    (fun _ _ hIJ ↦ coordinateProjectionEntropy_mono S ν hν hIJ)
    (fun {I J} hIJ i _ ↦ coordinateProjectionEntropy_increment_antitone S ν hν hIJ i)
    A c hc Finset.univ (fun i _ ↦ hcover i)
  simpa only [coordinateProjectionEntropy_univ, Finset.inter_univ] using h

omit [Fintype κ] in
/-- The codimension-one entropy cover, with no exposed-mask hypothesis. -/
theorem coordinate_codimension_entropy_cover (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) (hd : 2 ≤ Fintype.card ι) :
    ((Fintype.card ι : ℝ) - 1) * finiteEntropy ν ≤
      ∑ i, coordinateProjectionEntropy S ν (Finset.univ.erase i) := by
  have hdreal : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
  have hpos : 0 < (Fintype.card ι : ℝ) - 1 := by linarith
  let c : ℝ := 1 / ((Fintype.card ι : ℝ) - 1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcover (i : ι) : 1 ≤ ∑ k : ι, if i ∈ Finset.univ.erase k then c else 0 := by
    have he : (∑ k : ι, if i ∈ Finset.univ.erase k then c else 0) =
        ∑ k ∈ Finset.univ.erase i, c := by
      have hset : Finset.univ.erase i =
          Finset.univ.filter (fun k : ι ↦ i ∈ Finset.univ.erase k) := by
        ext k
        simp [eq_comm]
      conv_rhs => rw [hset, Finset.sum_filter]
    rw [he]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Nat.cast_sub (show 1 ≤ Fintype.card ι by omega), Nat.cast_one]
    dsimp [c]
    rw [mul_one_div_cancel hpos.ne']
  have h := coordinate_fractional_entropy_cover S ν hν hs
    (fun i : ι ↦ Finset.univ.erase i) (fun _ ↦ c) (fun _ ↦ hc) hcover
  rw [← Finset.mul_sum] at h
  have hm := mul_le_mul_of_nonneg_left h hpos.le
  dsimp [c] at hm
  simpa only [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul] using hm

end
end Erdos539Geometry
