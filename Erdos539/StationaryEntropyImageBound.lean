/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ImageQuadrupleLaw
import Erdos539.StationaryEntropyFibringBound

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq H]
local instance imageEntropyBoundDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

/-- The test-function entropy-fibring inequality also holds for arbitrary
actual partitions. No additive relation is asserted for the label space. -/
theorem entropy_image_partition_bound (Q : StationaryAdditiveLaw S ν)
    (hν : ∑ x, ν x = 1) (φ : G → H) (f : S → ℝ) (hf : ∀ x, 0 < f x)
    (B : S.image φ → ℝ) (hB : ∀ y, 0 < B y)
    (hpart : ∀ y, weightedGibbsPartition (fiber S φ y.val) (imageFiberWeight S φ f y) ≤ B y) :
    Q.entropy ≤ finiteEntropy (Q.imageFlat φ) +
      (∑ y, finitePush ν (imageEndpoint S φ) y * Real.log (B y)) - 4 * ∑ x, ν x * Real.log (f x) := by
  let w := fun z : (S × S) × (S × S) ↦ additiveQuadrupleWeight S f z.1.1 z.1.2 z.2.1 z.2.2
  let C := fun z : ((S.image φ) × (S.image φ)) × ((S.image φ) × (S.image φ)) ↦
    B z.1.1 ^ (1 / 4 : ℝ) * B z.1.2 ^ (1 / 4 : ℝ) * B z.2.1 ^ (1 / 4 : ℝ) * B z.2.2 ^ (1 / 4 : ℝ)
  have hw : ∀ z, 0 ≤ w z := by
    intro z
    dsimp only [w, additiveQuadrupleWeight]
    split_ifs
    · exact mul_nonneg (mul_nonneg (hf _).le (hf _).le) (mul_nonneg (hf _).le (hf _).le)
    · rfl
  have hsup : ∀ z, Q.flat z ≠ 0 → 0 < w z := by
    intro z hz
    have he : z.1.1.val + z.1.2.val = z.2.1.val + z.2.2.val := by
      by_contra hh
      exact hz (Q.supported _ _ _ _ hh)
    simp only [w, additiveQuadrupleWeight, if_pos he]
    exact mul_pos (mul_pos (hf _) (hf _)) (mul_pos (hf _) (hf _))
  have hC : ∀ z, 0 < C z := by
    intro z
    exact mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos (hB _) _) (Real.rpow_pos_of_pos (hB _) _))
      (Real.rpow_pos_of_pos (hB _) _)) (Real.rpow_pos_of_pos (hB _) _)
  have h := finiteEntropy_fiber_partition_bound Q.flat w
    (mapFour (imageEndpoint S φ)) C (fun _ ↦ Q.nonneg _ _ _ _)
    (by simpa only [flat, Fintype.sum_prod_type] using Q.total_mass hν) hw hC hsup
    (fun _ ↦ additiveWeight_image_push_le S φ f B hB hpart _ _ _ _)
  have hparent : finiteEntropy Q.flat = Q.entropy := by
    simp only [finiteEntropy, flat, entropy, Fintype.sum_prod_type]
  have hcross : (∑ z, Q.flat z * Real.log (w z)) = 4 * ∑ x, ν x * Real.log (f x) := by
    simpa only [flat, w, Fintype.sum_prod_type] using Q.additiveWeight_log_expectation f hf
  have hproj : (∑ z, Q.imageFlat φ z * Real.log (C z)) =
      ∑ y, finitePush ν (imageEndpoint S φ) y * Real.log (B y) := by
    simp only [C]
    simp_rw [log_four_rpow (hB _) (hB _) (hB _) (hB _)]
    rw [Q.imageFlat_endpoint_expectation_factor φ (1 / 4 : ℝ) (fun y ↦ Real.log (B y))]
    norm_num
  change finiteEntropy Q.flat ≤ finiteEntropy (Q.imageFlat φ) +
    (∑ z, Q.imageFlat φ z * Real.log (C z)) - ∑ z, Q.flat z * Real.log (w z) at h
  rw [hparent, hcross, hproj] at h
  exact h

end StationaryAdditiveLaw
end
end Erdos539Geometry
