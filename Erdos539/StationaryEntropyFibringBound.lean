/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ImageFiberWeights
import Erdos539.FiniteSubprobabilityEntropy
import Erdos539.GibbsLogProducts

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
local instance entropyImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

omit [AddCommGroup H] [DecidableEq H] in
theorem additiveWeight_log_expectation (Q : StationaryAdditiveLaw S ν)
    (f : S → ℝ) (hf : ∀ x, 0 < f x) :
    (∑ a, ∑ b, ∑ c, ∑ d, Q.mass a b c d * Real.log (additiveQuadrupleWeight S f a b c d)) =
      4 * ∑ x, ν x * Real.log (f x) := by
  have hpoint (a b c d : S) : Q.mass a b c d * Real.log (additiveQuadrupleWeight S f a b c d) =
      Q.mass a b c d * (Real.log (f a) + Real.log (f b) + Real.log (f c) + Real.log (f d)) := by
    by_cases he : a.val + b.val = c.val + d.val
    · simp only [additiveQuadrupleWeight, if_pos he,
        Real.log_mul (mul_pos (hf a) (hf b)).ne' (mul_pos (hf c) (hf d)).ne',
        Real.log_mul (hf a).ne' (hf b).ne', Real.log_mul (hf c).ne' (hf d).ne']
      ring
    · rw [Q.supported a b c d he]
      simp only [zero_mul]
  simp_rw [hpoint]
  exact Q.endpoint_expectation _

/-- Mixed-energy entropy fibring for an arbitrary actual stationary law
and arbitrary positive fiber test weights. It uses the actual projected
quadruple law, and does not postulate fiber entropy optimizers. -/
theorem entropy_image_fiber_bound (Q : StationaryAdditiveLaw S ν)
    (hν : ∑ x, ν x = 1) (φ : G →+ H) (f : S → ℝ) (hf : ∀ x, 0 < f x)
    (B : S.image φ → ℝ) (hB : ∀ y, 0 < B y)
    (hpart : ∀ y, weightedGibbsPartition (fiber S φ y.val) (imageFiberWeight S φ f y) ≤ B y) :
    Q.entropy ≤ (Q.map (imageEndpoint S φ) (imageEndpoint_preserves_additive S φ)).entropy +
      (∑ y, finitePush ν (imageEndpoint S φ) y * Real.log (B y)) - 4 * ∑ x, ν x * Real.log (f x) := by
  let w := fun z : (S × S) × (S × S) ↦ additiveQuadrupleWeight S f z.1.1 z.1.2 z.2.1 z.2.2
  let C := fun z : ((S.image φ) × (S.image φ)) × ((S.image φ) × (S.image φ)) ↦
    B z.1.1 ^ (1 / 4 : ℝ) * B z.1.2 ^ (1 / 4 : ℝ) * B z.2.1 ^ (1 / 4 : ℝ) * B z.2.2 ^ (1 / 4 : ℝ)
  let R := Q.map (imageEndpoint S φ) (imageEndpoint_preserves_additive S φ)
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
    (mapFour (imageEndpoint S φ)) C (fun z ↦ Q.nonneg _ _ _ _)
    (by simpa only [flat, Fintype.sum_prod_type] using Q.total_mass hν) hw hC hsup
    (fun z ↦ additiveWeight_image_push_le S φ f B hB hpart _ _ _ _)
  have hparent : finiteEntropy Q.flat = Q.entropy := by
    simp only [finiteEntropy, flat, entropy, Fintype.sum_prod_type]
  have himage : finiteEntropy (finitePush Q.flat (mapFour (imageEndpoint S φ))) = R.entropy := by
    simp only [finiteEntropy, R, map, entropy, Fintype.sum_prod_type]
  have hcross : (∑ z, Q.flat z * Real.log (w z)) = 4 * ∑ x, ν x * Real.log (f x) := by
    simpa only [flat, w, Fintype.sum_prod_type] using Q.additiveWeight_log_expectation f hf
  have hproj : (∑ z, finitePush Q.flat (mapFour (imageEndpoint S φ)) z * Real.log (C z)) =
      ∑ y, finitePush ν (imageEndpoint S φ) y * Real.log (B y) := by
    simp only [C, Fintype.sum_prod_type]
    simp_rw [log_four_rpow (hB _) (hB _) (hB _) (hB _)]
    change (∑ a, ∑ b, ∑ c, ∑ d, R.mass a b c d *
      ((1 / 4 : ℝ) * (Real.log (B a) + Real.log (B b) + Real.log (B c) + Real.log (B d)))) = _
    rw [R.endpoint_expectation_factor]
    norm_num
  rw [hparent, himage, hcross, hproj] at h
  exact h

end StationaryAdditiveLaw
end
end Erdos539Geometry
