/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryLawPush
import Erdos539.ActualWeightedPruning

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {ι : Type*}
local instance stationaryCoordinateEnergyDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The actual coordinate projection, with its image membership retained. -/
def projectEndpoint (S : Finset (ι → ℝ)) (I : Finset ι) (x : S) : projection S I :=
  ⟨project I x.val, by
    simp only [projection, Finset.mem_image]
    exact ⟨x.val, x.property, rfl⟩⟩

theorem projectEndpoint_preserves_additive (S : Finset (ι → ℝ)) (I : Finset ι)
    (a b c d : S) (h : a.val + b.val = c.val + d.val) :
    (projectEndpoint S I a).val + (projectEndpoint S I b).val =
      (projectEndpoint S I c).val + (projectEndpoint S I d).val :=
  congrArg (project I) h

theorem finitePush_projectEndpoint_sq (S : Finset (ι → ℝ)) (I : Finset ι) (f : S → ℝ)
    (v : projection S I) :
    finitePush (fun x ↦ f x ^ 2) (projectEndpoint S I) v =
      weightSquareSum (fiber S (project I) v.val) (extendWeight S f) := by
  simp only [finitePush, projectEndpoint, Subtype.ext_iff, weightSquareSum, fiber, Finset.sum_filter]
  rw [← Finset.sum_attach S]
  simp

theorem projected_sqrt_weight_unit (S : Finset (ι → ℝ)) (I : Finset ι) (f : S → ℝ)
    (hf : ∑ x, f x ^ 2 = 1) :
    (fun v ↦ Real.sqrt (finitePush (fun x ↦ f x ^ 2) (projectEndpoint S I) v)) ∈
      admissibleWeights (projection S I) := by
  refine ⟨fun _ ↦ Real.sqrt_nonneg _, ?_⟩
  simp_rw [Real.sq_sqrt (finitePush_nonneg _ _ (fun x ↦ sq_nonneg (f x)) _)]
  rw [finitePush_sum, hf]

/-- Literal equality with the original-fiber marginal used by weighted
pruning. In particular, this is not the energy of a replacement optimizer. -/
theorem projected_sqrt_energy_eq_actual (S : Finset (ι → ℝ)) (I : Finset ι) (f : S → ℝ) :
    weightedEnergy (projection S I)
      (extendWeight (projection S I) (fun v ↦ Real.sqrt (finitePush (fun x ↦ f x ^ 2) (projectEndpoint S I) v))) =
      actualMarginalEnergy S (extendWeight S f) I := by
  apply weightedEnergy_congr
  intro v hv
  simp only [extendWeight, dif_pos hv]
  rw [finitePush_projectEndpoint_sq]
  rfl

theorem actualMarginalEnergy_unit_bounds (S : Finset (ι → ℝ)) (I : Finset ι) (f : S → ℝ)
    (hf : ∑ x, f x ^ 2 = 1) :
    1 ≤ actualMarginalEnergy S (extendWeight S f) I ∧
      actualMarginalEnergy S (extendWeight S f) I ≤ energyNorm (projection S I) := by
  have hunit := projected_sqrt_weight_unit S I f hf
  have hl := weightedEnergy_ge_squareSum_sq (projection S I)
    (extendWeight (projection S I) (fun v ↦ Real.sqrt (finitePush (fun x ↦ f x ^ 2) (projectEndpoint S I) v)))
  rw [weightSquareSum_extend, hunit.2, one_pow, projected_sqrt_energy_eq_actual] at hl
  have hu := energyNorm_ge_admissible hunit
  rw [projected_sqrt_energy_eq_actual] at hu
  exact ⟨hl, hu⟩

namespace StationaryAdditiveLaw
variable {S : Finset (ι → ℝ)} {f : S → ℝ}

def projectLaw (Q : StationaryAdditiveLaw S (fun x ↦ f x ^ 2)) (I : Finset ι) :
    StationaryAdditiveLaw (projection S I)
      (finitePush (fun x ↦ f x ^ 2) (projectEndpoint S I)) :=
  Q.map (projectEndpoint S I) (projectEndpoint_preserves_additive S I)

/-- The first energy comparison in the parallel-projection theorem,
for every literal projected law. The later correlation and sweep bounds
are separate statements. -/
theorem projected_entropy_le_log_actual (Q : StationaryAdditiveLaw S (fun x ↦ f x ^ 2))
    (hf : ∑ x, f x ^ 2 = 1) (I : Finset ι) :
    (Q.projectLaw I).entropy -
      2 * finiteEntropy (finitePush (fun x ↦ f x ^ 2) (projectEndpoint S I)) ≤
      Real.log (actualMarginalEnergy S (extendWeight S f) I) := by
  have h := Q.map_entropy_le_log_energy (fun x ↦ sq_nonneg (f x)) hf
    (projectEndpoint S I) (projectEndpoint_preserves_additive S I)
  rw [projected_sqrt_energy_eq_actual] at h
  exact h

end StationaryAdditiveLaw
end
end Erdos539Geometry
