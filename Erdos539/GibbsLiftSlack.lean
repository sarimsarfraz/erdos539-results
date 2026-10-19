/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsProjectedDensity

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
local instance gibbsLiftImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

/-- The actual projection of the parent's Gibbs law; its endpoint law is
the parent's pushed-forward endpoint law, rather than the child's new law. -/
def projectedReferenceLaw (S : Finset G) (φ : G →+ H) (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    StationaryAdditiveLaw (S.image φ) (finitePush (referenceEndpoint S u) (imageEndpoint S φ)) :=
  (referenceGibbsLaw S u hu).map (imageEndpoint S φ) (imageEndpoint_preserves_additive S φ)

theorem projectedReferenceLaw_mass_density (S : Finset G) (φ : G →+ H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (a b c d : S.image φ) :
    (projectedReferenceLaw S φ u hu).mass a b c d =
      imageReferenceProduct S φ u a b c d * imageMixedPartition S φ u a b c d / referencePartition S u :=
  referenceGibbs_projected_density S φ u hu a b c d

theorem projectedReferenceLaw_endpoint_sum {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    ∑ x, finitePush (referenceEndpoint S u) (imageEndpoint S φ) x = 1 := by
  rw [finitePush_sum, referenceEndpoint_sum hS hu]

/-- Positive projected mass forces the literal lift partition to be
positive. No logarithm of a missing lift is used in the charged identity. -/
theorem imageMixedPartition_pos_of_projected_mass {S : Finset G} (hS : S.Nonempty)
    (φ : G →+ H) (u : S → ℝ) (hu : ∀ x, 0 < u x) {a b c d : S.image φ}
    (hp : (projectedReferenceLaw S φ u hu).mass a b c d ≠ 0) :
    0 < imageMixedPartition S φ u a b c d := by
  have hpos := lt_of_le_of_ne ((projectedReferenceLaw S φ u hu).nonneg a b c d) (Ne.symm hp)
  rw [projectedReferenceLaw_mass_density] at hpos
  by_contra hnot
  have hn := div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (imageReferenceProduct_pos S φ u hu a b c d).le (le_of_not_gt hnot))
    (referencePartition_pos hS hu).le
  linarith

/-- The logarithmic mixed-Holder loss. Only its parent-mass-weighted
version is charged; unattained projected quadruples have zero charge. -/
def imageLiftSlack (S : Finset G) (φ : G →+ H) (u : S → ℝ) (a b c d : S.image φ) : ℝ :=
  Real.log (imageGeometricPartition S φ u a b c d / imageMixedPartition S φ u a b c d)

def meanImageLiftSlack (S : Finset G) (φ : G →+ H) (u : S → ℝ) (hu : ∀ x, 0 < u x) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, (projectedReferenceLaw S φ u hu).mass a b c d * imageLiftSlack S φ u a b c d

theorem weighted_imageLiftSlack_nonneg {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) (a b c d : S.image φ) :
    0 ≤ (projectedReferenceLaw S φ u hu).mass a b c d * imageLiftSlack S φ u a b c d := by
  by_cases hp : (projectedReferenceLaw S φ u hu).mass a b c d = 0
  · rw [hp, zero_mul]
  have hK := imageMixedPartition_pos_of_projected_mass hS φ u hu hp
  have hratio : 1 ≤ imageGeometricPartition S φ u a b c d / imageMixedPartition S φ u a b c d :=
    (one_le_div hK).mpr (imageMixedPartition_le_geometric S φ u hu a b c d)
  exact mul_nonneg ((projectedReferenceLaw S φ u hu).nonneg _ _ _ _) (Real.log_nonneg hratio)

theorem meanImageLiftSlack_nonneg {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) : 0 ≤ meanImageLiftSlack S φ u hu :=
  Finset.sum_nonneg (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ Finset.sum_nonneg (fun c _ ↦
    Finset.sum_nonneg (fun d _ ↦ weighted_imageLiftSlack_nonneg hS φ u hu a b c d))))

theorem weighted_imageLiftSlack_log {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) (a b c d : S.image φ) :
    (projectedReferenceLaw S φ u hu).mass a b c d * imageLiftSlack S φ u a b c d =
      (projectedReferenceLaw S φ u hu).mass a b c d *
        (Real.log (imageGeometricPartition S φ u a b c d) - Real.log (imageMixedPartition S φ u a b c d)) := by
  by_cases hp : (projectedReferenceLaw S φ u hu).mass a b c d = 0
  · simp only [hp, zero_mul]
  rw [imageLiftSlack, Real.log_div (imageGeometricPartition_pos S φ u hu a b c d).ne'
    (imageMixedPartition_pos_of_projected_mass hS φ u hu hp).ne']

end
end Erdos539Geometry
