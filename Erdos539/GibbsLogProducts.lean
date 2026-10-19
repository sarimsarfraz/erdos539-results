/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsLiftSlack

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical

theorem log_four_rpow {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (t : ℝ) :
    Real.log (a ^ t * b ^ t * c ^ t * d ^ t) = t * (Real.log a + Real.log b + Real.log c + Real.log d) := by
  have hpa := Real.rpow_pos_of_pos ha t
  have hpb := Real.rpow_pos_of_pos hb t
  have hpc := Real.rpow_pos_of_pos hc t
  have hpd := Real.rpow_pos_of_pos hd t
  rw [Real.log_mul (mul_pos (mul_pos hpa hpb) hpc).ne' hpd.ne',
    Real.log_mul (mul_pos hpa hpb).ne' hpc.ne', Real.log_mul hpa.ne' hpb.ne',
    Real.log_rpow ha, Real.log_rpow hb, Real.log_rpow hc, Real.log_rpow hd]
  ring

variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
local instance gibbsLogImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

namespace StationaryAdditiveLaw
omit [DecidableEq G] [AddCommGroup H] [DecidableEq H] in
theorem endpoint_expectation_factor {S : Finset G} {ν : S → ℝ} (Q : StationaryAdditiveLaw S ν)
    (t : ℝ) (g : S → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, Q.mass a b c d * (t * (g a + g b + g c + g d))) =
      (4 * t) * ∑ x, ν x * g x := by
  simp_rw [mul_left_comm _ t]
  simp only [← Finset.mul_sum]
  rw [Q.endpoint_expectation]
  ring
end StationaryAdditiveLaw

omit [AddCommGroup G] [DecidableEq G] [AddCommGroup H] in
theorem imageReferenceProduct_log (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (a b c d : S.image φ) :
    Real.log (imageReferenceProduct S φ u a b c d) = (3 / 4 : ℝ) *
      (Real.log (finitePush u (imageEndpoint S φ) a) + Real.log (finitePush u (imageEndpoint S φ) b) +
        Real.log (finitePush u (imageEndpoint S φ) c) + Real.log (finitePush u (imageEndpoint S φ) d)) :=
  log_four_rpow (finitePush_imageEndpoint_pos S φ u hu a) (finitePush_imageEndpoint_pos S φ u hu b)
    (finitePush_imageEndpoint_pos S φ u hu c) (finitePush_imageEndpoint_pos S φ u hu d) _

omit [AddCommGroup H] in
theorem imageGeometricPartition_log (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (a b c d : S.image φ) :
    Real.log (imageGeometricPartition S φ u a b c d) = (1 / 4 : ℝ) *
      (Real.log (referencePartition (fiber S φ a.val) (imageFiberReference S φ u a)) +
        Real.log (referencePartition (fiber S φ b.val) (imageFiberReference S φ u b)) +
        Real.log (referencePartition (fiber S φ c.val) (imageFiberReference S φ u c)) +
        Real.log (referencePartition (fiber S φ d.val) (imageFiberReference S φ u d))) := by
  apply log_four_rpow
  all_goals exact referencePartition_pos (imageFiber_nonempty S φ _) (imageFiberReference_pos S φ u hu _)

/-- Endpoint averaging counts each of the four actual child log-partitions
once with coefficient 1/4. -/
theorem projected_log_geometric_average (S : Finset G) (φ : G →+ H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) :
    (∑ a, ∑ b, ∑ c, ∑ d, (projectedReferenceLaw S φ u hu).mass a b c d *
      Real.log (imageGeometricPartition S φ u a b c d)) =
      ∑ y, finitePush (referenceEndpoint S u) (imageEndpoint S φ) y *
        Real.log (referencePartition (fiber S φ y.val) (imageFiberReference S φ u y)) := by
  simp_rw [imageGeometricPartition_log S φ u hu]
  rw [(projectedReferenceLaw S φ u hu).endpoint_expectation_factor]
  norm_num

theorem projected_log_reference_average (S : Finset G) (φ : G →+ H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) :
    (∑ a, ∑ b, ∑ c, ∑ d, (projectedReferenceLaw S φ u hu).mass a b c d *
      Real.log (imageReferenceProduct S φ u a b c d)) =
      3 * ∑ y, finitePush (referenceEndpoint S u) (imageEndpoint S φ) y *
        Real.log (finitePush u (imageEndpoint S φ) y) := by
  simp_rw [imageReferenceProduct_log S φ u hu]
  rw [(projectedReferenceLaw S φ u hu).endpoint_expectation_factor]
  norm_num

end
end Erdos539Geometry
