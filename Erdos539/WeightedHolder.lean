/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedCollisions

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def weightedCorrelation (S : Finset G) (f g : G → ℝ) (z : G) : ℝ :=
  ∑ p ∈ fiber (S ×ˢ S) (fun p ↦ p.1 - p.2) z, f p.1 * g p.2

def differenceMixedEnergy (S : Finset G) (f g h k : G → ℝ) : ℝ :=
  ∑ z ∈ S - S, weightedCorrelation S f g z * weightedCorrelation S h k z

theorem differenceMixedEnergy_eq_quadruples (S : Finset G) (f g h k : G → ℝ) :
    differenceMixedEnergy S f g h k = ∑ p ∈ S ×ˢ S, ∑ q ∈ S ×ˢ S,
      if p.1 - p.2 = q.1 - q.2 then (f p.1 * g p.2) * (h q.1 * k q.2) else 0 := by
  apply weighted_fiber_collision
  intro p hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  exact Finset.mem_sub.mpr ⟨p.1, ha, p.2, hb, rfl⟩

/-- Re-pairing an additive quadruple converts cross convolution energy into
an inner product of the two autocorrelations. -/
theorem mixedWeightedEnergy_repair (S : Finset G) (f g : G → ℝ) :
    mixedWeightedEnergy S f g f g = differenceMixedEnergy S f f g g := by
  rw [mixedWeightedEnergy_eq_quadruples, differenceMixedEnergy_eq_quadruples]
  simp_rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro b _
  have hrel : a + b = c + d ↔ a - c = d - b := by
    rw [sub_eq_sub_iff_add_eq_add]
    simp only [add_comm d c]
  by_cases h : a + b = c + d
  · simp only [if_pos h, if_pos (hrel.mp h)]
    ring
  · simp only [if_neg h, if_neg (mt hrel.mpr h)]

theorem differenceMixedEnergy_self (S : Finset G) (f : G → ℝ) :
    differenceMixedEnergy S f f f f = weightedEnergy S f := by
  rw [← mixedWeightedEnergy_repair, mixedWeightedEnergy_self]

/-- The second Cauchy-Schwarz step bounds cross convolution by the two
individual additive energies. It is valid for arbitrary real weights. -/
theorem crossWeightedEnergy_sq_le (S : Finset G) (f g : G → ℝ) :
    mixedWeightedEnergy S f g f g ^ 2 ≤ weightedEnergy S f * weightedEnergy S g := by
  rw [mixedWeightedEnergy_repair]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (S - S)
    (weightedCorrelation S f f) (weightedCorrelation S g g)
  have heF : (∑ z ∈ S - S, weightedCorrelation S f f z ^ 2) = weightedEnergy S f := by
    simpa only [differenceMixedEnergy, pow_two] using differenceMixedEnergy_self S f
  have heG : (∑ z ∈ S - S, weightedCorrelation S g g z ^ 2) = weightedEnergy S g := by
    simpa only [differenceMixedEnergy, pow_two] using differenceMixedEnergy_self S g
  rw [heF, heG] at h
  exact h

theorem crossWeightedEnergy_nonneg (S : Finset G) (f g : G → ℝ) :
    0 ≤ mixedWeightedEnergy S f g f g :=
  Finset.sum_nonneg (fun _ _ ↦ mul_self_nonneg _)

/-- Mixed-energy Holder, in a division-free fourth-power form. This finite
proof uses two Cauchy-Schwarz inequalities and no Fourier theorem. -/
theorem mixedWeightedEnergy_fourth_le (S : Finset G) (f g h k : G → ℝ) :
    mixedWeightedEnergy S f g h k ^ 4 ≤
      weightedEnergy S f * weightedEnergy S g * weightedEnergy S h * weightedEnergy S k := by
  have hfirst := mixedWeightedEnergy_sq_le S f g h k
  have hsecond := crossWeightedEnergy_sq_le S f g
  have hthird := crossWeightedEnergy_sq_le S h k
  have hproduct := mul_le_mul hsecond hthird (sq_nonneg _)
    (mul_nonneg (weightedEnergy_nonneg S f) (weightedEnergy_nonneg S g))
  have hn := mul_nonneg (crossWeightedEnergy_nonneg S f g) (crossWeightedEnergy_nonneg S h k)
  have hs : (mixedWeightedEnergy S f g h k ^ 2) ^ 2 ≤
      (mixedWeightedEnergy S f g f g * mixedWeightedEnergy S h k h k) ^ 2 := by
    nlinarith [sq_nonneg (mixedWeightedEnergy S f g h k)]
  nlinarith

end
end Erdos539Geometry
