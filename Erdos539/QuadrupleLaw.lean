/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyAtoms

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The literal unnormalized additive-quadruple weight on the actual support. -/
def additiveQuadrupleWeight (S : Finset G) (f : S → ℝ) (a b c d : S) : ℝ :=
  if a.val + b.val = c.val + d.val then (f a * f b) * (f c * f d) else 0

/-- The canonical law associated to an exact energy optimizer. -/
def optimizerQuadrupleLaw (S : Finset G) (f : S → ℝ) (a b c d : S) : ℝ :=
  additiveQuadrupleWeight S f a b c d / energyNorm S

theorem mixedWeightedEnergy_subtype (S : Finset G) (f g h k : S → ℝ) :
    mixedWeightedEnergy S (extendWeight S f) (extendWeight S g)
      (extendWeight S h) (extendWeight S k) =
      ∑ a : S, ∑ b : S, ∑ c : S, ∑ d : S,
        if a.val + b.val = c.val + d.val then (f a * g b) * (h c * k d) else 0 := by
  rw [mixedWeightedEnergy_eq_quadruples]
  simp only [Finset.sum_product]
  rw [← Finset.sum_attach S]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_attach S]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_attach S]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_attach S]
  simp

theorem additiveQuadrupleWeight_swap_left (S : Finset G) (f : S → ℝ) (a b c d : S) :
    additiveQuadrupleWeight S f a b c d = additiveQuadrupleWeight S f b a c d := by
  simp only [additiveQuadrupleWeight, add_comm a.val b.val, mul_comm (f a) (f b)]

theorem additiveQuadrupleWeight_swap_right (S : Finset G) (f : S → ℝ) (a b c d : S) :
    additiveQuadrupleWeight S f a b c d = additiveQuadrupleWeight S f a b d c := by
  simp only [additiveQuadrupleWeight, add_comm c.val d.val, mul_comm (f c) (f d)]

theorem additiveQuadrupleWeight_swap_sides (S : Finset G) (f : S → ℝ) (a b c d : S) :
    additiveQuadrupleWeight S f a b c d = additiveQuadrupleWeight S f c d a b := by
  simp only [additiveQuadrupleWeight, eq_comm, mul_comm]

theorem additiveQuadrupleWeight_fourth_marginal {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (d : S) :
    (∑ a : S, ∑ b : S, ∑ c : S, additiveQuadrupleWeight S f a b c d) =
      energyNorm S * f d ^ 2 := by
  have hstat := energyMaximizer_stationary hf hE (fun x ↦ pointWeight d.val x.val)
  rw [inner_pointWeight, mixedWeightedEnergy_subtype] at hstat
  have htest :
      (∑ a : S, ∑ b : S, ∑ c : S, ∑ x : S,
        if a.val + b.val = c.val + x.val then (f a * f b) * (f c * pointWeight d.val x.val) else 0) =
      ∑ a : S, ∑ b : S, ∑ c : S,
        if a.val + b.val = c.val + d.val then (f a * f b) * f c else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    have he : ∀ x : S,
        (if a.val + b.val = c.val + x.val then (f a * f b) * (f c * pointWeight d.val x.val) else 0) =
        if x = d then (if a.val + b.val = c.val + d.val then (f a * f b) * f c else 0) else 0 := by
      intro x
      by_cases hx : x = d
      · subst x
        simp [pointWeight]
      · have hv : x.val ≠ d.val := fun h ↦ hx (Subtype.ext h)
        simp [pointWeight, hx, hv]
    simp_rw [he]
    simp
  rw [htest] at hstat
  calc
    _ = (∑ a : S, ∑ b : S, ∑ c : S,
        if a.val + b.val = c.val + d.val then (f a * f b) * f c else 0) * f d := by
      simp only [Finset.sum_mul, additiveQuadrupleWeight, ite_mul, zero_mul, mul_assoc]
    _ = _ := by rw [hstat]; ring

theorem additiveQuadrupleWeight_third_marginal {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (c : S) :
    (∑ a : S, ∑ b : S, ∑ d : S, additiveQuadrupleWeight S f a b c d) =
      energyNorm S * f c ^ 2 := by
  simp_rw [additiveQuadrupleWeight_swap_right S f _ _ c]
  exact additiveQuadrupleWeight_fourth_marginal hf hE c

theorem additiveQuadrupleWeight_first_marginal {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (a : S) :
    (∑ b : S, ∑ c : S, ∑ d : S, additiveQuadrupleWeight S f a b c d) =
      energyNorm S * f a ^ 2 := by
  simp_rw [additiveQuadrupleWeight_swap_sides S f a]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
  exact additiveQuadrupleWeight_third_marginal hf hE a

theorem additiveQuadrupleWeight_second_marginal {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (b : S) :
    (∑ a : S, ∑ c : S, ∑ d : S, additiveQuadrupleWeight S f a b c d) =
      energyNorm S * f b ^ 2 := by
  simp_rw [additiveQuadrupleWeight_swap_left S f _ b]
  exact additiveQuadrupleWeight_first_marginal hf hE b

theorem optimizerQuadrupleLaw_nonneg {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (a b c d : S) :
    0 ≤ optimizerQuadrupleLaw S f a b c d := by
  apply div_nonneg _ (energyNorm_nonneg S)
  unfold additiveQuadrupleWeight
  split_ifs
  · exact mul_nonneg (mul_nonneg (hf.1 a) (hf.1 b)) (mul_nonneg (hf.1 c) (hf.1 d))
  · rfl

theorem optimizerQuadrupleLaw_fourth_marginal {S : Finset G} {f : S → ℝ}
    (hS : S.Nonempty) (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) (d : S) :
    (∑ a : S, ∑ b : S, ∑ c : S, optimizerQuadrupleLaw S f a b c d) = f d ^ 2 := by
  simp only [optimizerQuadrupleLaw, div_eq_mul_inv, ← Finset.sum_mul]
  rw [additiveQuadrupleWeight_fourth_marginal hf hE]
  field_simp [ne_of_gt (energyNorm_pos hS)]

theorem optimizerQuadrupleLaw_first_marginal {S : Finset G} {f : S → ℝ}
    (hS : S.Nonempty) (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) (a : S) :
    (∑ b : S, ∑ c : S, ∑ d : S, optimizerQuadrupleLaw S f a b c d) = f a ^ 2 := by
  simp only [optimizerQuadrupleLaw, div_eq_mul_inv, ← Finset.sum_mul]
  rw [additiveQuadrupleWeight_first_marginal hf hE]
  field_simp [ne_of_gt (energyNorm_pos hS)]

theorem optimizerQuadrupleLaw_second_marginal {S : Finset G} {f : S → ℝ}
    (hS : S.Nonempty) (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) (b : S) :
    (∑ a : S, ∑ c : S, ∑ d : S, optimizerQuadrupleLaw S f a b c d) = f b ^ 2 := by
  simp only [optimizerQuadrupleLaw, div_eq_mul_inv, ← Finset.sum_mul]
  rw [additiveQuadrupleWeight_second_marginal hf hE]
  field_simp [ne_of_gt (energyNorm_pos hS)]

theorem optimizerQuadrupleLaw_third_marginal {S : Finset G} {f : S → ℝ}
    (hS : S.Nonempty) (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) (c : S) :
    (∑ a : S, ∑ b : S, ∑ d : S, optimizerQuadrupleLaw S f a b c d) = f c ^ 2 := by
  simp only [optimizerQuadrupleLaw, div_eq_mul_inv, ← Finset.sum_mul]
  rw [additiveQuadrupleWeight_third_marginal hf hE]
  field_simp [ne_of_gt (energyNorm_pos hS)]

theorem optimizerQuadrupleLaw_sum {S : Finset G} {f : S → ℝ}
    (hS : S.Nonempty) (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    (∑ a : S, ∑ b : S, ∑ c : S, ∑ d : S, optimizerQuadrupleLaw S f a b c d) = 1 := by
  simp_rw [optimizerQuadrupleLaw_first_marginal hS hf hE]
  exact hf.2

end
end Erdos539Geometry
