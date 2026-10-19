/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyNormBasics

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [AddCommGroup G] in
theorem extendWeight_scale (S : Finset G) (f : S → ℝ) (c : ℝ) :
    extendWeight S (fun x ↦ c * f x) = fun x ↦ c * extendWeight S f x := by
  funext x
  by_cases hx : x ∈ S <;> simp [extendWeight, hx]

omit [AddCommGroup G] in
theorem extendWeight_abs (S : Finset G) (f : S → ℝ) :
    extendWeight S (fun x ↦ |f x|) = fun x ↦ |extendWeight S f x| := by
  funext x
  by_cases hx : x ∈ S <;> simp [extendWeight, hx]

/-- Taking absolute values cannot decrease additive energy. -/
theorem weightedEnergy_le_abs (S : Finset G) (f : G → ℝ) :
    weightedEnergy S f ≤ weightedEnergy S (fun x ↦ |f x|) := by
  rw [weightedEnergy_eq_quadruples, weightedEnergy_eq_quadruples]
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro q _
  by_cases h : p.1 + p.2 = q.1 + q.2
  · simp only [if_pos h]
    simpa only [abs_mul] using le_abs_self ((f p.1 * f p.2) * (f q.1 * f q.2))
  · simp only [if_neg h, le_refl]

/-- The exact norm controls every nonnegative weight, without a normalization
premise. The zero-square-sum case is included. -/
theorem energyNorm_bound_nonneg (S : Finset G) (f : S → ℝ) (hf : ∀ x, 0 ≤ f x) :
    weightedEnergy S (extendWeight S f) ≤ energyNorm S * (∑ x, f x ^ 2) ^ 2 := by
  let L : ℝ := ∑ x, f x ^ 2
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  by_cases hL : L = 0
  · have hf0 : f = 0 := by
      funext x
      have hs : f x ^ 2 ≤ L := Finset.single_le_sum (fun y _ ↦ sq_nonneg (f y)) (Finset.mem_univ x)
      rw [hL] at hs
      change f x = 0
      nlinarith [sq_nonneg (f x)]
    rw [hf0]
    simp [extendWeight, weightedEnergy, weightedConvolution]
  · have hLp : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL)
    have hr : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLp
    let c : ℝ := 1 / Real.sqrt L
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hcL : c ^ 2 * L = 1 := by
      dsimp [c]
      field_simp
      nlinarith [Real.sq_sqrt hL0]
    let g : S → ℝ := fun x ↦ c * f x
    have hg : g ∈ admissibleWeights S := by
      refine ⟨fun x ↦ mul_nonneg hc (hf x), ?_⟩
      change (∑ x : S, (c * f x) ^ 2) = 1
      simp_rw [mul_pow]
      rw [← Finset.mul_sum]
      exact hcL
    have hmax := energyNorm_ge_admissible hg
    change weightedEnergy S (extendWeight S (fun x ↦ c * f x)) ≤ energyNorm S at hmax
    rw [extendWeight_scale, weightedEnergy_scale] at hmax
    have he : c ^ 4 * L ^ 2 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, ← mul_pow, hcL, one_pow]
    change weightedEnergy S (extendWeight S f) ≤ energyNorm S * L ^ 2
    calc
      _ = (c ^ 4 * weightedEnergy S (extendWeight S f)) * L ^ 2 := by
        have hh := congrArg (fun x ↦ x * weightedEnergy S (extendWeight S f)) he
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hmax (sq_nonneg L)

/-- The same bound holds for arbitrary real weights. This permits unconstrained
first-order variations at a nonnegative maximizing weight. -/
theorem energyNorm_bound (S : Finset G) (f : S → ℝ) :
    weightedEnergy S (extendWeight S f) ≤ energyNorm S * (∑ x, f x ^ 2) ^ 2 := by
  have h := energyNorm_bound_nonneg S (fun x ↦ |f x|) (fun _ ↦ abs_nonneg _)
  rw [extendWeight_abs] at h
  simp only [sq_abs] at h
  exact (weightedEnergy_le_abs S (extendWeight S f)).trans h

end
end Erdos539Geometry
