/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ConvolutionAlgebra
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [AddCommGroup G] in
theorem extendWeight_variation (S : Finset G) (f g : S → ℝ) (t : ℝ) :
    extendWeight S (fun x ↦ f x + t * g x) = fun x ↦ extendWeight S f x + t * extendWeight S g x := by
  funext x
  by_cases hx : x ∈ S <;> simp [extendWeight, hx]

omit [AddCommGroup G] [DecidableEq G] in
theorem hasDerivAt_squareSum_variation (S : Finset G) (f g : S → ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∑ x, (f x + t * g x) ^ 2) (2 * ∑ x, f x * g x) 0 := by
  have hp : ∀ x : S, HasDerivAt (fun t : ℝ ↦ (f x + t * g x) ^ 2) (2 * f x * g x) 0 := by
    intro x
    simpa using ((hasDerivAt_const (0 : ℝ) (f x)).add ((hasDerivAt_id (0 : ℝ)).mul_const (g x))).pow 2
  simpa only [Finset.mul_sum, mul_assoc] using HasDerivAt.fun_sum (u := Finset.univ) (fun x _ ↦ hp x)

omit [DecidableEq G] in
theorem hasDerivAt_convolution_variation (S : Finset G) (f g : G → ℝ) (z : G) :
    HasDerivAt (fun t : ℝ ↦ weightedConvolution S (fun x ↦ f x + t * g x) (fun x ↦ f x + t * g x) z)
      (2 * weightedConvolution S f g z) 0 := by
  have hp : HasDerivAt (fun t : ℝ ↦ weightedConvolution S f f z +
      t * (2 * weightedConvolution S f g z) + t ^ 2 * weightedConvolution S g g z)
      (2 * weightedConvolution S f g z) 0 := by
    simpa using ((hasDerivAt_const (0 : ℝ) (weightedConvolution S f f z)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (2 * weightedConvolution S f g z))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (weightedConvolution S g g z))
  convert hp using 1
  funext t
  rw [weightedConvolution_variation]
  ring

theorem hasDerivAt_weightedEnergy_variation (S : Finset G) (f g : G → ℝ) :
    HasDerivAt (fun t : ℝ ↦ weightedEnergy S (fun x ↦ f x + t * g x))
      (4 * mixedWeightedEnergy S f f f g) 0 := by
  have hp : ∀ z, HasDerivAt
      (fun t : ℝ ↦ weightedConvolution S (fun x ↦ f x + t * g x) (fun x ↦ f x + t * g x) z ^ 2)
      (4 * (weightedConvolution S f f z * weightedConvolution S f g z)) 0 := by
    intro z
    convert (hasDerivAt_convolution_variation S f g z).pow 2 using 1
    simp only [zero_mul, add_zero, Nat.cast_ofNat]
    ring
  simpa only [weightedEnergy, mixedWeightedEnergy, Finset.mul_sum] using
    HasDerivAt.fun_sum (u := S + S) (fun z _ ↦ hp z)

theorem hasDerivAt_energy_extend_variation (S : Finset G) (f g : S → ℝ) :
    HasDerivAt (fun t : ℝ ↦ weightedEnergy S (extendWeight S (fun x ↦ f x + t * g x)))
      (4 * mixedWeightedEnergy S (extendWeight S f) (extendWeight S f) (extendWeight S f) (extendWeight S g)) 0 := by
  convert hasDerivAt_weightedEnergy_variation S (extendWeight S f) (extendWeight S g) using 1
  funext t
  rw [extendWeight_variation]

/-- The exact optimizer equation against every signed test weight. Absolute-
value domination justifies the unconstrained variations, even at zero atoms. -/
theorem energyMaximizer_stationary {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (g : S → ℝ) :
    mixedWeightedEnergy S (extendWeight S f) (extendWeight S f) (extendWeight S f) (extendWeight S g) =
      energyNorm S * ∑ x, f x * g x := by
  let Φ : ℝ → ℝ := fun t ↦ energyNorm S * (∑ x, (f x + t * g x) ^ 2) ^ 2 -
    weightedEnergy S (extendWeight S (fun x ↦ f x + t * g x))
  have hΦ0 : Φ 0 = 0 := by
    simp only [Φ, zero_mul, add_zero, hf.2, hE, one_pow, mul_one, sub_self]
  have hmin : IsLocalMin Φ 0 := by
    apply Filter.Eventually.of_forall
    intro t
    rw [hΦ0]
    exact sub_nonneg.mpr (energyNorm_bound S (fun x ↦ f x + t * g x))
  have hd := (((hasDerivAt_squareSum_variation S f g).pow 2).const_mul (energyNorm S)).sub
    (hasDerivAt_energy_extend_variation S f g)
  have hz := hmin.hasDerivAt_eq_zero hd
  simp only [zero_mul, add_zero, hf.2, one_pow, Nat.cast_ofNat, mul_one] at hz
  nlinarith

end
end Erdos539Geometry
