/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.QuadrupleLaw
import Erdos539.FiniteEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem optimizerQuadrupleLaw_entropy_term {S : Finset G} (hS : S.Nonempty)
    (f : S → ℝ) (a b c d : S) :
    Real.negMulLog (optimizerQuadrupleLaw S f a b c d) =
      optimizerQuadrupleLaw S f a b c d *
        (Real.log (energyNorm S) - Real.log (f a) - Real.log (f b) -
          Real.log (f c) - Real.log (f d)) := by
  by_cases habcd : a.val + b.val = c.val + d.val
  · by_cases ha : f a = 0
    · simp [optimizerQuadrupleLaw, additiveQuadrupleWeight, habcd, ha]
    by_cases hb : f b = 0
    · simp [optimizerQuadrupleLaw, additiveQuadrupleWeight, habcd, hb]
    by_cases hc : f c = 0
    · simp [optimizerQuadrupleLaw, additiveQuadrupleWeight, habcd, hc]
    by_cases hd : f d = 0
    · simp [optimizerQuadrupleLaw, additiveQuadrupleWeight, habcd, hd]
    have hlog : Real.log (optimizerQuadrupleLaw S f a b c d) =
        Real.log (f a) + Real.log (f b) + (Real.log (f c) + Real.log (f d)) -
          Real.log (energyNorm S) := by
      simp only [optimizerQuadrupleLaw, additiveQuadrupleWeight, if_pos habcd]
      rw [Real.log_div (mul_ne_zero (mul_ne_zero ha hb) (mul_ne_zero hc hd))
        (energyNorm_pos hS).ne', Real.log_mul (mul_ne_zero ha hb) (mul_ne_zero hc hd),
        Real.log_mul ha hb, Real.log_mul hc hd]
    unfold Real.negMulLog
    rw [hlog]
    ring
  · simp [optimizerQuadrupleLaw, additiveQuadrupleWeight, habcd]

/-- Entropy of the canonical additive-quadruple law, in nats. -/
def optimizerQuadrupleEntropy (S : Finset G) (f : S → ℝ) : ℝ :=
  ∑ a : S, ∑ b : S, ∑ c : S, ∑ d : S,
    Real.negMulLog (optimizerQuadrupleLaw S f a b c d)

/-- The actual canonical law has H(Q) = log Lambda + 2 H(f^2).
Every endpoint marginal is proved from optimizer stationarity. -/
theorem optimizerQuadrupleEntropy_eq {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    optimizerQuadrupleEntropy S f = Real.log (energyNorm S) +
      2 * finiteEntropy (fun x : S ↦ f x ^ 2) := by
  let Q := optimizerQuadrupleLaw S f
  have hconst : (∑ a, ∑ b, ∑ c, ∑ d, Q a b c d * Real.log (energyNorm S)) =
      Real.log (energyNorm S) := by
    simp only [← Finset.sum_mul, Q, optimizerQuadrupleLaw_sum hS hf hE, one_mul]
  have hfirst : (∑ a, ∑ b, ∑ c, ∑ d, Q a b c d * Real.log (f a)) =
      ∑ a, f a ^ 2 * Real.log (f a) := by
    simp only [← Finset.sum_mul, Q, optimizerQuadrupleLaw_first_marginal hS hf hE]
  have hsecond : (∑ a, ∑ b, ∑ c, ∑ d, Q a b c d * Real.log (f b)) =
      ∑ b, f b ^ 2 * Real.log (f b) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, Q, optimizerQuadrupleLaw_second_marginal hS hf hE]
  have hthird : (∑ a, ∑ b, ∑ c, ∑ d, Q a b c d * Real.log (f c)) =
      ∑ c, f c ^ 2 * Real.log (f c) := by
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, Q, optimizerQuadrupleLaw_third_marginal hS hf hE]
  have hfourth : (∑ a, ∑ b, ∑ c, ∑ d, Q a b c d * Real.log (f d)) =
      ∑ d, f d ^ 2 * Real.log (f d) := by
    conv_lhs => arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, Q, optimizerQuadrupleLaw_fourth_marginal hS hf hE]
  have hent : finiteEntropy (fun x : S ↦ f x ^ 2) =
      -2 * ∑ x : S, f x ^ 2 * Real.log (f x) := by
    simp only [finiteEntropy, Real.negMulLog, Real.log_pow, Nat.cast_ofNat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  unfold optimizerQuadrupleEntropy
  simp_rw [optimizerQuadrupleLaw_entropy_term hS, mul_sub, Finset.sum_sub_distrib]
  change (∑ a, ∑ b, ∑ c, ∑ d, Q a b c d * Real.log (energyNorm S)) -
    (∑ a, ∑ b, ∑ c, ∑ d, Q a b c d * Real.log (f a)) -
    (∑ a, ∑ b, ∑ c, ∑ d, Q a b c d * Real.log (f b)) -
    (∑ a, ∑ b, ∑ c, ∑ d, Q a b c d * Real.log (f c)) -
    (∑ a, ∑ b, ∑ c, ∑ d, Q a b c d * Real.log (f d)) = _
  rw [hconst, hfirst, hsecond, hthird, hfourth, hent]
  ring

theorem energyMaximizer_entropy_bounds {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    Real.log (energyNorm S) ≤ finiteEntropy (fun x : S ↦ f x ^ 2) ∧
      finiteEntropy (fun x : S ↦ f x ^ 2) ≤ Real.log S.card := by
  letI : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  constructor
  · exact finiteEntropy_ge_log_of_atom_bound _ (fun x ↦ sq_nonneg _) hf.2
      (energyNorm_pos hS) (energyMaximizer_atom_bound hS hf hE)
  · simpa only [Fintype.card_coe] using finiteEntropy_le_log_card _ (fun x : S ↦ sq_nonneg (f x)) hf.2

end
end Erdos539Geometry
