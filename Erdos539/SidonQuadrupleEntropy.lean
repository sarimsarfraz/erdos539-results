/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SidonLabelAlgebra
import Erdos539.SharpSidonSums
import Erdos539.FiniteSubprobabilityEntropy
import Erdos539.GibbsLogProducts

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical

/-- A literal probability law supported on equal unordered label pairs
has entropy at most log_2(6) times its common endpoint entropy. The
common-marginal identity is explicit and is proved for actual label
pushforwards in the application. -/
theorem sidonQuadruple_entropy_le {α : Type*} [Fintype α]
    (p : (α × α) × (α × α) → ℝ) (η : α → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hps : ∑ z, p z = 1)
    (hη : ∀ x, 0 < η x) (hηs : ∑ x, η x = 1)
    (hsupport : ∀ z, p z ≠ 0 → SameUnorderedPair z.1.1 z.1.2 z.2.1 z.2.2)
    (hend : ∀ g : α → ℝ, (∑ z, p z * (g z.1.1 + g z.1.2 + g z.2.1 + g z.2.2)) = 4 * ∑ x, η x * g x) :
    finiteEntropy p ≤ sharpSidonExponent * finiteEntropy η := by
  let w := fun x ↦ η x ^ (sharpSidonExponent / 4)
  let W := fun z : (α × α) × (α × α) ↦
    if SameUnorderedPair z.1.1 z.1.2 z.2.1 z.2.2 then (w z.1.1 * w z.1.2) * (w z.2.1 * w z.2.2) else 0
  have hw : ∀ x, 0 < w x := fun x ↦ Real.rpow_pos_of_pos (hη x) _
  have hW : ∀ z, 0 ≤ W z := by
    intro z
    dsimp only [W]
    split_ifs
    · exact (mul_pos (mul_pos (hw _) (hw _)) (mul_pos (hw _) (hw _))).le
    · rfl
  have hγ : sharpSidonExponent ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) sharpSidonExponent_bounds.1)
  have hpow : (sharpSidonExponent / 4) * (4 / sharpSidonExponent) = 1 := by field_simp
  have hroot (x : α) : w x ^ (4 / sharpSidonExponent) = η x := by
    dsimp only [w]
    rw [← Real.rpow_mul (hη x).le, hpow, Real.rpow_one]
  have hWs : ∑ z, W z ≤ 1 := by
    simp only [W, Fintype.sum_prod_type]
    rw [unordered_pair_energy]
    have h := sharp_sidon_energy_bound Finset.univ w (fun x _ ↦ (hw x).le)
    simpa only [hroot, hηs, Real.one_rpow] using h
  have hsup : ∀ z, p z ≠ 0 → 0 < W z := by
    intro z hz
    simp only [W, if_pos (hsupport z hz)]
    exact mul_pos (mul_pos (hw _) (hw _)) (mul_pos (hw _) (hw _))
  have h := finiteRelEntropy_subprob_nonneg p W hp hW hps hWs hsup
  have hpoint (z : (α × α) × (α × α)) : p z * Real.log (W z) =
      p z * ((sharpSidonExponent / 4) *
        (Real.log (η z.1.1) + Real.log (η z.1.2) + Real.log (η z.2.1) + Real.log (η z.2.2))) := by
    by_cases hz : p z = 0
    · simp [hz]
    have he : (w z.1.1 * w z.1.2) * (w z.2.1 * w z.2.2) = w z.1.1 * w z.1.2 * w z.2.1 * w z.2.2 := by ring
    dsimp only [W]
    rw [if_pos (hsupport z hz), he]
    dsimp only [w]
    rw [log_four_rpow (hη _) (hη _) (hη _) (hη _)]
  have hcross : (∑ z, p z * Real.log (W z)) = -sharpSidonExponent * finiteEntropy η := by
    simp_rw [hpoint, mul_left_comm _ (sharpSidonExponent / 4)]
    rw [← Finset.mul_sum, hend (fun x ↦ Real.log (η x))]
    simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
    ring
  rw [finiteRelEntropy_eq_entropy_cross, hcross] at h
  linarith

end
end Erdos539Geometry
