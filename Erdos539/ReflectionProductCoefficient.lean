/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SparseReflectionProductExistence
import Erdos539.ReflectionCoverCard

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
local instance reflectionProductCoefficientRealDecidableEq {ι : Type} : DecidableEq (ι → ℝ) := Classical.decEq _
local instance reflectionProductCoefficientIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _

/-- Every c<2 fails with any fixed additive allowance, uniformly over all
positive strip parameters. Hence making the parent norm/fan ratio arbitrarily
large does not repair reflection. All exact optimizers are included. -/
theorem eventually_product_reflection_coefficient_obstruction (c A : ℝ) (hc : c < 2) :
    ∃ M : ℕ, 10 ≤ M ∧ ∀ m : ℕ, M ≤ m →
      ∃ S : Finset ℤ, S.Nonempty ∧ ∀ T : ℕ, 0 < T →
        (sparseReflectionProduct S T).Nonempty ∧
        (T : ℝ) / (27 * (m : ℝ)) ≤ energyNorm (sparseReflectionProduct S T) / maxFan (sparseReflectionProduct S T) ∧
        ∀ f : sparseReflectionProduct S T → ℝ, f ∈ admissibleWeights (sparseReflectionProduct S T) →
          weightedEnergy (sparseReflectionProduct S T) (extendWeight _ f) = energyNorm (sparseReflectionProduct S T) →
          ∀ w, energyNorm (reflectedSupport (sparseReflectionProduct S T) w) <
            energyNorm (sparseReflectionProduct S T) * Real.exp
              (-c * (finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm (sparseReflectionProduct S T))) - A) := by
  let d := max c 0
  have hd : d < 2 := max_lt hc (by norm_num)
  have hd0 : 0 ≤ d := le_max_right _ _
  have hcd : c ≤ d := le_max_left _ _
  obtain ⟨M, hM⟩ := exists_nat_gt (max 10 (Real.exp ((A + Real.log 24 + d * Real.log 54 + 1) / (2 - d))))
  have hM10 : (10 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hMn : 10 ≤ M := by exact_mod_cast hM10.le
  refine ⟨M, hMn, ?_⟩
  intro m hm
  have hmn : 10 ≤ m := hMn.trans hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hMm : (M : ℝ) ≤ m := by exact_mod_cast hm
  have hexp : Real.exp ((A + Real.log 24 + d * Real.log 54 + 1) / (2 - d)) < m :=
    ((le_max_right _ _).trans_lt hM).trans_le hMm
  have hlog := Real.log_lt_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  have hgap := (div_lt_iff₀ (sub_pos.mpr hd)).mp hlog
  obtain ⟨S, hS, _, _, hproducts⟩ := exists_sparse_reflection_products m hmn
  refine ⟨S, hS, ?_⟩
  intro T hT
  obtain ⟨hP, hfan, hcard, href⟩ := hproducts T hT
  refine ⟨hP, hfan, ?_⟩
  intro f hf hE w
  let P := sparseReflectionProduct S T
  let e := finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm P)
  have he0 : 0 ≤ e := sub_nonneg.mpr (energyMaximizer_entropy_bounds hP hf hE).1
  have hehi : e ≤ Real.log (m : ℝ) + Real.log 54 :=
    (reflection_product_optimizer_bounds hP hmR hcard href hf hE).2.1
  have hce : c * e ≤ d * (Real.log (m : ℝ) + Real.log 54) :=
    (mul_le_mul_of_nonneg_right hcd he0).trans (mul_le_mul_of_nonneg_left hehi hd0)
  by_cases hw : (reflectedSupport P w).Nonempty
  · have hl := reflection_loss_of_norm_bound hP hmR w hw (href w)
    have hstrict : c * e + A < Real.log (energyNorm P / energyNorm (reflectedSupport P w)) := by
      nlinarith only [hgap, hce, hl]
    rw [Real.log_div (energyNorm_pos hP).ne' (energyNorm_pos hw).ne'] at hstrict
    apply (Real.log_lt_log_iff (energyNorm_pos hw)
      (mul_pos (energyNorm_pos hP) (Real.exp_pos _))).mp
    rw [Real.log_mul (energyNorm_pos hP).ne' (Real.exp_pos _).ne', Real.log_exp]
    change Real.log (energyNorm (reflectedSupport P w)) < Real.log (energyNorm P) + (-c * e - A)
    linarith
  · change energyNorm (reflectedSupport P w) < _
    rw [Finset.not_nonempty_iff_eq_empty.mp hw, energyNorm_empty]
    exact mul_pos (energyNorm_pos hP) (Real.exp_pos _)

end
end Erdos539Geometry
