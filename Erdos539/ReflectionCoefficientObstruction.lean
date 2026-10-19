/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SparseReflectionEntropyLoss
import Erdos539.QuadrupleEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance reflectionCoefficientIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _
local instance reflectionCoefficientIndexDecidableEq (S : Finset ℤ) : DecidableEq S := Classical.decEq _

/-- Every coefficient below two fails, with any fixed additive error,
for all sufficiently large parameters and every exact optimizer of the
same constructed scalar support. Empty reflected supports are included. -/
theorem eventually_reflection_coefficient_obstruction (c A : ℝ) (hc : c < 2) :
    ∃ M : ℕ, 10 ≤ M ∧ ∀ m : ℕ, M ≤ m →
      ∃ S : Finset ℤ, S.Nonempty ∧ S ⊆ Finset.Ico 0 ((m ^ 12 : ℕ) : ℤ) ∧
        ∀ f : S → ℝ, f ∈ admissibleWeights S →
          weightedEnergy S (extendWeight S f) = energyNorm S →
          ∀ w : ℤ, energyNorm (reflectedSupport S w) <
            energyNorm S * Real.exp (-c * (finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm S)) - A) := by
  let d := max c 0
  have hd : d < 2 := max_lt hc (by norm_num)
  have hd0 : 0 ≤ d := le_max_right _ _
  have hcd : c ≤ d := le_max_left _ _
  obtain ⟨M, hM⟩ := exists_nat_gt (max 10 (Real.exp ((A + Real.log 24 + d * Real.log 16 + 1) / (2 - d))))
  have hM10 : (10 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hMn : 10 ≤ M := by exact_mod_cast hM10.le
  refine ⟨M, hMn, ?_⟩
  intro m hm
  have hmn : 10 ≤ m := hMn.trans hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hMm : (M : ℝ) ≤ m := by exact_mod_cast hm
  have hexp : Real.exp ((A + Real.log 24 + d * Real.log 16 + 1) / (2 - d)) < m :=
    ((le_max_right _ _).trans_lt hM).trans_le hMm
  have hlog := Real.log_lt_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  have hgap := (div_lt_iff₀ (sub_pos.mpr hd)).mp hlog
  obtain ⟨S, hS, hI, hratio, hent⟩ := exists_sparse_reflection_entropy_loss m hmn
  refine ⟨S, hS, hI, ?_⟩
  intro f hf hE w
  let e := finiteEntropy (fun x : S ↦ f x ^ 2) - Real.log (energyNorm S)
  have he0 : 0 ≤ e := sub_nonneg.mpr (energyMaximizer_entropy_bounds hS hf hE).1
  have hehi : e ≤ Real.log (m : ℝ) + Real.log 16 := (hent _ (fun x ↦ sq_nonneg (f x)) hf.2).1
  have hce : c * e ≤ d * (Real.log (m : ℝ) + Real.log 16) :=
    (mul_le_mul_of_nonneg_right hcd he0).trans (mul_le_mul_of_nonneg_left hehi hd0)
  by_cases hw : (reflectedSupport S w).Nonempty
  · have hl := reflected_log_norm_loss_of_ratio hS hmR w hw (hratio w)
    have hstrict : c * e + A < Real.log (energyNorm S / energyNorm (reflectedSupport S w)) := by
      nlinarith only [hgap, hce, hl]
    rw [Real.log_div (energyNorm_pos hS).ne' (energyNorm_pos hw).ne'] at hstrict
    apply (Real.log_lt_log_iff (energyNorm_pos hw)
      (mul_pos (energyNorm_pos hS) (Real.exp_pos _))).mp
    rw [Real.log_mul (energyNorm_pos hS).ne' (Real.exp_pos _).ne', Real.log_exp]
    change Real.log (energyNorm (reflectedSupport S w)) < Real.log (energyNorm S) + (-c * e - A)
    linarith
  · have he : reflectedSupport S w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hw
    rw [he, energyNorm_empty]
    exact mul_pos (energyNorm_pos hS) (Real.exp_pos _)

end
end Erdos539Geometry
