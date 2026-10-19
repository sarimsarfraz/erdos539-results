/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.UniformEnergyWeight
import Erdos539.SidonEnergy
import Erdos539.StationaryUniformDefect
import Erdos539.StationaryOptimizedProfile

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem countingEnergy_sidon {S : Finset G} (hS : HasSidonSums S) :
    countingEnergy S = 2 * (S.card : ℝ) ^ 2 - S.card := by
  simpa only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
    weightedEnergy_sidon hS (fun _ ↦ 1)

theorem sidon_admissible_energy_upper {S : Finset G} (hS : S.Nonempty) (hSidon : HasSidonSums S)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S) :
    weightedEnergy S (extendWeight S f) ≤ 2 - 1 / (S.card : ℝ) := by
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have h2 : (∑ x ∈ S, extendWeight S f x ^ 2) = 1 := by
    change weightSquareSum S (extendWeight S f) = 1
    rw [weightSquareSum_extend, hf.2]
  have h4 : (∑ x ∈ S, extendWeight S f x ^ 4) = ∑ x : S, f x ^ 4 := by
    rw [← Finset.sum_attach S]
    simp
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset S)
    (fun _ ↦ (1 : ℝ)) (fun x ↦ f x ^ 2)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul, mul_one, ← pow_mul, hf.2] at hc
  have hl : 1 / (S.card : ℝ) ≤ ∑ x : S, f x ^ 4 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  rw [weightedEnergy_sidon hSidon, h2, h4]
  norm_num at hl ⊢
  linarith

/-- Every nonempty Sidon support has the exact norm 2-1/|S|, and the
uniform squared weight is an actual maximizing endpoint law. -/
theorem energyNorm_sidon {S : Finset G} (hS : S.Nonempty) (hSidon : HasSidonSums S) :
    energyNorm S = 2 - 1 / (S.card : ℝ) := by
  apply le_antisymm
  · obtain ⟨f, hf, hs, hE⟩ := energyNorm_attained hS
    rw [← hE]
    exact sidon_admissible_energy_upper hS hSidon ⟨hf, hs⟩
  · have h := energyNorm_ge_admissible (uniformEnergyWeight_admissible hS)
    rw [uniformEnergyWeight_energy, countingEnergy_sidon hSidon] at h
    have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
    have he : (2 * (S.card : ℝ) ^ 2 - S.card) / (S.card : ℝ) ^ 2 = 2 - 1 / S.card := by
      field_simp
    rwa [he] at h

theorem uniformEnergyWeight_maximizes_sidon {S : Finset G} (hS : S.Nonempty) (hSidon : HasSidonSums S) :
    weightedEnergy S (extendWeight S (uniformEnergyWeight S)) = energyNorm S := by
  rw [uniformEnergyWeight_energy, countingEnergy_sidon hSidon, energyNorm_sidon hS hSidon]
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  field_simp

theorem stationaryEnergyProfile_sidon_uniform {S : Finset G} (hS : S.Nonempty) (hSidon : HasSidonSums S) :
    stationaryEnergyProfile S (uniformReference S) = Real.log (2 - 1 / (S.card : ℝ)) := by
  have h := stationaryEnergyProfile_optimizer hS (uniformEnergyWeight_admissible hS)
    (uniformEnergyWeight_maximizes_sidon hS hSidon)
  simpa only [uniformEnergyWeight_sq, energyNorm_sidon hS hSidon] using h

theorem stationaryEnergyProfile_sidon_uniform_lt_log_two {S : Finset G}
    (hS : S.Nonempty) (hSidon : HasSidonSums S) :
    stationaryEnergyProfile S (uniformReference S) < Real.log 2 := by
  rw [stationaryEnergyProfile_sidon_uniform hS hSidon]
  have hp : 0 < 2 - 1 / (S.card : ℝ) := by
    rw [← energyNorm_sidon hS hSidon]
    exact energyNorm_pos hS
  apply Real.log_lt_log hp
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  linarith [one_div_pos.mpr hn]

end
end Erdos539Geometry
