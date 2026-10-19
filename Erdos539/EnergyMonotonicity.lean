/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedEnergyRoot

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem weightedEnergy_mono (S : Finset G) {f g : G → ℝ}
    (hf : ∀ x ∈ S, 0 ≤ f x) (hfg : ∀ x ∈ S, f x ≤ g x) :
    weightedEnergy S f ≤ weightedEnergy S g := by
  rw [weightedEnergy_eq_quadruples, weightedEnergy_eq_quadruples]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
  split_ifs
  · exact mul_le_mul
      (mul_le_mul (hfg _ hp1) (hfg _ hp2) (hf _ hp2) ((hf _ hp1).trans (hfg _ hp1)))
      (mul_le_mul (hfg _ hq1) (hfg _ hq2) (hf _ hq2) ((hf _ hq1).trans (hfg _ hq1)))
      (mul_nonneg (hf _ hq1) (hf _ hq2))
      (mul_nonneg ((hf _ hp1).trans (hfg _ hp1)) ((hf _ hp2).trans (hfg _ hp2)))
  · rfl

/-- Deleting a part with at most one sixteenth of the energy leaves at
least one sixteenth in the other part. This uses the actual fourth-root
triangle inequality, not a probability-mass estimate. -/
theorem weightedEnergy_split_retention (S : Finset G) (f g : G → ℝ)
    (hbad : weightedEnergy S f ≤ weightedEnergy S (f + g) / 16) :
    weightedEnergy S (f + g) / 16 ≤ weightedEnergy S g := by
  have hf0 := energyFourthRoot_nonneg S f
  have hg0 := energyFourthRoot_nonneg S g
  have hsum0 := energyFourthRoot_nonneg S (f + g)
  have hfhalf : energyFourthRoot S f ≤ energyFourthRoot S (f + g) / 2 := by
    apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity)
    rw [energyFourthRoot_pow_four, div_pow, energyFourthRoot_pow_four]
    norm_num
    exact hbad
  have htri := energyFourthRoot_add_le S f g
  have hgood : energyFourthRoot S (f + g) / 2 ≤ energyFourthRoot S g := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ energyFourthRoot S (f + g) / 2) hgood 4
  rw [div_pow, energyFourthRoot_pow_four, energyFourthRoot_pow_four] at hp
  norm_num at hp
  exact hp

/-- Mixed-energy Holder with a common fiber-norm bound and four arbitrary
row masses. The weights themselves may be signed. -/
theorem mixedWeightedEnergy_le_common_bound (S : Finset G) (f g h k : G → ℝ)
    {M a b c d : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hf : weightedEnergy S f ≤ M * a ^ 4) (hg : weightedEnergy S g ≤ M * b ^ 4)
    (hh : weightedEnergy S h ≤ M * c ^ 4) (hk : weightedEnergy S k ≤ M * d ^ 4) :
    mixedWeightedEnergy S f g h k ≤ M * a * b * c * d := by
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity)
  have hfg := mul_le_mul hf hg (weightedEnergy_nonneg S g) (by positivity : 0 ≤ M * a ^ 4)
  have hfgh := mul_le_mul hfg hh (weightedEnergy_nonneg S h)
    (by positivity : 0 ≤ (M * a ^ 4) * (M * b ^ 4))
  have hall := mul_le_mul hfgh hk (weightedEnergy_nonneg S k)
    (by positivity : 0 ≤ (M * a ^ 4) * (M * b ^ 4) * (M * c ^ 4))
  have hholder := (mixedWeightedEnergy_fourth_le S f g h k).trans hall
  convert hholder using 1
  ring

end
end Erdos539Geometry
