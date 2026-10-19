/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyNormBasics

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem sum_weightedCorrelation (S : Finset G) (f g : G → ℝ) :
    ∑ z ∈ S - S, weightedCorrelation S f g z = (∑ x ∈ S, f x) * ∑ x ∈ S, g x := by
  calc
    _ = ∑ p ∈ S ×ˢ S, f p.1 * g p.2 := by
      refine @Finset.sum_fiberwise_of_maps_to (G × G) G ℝ _ (S ×ˢ S) (S - S)
        (Classical.decEq G) (fun p ↦ p.1 - p.2) ?_ _
      intro p hp
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
      exact Finset.mem_sub.mpr ⟨p.1, hx, p.2, hy, rfl⟩
    _ = _ := by rw [Finset.sum_product]; simp_rw [← Finset.mul_sum]; rw [← Finset.sum_mul]

/-- Cauchy-Schwarz on difference representations, for weighted inputs. -/
theorem sum_weight_fourth_le_difference_energy (S : Finset G) (f : G → ℝ) :
    (∑ x ∈ S, f x) ^ 4 ≤ (S - S).card * weightedEnergy S f := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (S - S) (fun _ ↦ (1 : ℝ)) (weightedCorrelation S f f)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [sum_weightedCorrelation] at h
  have he : (∑ z ∈ S - S, weightedCorrelation S f f z ^ 2) = weightedEnergy S f := by
    simpa only [differenceMixedEnergy, pow_two] using differenceMixedEnergy_self S f
  rw [he] at h
  convert h using 1
  ring

/-- The uniform normalized weight supplies the sharp elementary norm lower
bound using the ordinary difference count. -/
theorem card_sq_le_difference_mul_energyNorm {S : Finset G} (hS : S.Nonempty) :
    (S.card : ℝ) ^ 2 ≤ (S - S).card * energyNorm S := by
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hr : 0 < Real.sqrt (S.card : ℝ) := Real.sqrt_pos.mpr hn
  let c : ℝ := 1 / Real.sqrt (S.card : ℝ)
  let f : S → ℝ := fun _ ↦ c
  have hf : f ∈ admissibleWeights S := by
    refine ⟨fun _ ↦ by dsimp [f, c]; positivity, ?_⟩
    change (∑ _x : S, c ^ 2) = 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    dsimp [c]
    field_simp
    nlinarith [Real.sq_sqrt hn.le]
  have hsum : (∑ x ∈ S, extendWeight S f x) = (S.card : ℝ) * c := by
    rw [← Finset.sum_attach S]
    simp [f]
  have hNc : (S.card : ℝ) * c = Real.sqrt (S.card : ℝ) := by
    dsimp [c]
    rw [mul_one_div]
    apply (div_eq_iff hr.ne').mpr
    rw [← pow_two, Real.sq_sqrt hn.le]
  have hfour : (∑ x ∈ S, extendWeight S f x) ^ 4 = (S.card : ℝ) ^ 2 := by
    rw [hsum, hNc, show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt hn.le]
  have h := sum_weight_fourth_le_difference_energy S (extendWeight S f)
  rw [hfour] at h
  exact h.trans (mul_le_mul_of_nonneg_left (energyNorm_ge_admissible hf) (Nat.cast_nonneg _))

theorem energyNorm_ge_card_sq_div_difference {S : Finset G} (hS : S.Nonempty) :
    (S.card : ℝ) ^ 2 / (S - S).card ≤ energyNorm S := by
  obtain ⟨a, ha⟩ := hS
  have hz : (0 : G) ∈ S - S := Finset.mem_sub.mpr ⟨a, ha, a, ha, sub_self a⟩
  have hd : (0 : ℝ) < (S - S).card := by exact_mod_cast Finset.card_pos.mpr ⟨0, hz⟩
  exact (div_le_iff₀ hd).mpr (by simpa only [mul_comm] using
    card_sq_le_difference_mul_energyNorm ⟨a, ha⟩)

theorem energyNorm_ge_of_difference_doubling {S : Finset G} (hS : S.Nonempty)
    {K : ℝ} (hK : 0 < K) (hD : ((S - S).card : ℝ) ≤ K * S.card) :
    (S.card : ℝ) / K ≤ energyNorm S := by
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have h := card_sq_le_difference_mul_energyNorm hS
  have hm := mul_le_mul_of_nonneg_right hD (energyNorm_nonneg S)
  apply (div_le_iff₀ hK).mpr
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

end
end Erdos539Geometry
