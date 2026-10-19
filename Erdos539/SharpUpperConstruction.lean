/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PowerFamilies
import Erdos539.SharpExponents
import Erdos539.FixedDimension

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

theorem combineExponent_fraction {a₁ a₂ b₁ b₂ : ℕ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) :
    ((b₁ * a₂ + b₂ * a₁ : ℕ) : ℚ) /
        ((a₁ * a₂ + (b₁ * a₂ + b₂ * a₁) : ℕ) : ℚ) =
      combineExponent ((b₁ : ℚ) / a₁) ((b₂ : ℚ) / a₂) := by
  have h₁ : (0 : ℚ) < a₁ := by exact_mod_cast ha₁
  have h₂ : (0 : ℚ) < a₂ := by exact_mod_cast ha₂
  have hsum : (0 : ℚ) < (a₁ : ℚ) * a₂ + ((b₁ : ℚ) * a₂ + (b₂ : ℚ) * a₁) := by positivity
  unfold combineExponent
  push_cast
  field_simp
  ring

/-- The minimizing split recursion is realized by an actual family of finite
integer sets in every fixed positive dimension. -/
theorem exists_sharp_power_construction {d : ℕ} (hd : 0 < d) :
    ∃ a b : ℕ, 0 < a ∧ a ≤ 2 * b ∧ b ≤ a ∧
      (b : ℚ) / a = sharpExponent d ∧ HasPowerConstruction d a b := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hone : d = 1
    · subst d
      exact ⟨1, 1, by decide, by decide, by decide, by norm_num, hasPowerConstruction_one⟩
    · obtain ⟨p, s, hp, hs, he, hmin⟩ := sharpExponent_attained (by omega : 2 ≤ d)
      obtain ⟨a₁, b₁, ha₁, hhalf₁, hle₁, hratio₁, hF⟩ := ih p (by omega) hp
      obtain ⟨a₂, b₂, ha₂, hhalf₂, hle₂, hratio₂, hG⟩ := ih s (by omega) hs
      let A := a₁ * a₂
      let B := b₁ * a₂ + b₂ * a₁
      have hAB : A ≤ B := by
        have h₁ := Nat.mul_le_mul_right a₂ hhalf₁
        have h₂ := Nat.mul_le_mul_right a₁ hhalf₂
        dsimp only [A, B]
        nlinarith
      refine ⟨A + B, B, by dsimp only [A]; positivity, by omega, by omega, ?_, ?_⟩
      · rw [hmin, ← hratio₁, ← hratio₂]
        exact combineExponent_fraction ha₁ ha₂
      · rw [← he]
        exact hF.glue hp hG hAB

/-- The upper bound with the optimal recursive exponent holds for all n in
every fixed positive dimension. -/
theorem exists_sharp_upper_construction {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∃ F : Finset (Fin d → ℤ), F.card = n ∧
      ((integerPositiveDifferences F).card : ℝ) ≤ C * (n : ℝ) ^ (sharpExponent d : ℝ) := by
  obtain ⟨a, b, ha, _hhalf, _hle, hratio, C, hC, hfamily⟩ := exists_sharp_power_construction hd
  have hratio' : (b : ℝ) / a = (sharpExponent d : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun q : ℚ ↦ (q : ℝ)) hratio
  refine ⟨(C : ℝ) * 2 ^ b, by positivity, ?_⟩
  intro n hn
  have hf : ∀ W : ℕ, ∃ F : Finset (Fin d → ℤ), F.card = W ^ a ∧
      (integerPositiveDifferences F).card ≤ C * W ^ b := by
    intro W
    obtain ⟨F, hF, hD, _hΔ⟩ := hfamily W
    exact ⟨F, hF, hD⟩
  simpa only [hratio'] using interpolate_integer_construction ha hf hn

theorem fixedDimensionalMinimum_sharp_upper {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (fixedDimensionalMinimum d n : ℝ) ≤ C * (n : ℝ) ^ (sharpExponent d : ℝ) := by
  obtain ⟨C, hC, hfamily⟩ := exists_sharp_upper_construction hd
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨F, hF, hD⟩ := hfamily n hn
  have hm : (fixedDimensionalMinimum d n : ℝ) ≤ (integerPositiveDifferences F).card := by
    exact_mod_cast fixedDimensionalMinimum_le F hF
  exact hm.trans hD

end
end Erdos539Geometry
