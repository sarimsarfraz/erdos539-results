/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.LayerPowerFamilies
import Erdos539.SharpUpperConstruction

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

/-- The minimizing split recursion is realized by an actual family of finite
integer sets in every fixed positive dimension. -/
theorem exists_sharp_layer_power_construction {d : ℕ} (hd : 0 < d) :
    ∃ a b : ℕ, 0 < a ∧ a ≤ 2 * b ∧ b ≤ a ∧
      (b : ℚ) / a = sharpExponent d ∧ HasLayerPowerConstruction d a b := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hone : d = 1
    · subst d
      exact ⟨1, 1, by decide, by decide, by decide, by norm_num, hasLayerPowerConstruction_one⟩
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


theorem integerRealSet_card {ι : Type} (F : Finset (ι → ℤ)) :
    (integerRealSet F).card = F.card := integerToReal_image_card F

theorem posDiff_integerRealSet_card {ι : Type} (F : Finset (ι → ℤ)) :
    (posDiff (integerRealSet F)).card = (integerPositiveDifferences F).card :=
  posDiff_integerToReal_card F

/-- Sharpness inside the recursive layer class itself: arbitrarily large
actual members attain the sharp upper exponent with an explicit exponential-in-d constant. -/
theorem exists_arbitrarily_large_sharp_layer_set_explicit {d : ℕ} (hd : 0 < d) :
    ∀ N : ℕ, ∃ S : Finset (Fin d → ℝ),
      LayerConstructible (Fin d) S ∧ N ≤ S.card ∧ S.Nonempty ∧
        ((posDiff S).card : ℝ) ≤ (8 : ℝ) ^ d * (S.card : ℝ) ^ (sharpExponent d : ℝ) := by
  obtain ⟨a, b, ha, _hhalf, _hle, hratio, C, _hC, hcap, hfamily⟩ := exists_sharp_layer_power_construction hd
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hratio' : (b : ℝ) / a = (sharpExponent d : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun q : ℚ ↦ (q : ℝ)) hratio
  have hprod : (a : ℝ) * (sharpExponent d : ℝ) = b := by
    rw [← hratio']
    field_simp
  intro N
  let W := N + 1
  have hW : 0 < W := by dsimp only [W]; omega
  obtain ⟨F, hF, hD, _hΔ, hCF⟩ := hfamily W hW
  have hn : N ≤ F.card := by
    rw [hF]
    have hh : W ≤ W ^ a := by simpa only [pow_one] using Nat.pow_le_pow_right hW ha
    exact (Nat.le_succ N).trans hh
  have hFn : F.Nonempty := Finset.card_pos.mp (by rw [hF]; exact pow_pos hW _)
  have hpow : ((W ^ a : ℕ) : ℝ) ^ (sharpExponent d : ℝ) = (W : ℝ) ^ b := by
    calc
      _ = ((W : ℝ) ^ (a : ℝ)) ^ (sharpExponent d : ℝ) := by rw [Real.rpow_natCast, Nat.cast_pow]
      _ = (W : ℝ) ^ ((a : ℝ) * (sharpExponent d : ℝ)) := (Real.rpow_mul (Nat.cast_nonneg _) _ _).symm
      _ = _ := by rw [hprod, Real.rpow_natCast]
  refine ⟨integerRealSet F, hCF, ?_, integerRealSet_nonempty hFn, ?_⟩
  · simpa only [integerRealSet_card] using hn
  · rw [posDiff_integerRealSet_card, integerRealSet_card, hF, hpow]
    have hC : C ≤ 8 ^ d := (by omega : C ≤ 4 * C).trans hcap
    exact_mod_cast hD.trans (Nat.mul_le_mul_right _ hC)

/-- The same sharpness result with an existential dimension-dependent constant. -/
theorem exists_arbitrarily_large_sharp_layer_set {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ S : Finset (Fin d → ℝ),
      LayerConstructible (Fin d) S ∧ N ≤ S.card ∧ S.Nonempty ∧
        ((posDiff S).card : ℝ) ≤ C * (S.card : ℝ) ^ (sharpExponent d : ℝ) := by
  exact ⟨8 ^ d, by positivity, exists_arbitrarily_large_sharp_layer_set_explicit hd⟩

end
end Erdos539Geometry
