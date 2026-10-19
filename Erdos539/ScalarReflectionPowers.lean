/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarRadixEmbedding
import Erdos539.ReflectionCounterexampleExcess

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical

/-- The actual base-1000 encoding of independent copies of the seventy
digits, always as a finite subset of one scalar integer coordinate. -/
def scalarReflectionPower : ℕ → Finset ℤ
  | 0 => {0}
  | n + 1 => (scalarReflectionPower n ×ˢ reflectionCounterexample).image (scalarRadixMap (1000 ^ n))

theorem scalarReflectionPower_nonempty (n : ℕ) : (scalarReflectionPower n).Nonempty := by
  induction n with
  | zero => exact Finset.singleton_nonempty _
  | succ n ih =>
    exact (ih.product (show reflectionCounterexample.Nonempty from ⟨0, by decide +kernel⟩)).image _

/-- Twice every encoded point lies strictly below the next radix. Thus
even pair sums have no carries into the next digit. -/
theorem scalarReflectionPower_bounds (n : ℕ) :
    ∀ a ∈ scalarReflectionPower n, 0 ≤ a ∧ 2 * a < (1000 : ℤ) ^ n := by
  induction n with
  | zero => simp [scalarReflectionPower]
  | succ n ih =>
    intro x hx
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    have ha' := ih a ha
    have hb' := reflectionCounterexample_bounds b hb
    have hm : (0 : ℤ) < 1000 ^ n := pow_pos (by norm_num) _
    have hbm := mul_le_mul_of_nonneg_left (show 2 * b ≤ 386 by omega) hm.le
    change 0 ≤ a + 1000 ^ n * b ∧ 2 * (a + 1000 ^ n * b) < 1000 ^ (n + 1)
    rw [pow_succ]
    constructor
    · exact add_nonneg ha'.1 (mul_nonneg hm.le hb'.1)
    · nlinarith

theorem scalarReflectionPower_injections (n : ℕ) :
    Set.InjOn (scalarRadixMap ((1000 : ℤ) ^ n))
      (↑(scalarReflectionPower n ×ˢ reflectionCounterexample) : Set (ℤ × ℤ)) ∧
    Set.InjOn (scalarRadixMap ((1000 : ℤ) ^ n))
      (↑((scalarReflectionPower n ×ˢ reflectionCounterexample) +
        (scalarReflectionPower n ×ˢ reflectionCounterexample)) : Set (ℤ × ℤ)) :=
  scalarRadixMap_injOn_support_and_sums (pow_pos (by norm_num) _) (scalarReflectionPower_bounds n)

theorem scalarReflectionPower_card (n : ℕ) : (scalarReflectionPower n).card = 70 ^ n := by
  induction n with
  | zero => simp [scalarReflectionPower]
  | succ n ih =>
    rw [scalarReflectionPower, Finset.card_image_of_injOn (scalarReflectionPower_injections n).1,
      Finset.card_product, ih, reflectionCounterexample_card, pow_succ]

theorem countingEnergy_zero_singleton : countingEnergy ({0} : Finset ℤ) = 1 := by
  have hb : ∀ a ∈ ({0} : Finset ℤ), 0 ≤ a ∧ 2 * a < (1 : ℤ) := by simp
  have he : integerIntervalEnergy ({0} : Finset ℤ) 1 = 1 := by decide +kernel
  rw [← integerIntervalEnergy_eq_counting _ 1 hb, he]
  norm_num

theorem scalarReflectionPower_energy (n : ℕ) : countingEnergy (scalarReflectionPower n) = (83610 : ℝ) ^ n := by
  induction n with
  | zero => simpa only [scalarReflectionPower, pow_zero] using countingEnergy_zero_singleton
  | succ n ih =>
    rw [scalarReflectionPower, countingEnergy_image_of_sum_injective _ _
      (scalarReflectionPower_injections n).1 (scalarReflectionPower_injections n).2,
      countingEnergy_product, ih, reflectionCounterexample_energy, pow_succ]

theorem scalarReflectionPower_countingDefect (n : ℕ) :
    countingDefect (scalarReflectionPower n) = n * countingDefect reflectionCounterexample := by
  induction n with
  | zero => simp [countingDefect, scalarReflectionPower_card, scalarReflectionPower_energy]
  | succ n ih =>
    rw [scalarReflectionPower, countingDefect_image_of_sum_injective _ _
      (scalarReflectionPower_injections n).1 (scalarReflectionPower_injections n).2,
      countingDefect_product (scalarReflectionPower_nonempty n)
        (show reflectionCounterexample.Nonempty from ⟨0, by decide +kernel⟩), ih]
    push_cast
    ring

theorem scalarReflectionPower_reflectedMean (n : ℕ) :
    reflectedMeanCountingDefect (scalarReflectionPower n) = n * reflectedMeanCountingDefect reflectionCounterexample := by
  induction n with
  | zero =>
    have hr : reflectedSupport ({0} : Finset ℤ) 0 = {0} := by
      ext x
      simp [reflectedSupport]
    simp only [scalarReflectionPower, Nat.cast_zero, reflectedMeanCountingDefect, Finset.singleton_add_singleton, zero_add,
      Finset.sum_singleton, hr, Finset.card_singleton, Nat.cast_one, one_pow,
      countingEnergy_zero_singleton, div_self (by norm_num : (1 : ℝ) ≠ 0),
      Real.log_one, mul_zero, zero_mul]
  | succ n ih =>
    rw [scalarReflectionPower, reflectedMeanCountingDefect_image_of_sum_injective _ _
      (scalarReflectionPower_injections n).1 (scalarReflectionPower_injections n).2,
      reflectedMeanCountingDefect_product (scalarReflectionPower_nonempty n)
        (show reflectionCounterexample.Nonempty from ⟨0, by decide +kernel⟩), ih]
    push_cast
    ring

end
end Erdos539Geometry
