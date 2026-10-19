/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProductNorm

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
local instance binaryIntDecidableEq : DecidableEq ℤ := Classical.decEq _

/-- The literal two-point energy, with no normalization assumption. -/
theorem weightedEnergy_binary (f : ℤ → ℝ) :
    weightedEnergy {0, 1} f = f 0 ^ 4 + 4 * f 0 ^ 2 * f 1 ^ 2 + f 1 ^ 4 := by
  norm_num [weightedEnergy_eq_four_sum]
  ring

/-- The two-point optimizer has exact norm 3/2. -/
theorem energyNorm_binary : energyNorm ({0, 1} : Finset ℤ) = 3 / 2 := by
  apply le_antisymm
  · obtain ⟨f, _, hunit, hE⟩ := energyNorm_attained
      (show ({0, 1} : Finset ℤ).Nonempty from ⟨0, by simp⟩)
    let w := extendWeight ({0, 1} : Finset ℤ) f
    have hs : w 0 ^ 2 + w 1 ^ 2 = 1 := by
      have h := weightSquareSum_extend ({0, 1} : Finset ℤ) f
      simpa only [weightSquareSum, Finset.sum_pair (by norm_num : (0 : ℤ) ≠ 1), hunit] using h
    rw [← hE, weightedEnergy_binary]
    change w 0 ^ 4 + 4 * w 0 ^ 2 * w 1 ^ 2 + w 1 ^ 4 ≤ 3 / 2
    nlinarith [sq_nonneg (w 0 ^ 2 - w 1 ^ 2), congrArg (fun x : ℝ ↦ x ^ 2) hs]
  · have h := weightedEnergy_le_norm_squareSum ({0, 1} : Finset ℤ) (fun _ ↦ 1)
    norm_num [weightedEnergy_binary, weightSquareSum] at h
    linarith

/-- Nested products provide the Boolean cube without changing ambient
coordinate type during a proof. The zero-dimensional cube is a singleton. -/
@[reducible] def BinaryAmbient : ℕ → Type
  | 0 => ℤ
  | n + 1 => ℤ × BinaryAmbient n

@[reducible] instance binaryAmbientAddCommGroup (n : ℕ) : AddCommGroup (BinaryAmbient n) := by
  induction n with
  | zero => exact inferInstanceAs (AddCommGroup ℤ)
  | succ n ih => exact @Prod.instAddCommGroup ℤ (BinaryAmbient n) _ ih

def binaryCube : (n : ℕ) → Finset (BinaryAmbient n)
  | 0 => {0}
  | n + 1 => ({0, 1} : Finset ℤ) ×ˢ binaryCube n

@[simp] theorem binaryCube_nonempty (n : ℕ) : (binaryCube n).Nonempty := by
  induction n with
  | zero => exact Finset.singleton_nonempty 0
  | succ n ih => exact (show ({0, 1} : Finset ℤ).Nonempty from ⟨0, by simp⟩).product ih

@[simp] theorem binaryCube_card (n : ℕ) : (binaryCube n).card = 2 ^ n := by
  induction n with
  | zero => simp [binaryCube]
  | succ n ih =>
    change (({0, 1} : Finset ℤ) ×ˢ binaryCube n).card = 2 ^ (n + 1)
    rw [Finset.card_product, ih]
    norm_num [pow_succ, Nat.mul_comm]

@[simp] theorem energyNorm_binaryCube (n : ℕ) : energyNorm (binaryCube n) = (3 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp [binaryCube]
  | succ n ih =>
    have hh := @energyNorm_product ℤ (BinaryAmbient n) _ binaryIntDecidableEq _
      (Classical.decEq _) ({0, 1} : Finset ℤ) (binaryCube n)
    have hdec : @instDecidableEqProd ℤ (BinaryAmbient n) binaryIntDecidableEq
        (Classical.decEq _) = Classical.decEq (ℤ × BinaryAmbient n) := Subsingleton.elim _ _
    rw [hdec] at hh
    rw [energyNorm_binary, ih] at hh
    simpa only [binaryCube, pow_succ, mul_comm] using hh

end
end Erdos539Geometry
