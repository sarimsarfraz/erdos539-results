/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntervalConstruction
import Erdos539.IntegerReindex
import Mathlib.Data.Fintype.Sum

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι κ : Type*}

/-- Finite coordinate sets always admit a separated layered gluing. -/
theorem exists_gluing [Fintype ι] [Fintype κ]
    (F : Finset (ι → ℤ)) (G : Finset (κ → ℤ)) (K : ℕ) (i : ι) :
    ∃ H : Finset (ι ⊕ κ → ℤ),
      H.card = K * F.card * G.card ∧
      (integerPositiveDifferences H).card ≤
        (integerPositiveDifferences F).card * (integerPositiveDifferences G).card +
        (K - 1) * ((integerDifferences F).card + (integerDifferences G).card) ∧
      (integerDifferences H).card ≤
        (2 * K - 1) * (integerDifferences F).card * (integerDifferences G).card := by
  obtain ⟨M₁, hM₁, hF⟩ := exists_coordinate_gap F
  obtain ⟨M₂, _hM₂, hG⟩ := exists_coordinate_gap G
  let M := max M₁ M₂
  have hM : 0 < M := hM₁.trans_le (le_max_left _ _)
  have hF' : HasCoordinateGap F M := fun x hx y hy i ↦ (hF x hx y hy i).trans_le (le_max_left _ _)
  have hG' : HasCoordinateGap G M := fun x hx y hy i ↦ (hG x hx y hy i).trans_le (le_max_right _ _)
  exact ⟨gluing F G K M, gluing_card G K hM hF' i,
    gluing_integerPositiveDifferences_card_le K hM hF' hG',
    gluing_integerDifferences_card_le F G K M⟩

/-- The planar layered family has W cubed points and at most 5 W squared
positive differences, with linear ordinary-difference growth. -/
theorem exists_planar_power_construction (W : ℕ) :
    ∃ F : Finset (Unit ⊕ Unit → ℤ), F.card = W ^ 3 ∧
      (integerPositiveDifferences F).card ≤ 5 * W ^ 2 ∧
      (integerDifferences F).card ≤ 8 * W ^ 3 := by
  let I := intervalVectors W
  obtain ⟨F, hcard, hpos, hdiff⟩ := exists_gluing I I W ()
  have hI : I.card = W := intervalVectors_card W
  have hD : (integerPositiveDifferences I).card ≤ W := intervalVectors_posDiff_card_le W
  have hΔ : (integerDifferences I).card ≤ 2 * W := intervalVectors_differences_card_le W
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [hcard, hI]
    ring
  · calc
      _ ≤ _ := hpos
      _ ≤ W * W + W * (2 * W + 2 * W) :=
        Nat.add_le_add (Nat.mul_le_mul hD hD)
          (Nat.mul_le_mul (Nat.sub_le W 1) (Nat.add_le_add hΔ hΔ))
      _ = _ := by ring
  · calc
      _ ≤ _ := hdiff
      _ ≤ (2 * W) * (2 * W) * (2 * W) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le (2 * W) 1) hΔ) hΔ
      _ = _ := by ring

/-- A concrete three-dimensional family with W to the eighth points and
at most 15 W to the fifth positive differences. -/
theorem exists_three_dimensional_power_construction (W : ℕ) :
    ∃ F : Finset (Fin 3 → ℤ), F.card = W ^ 8 ∧
      (integerPositiveDifferences F).card ≤ 15 * W ^ 5 ∧
      (integerDifferences F).card ≤ 32 * W ^ 8 := by
  classical
  obtain ⟨G, hG, hDG, hΔG⟩ := exists_planar_power_construction W
  let I := intervalVectors (W ^ 3)
  obtain ⟨H, hcard, hpos, hdiff⟩ := exists_gluing I G (W ^ 2) ()
  have hI : I.card = W ^ 3 := intervalVectors_card _
  have hD : (integerPositiveDifferences I).card ≤ W ^ 3 := intervalVectors_posDiff_card_le _
  have hΔ : (integerDifferences I).card ≤ 2 * W ^ 3 := intervalVectors_differences_card_le _
  let e : (Unit ⊕ (Unit ⊕ Unit)) ≃ Fin 3 := Fintype.equivOfCardEq (by simp)
  refine ⟨H.image (reindexInteger e), ?_, ?_, ?_⟩
  · rw [reindexInteger_card, hcard, hI, hG]
    ring
  · rw [integerPositiveDifferences_reindex_card]
    calc
      _ ≤ _ := hpos
      _ ≤ W ^ 3 * (5 * W ^ 2) + W ^ 2 * (2 * W ^ 3 + 8 * W ^ 3) :=
        Nat.add_le_add (Nat.mul_le_mul hD hDG)
          (Nat.mul_le_mul (Nat.sub_le (W ^ 2) 1) (Nat.add_le_add hΔ hΔG))
      _ = _ := by ring
  · rw [integerDifferences_reindex_card]
    calc
      _ ≤ _ := hdiff
      _ ≤ (2 * W ^ 2) * (2 * W ^ 3) * (8 * W ^ 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le (2 * W ^ 2) 1) hΔ) hΔG
      _ = _ := by ring

end
end Erdos539Geometry
