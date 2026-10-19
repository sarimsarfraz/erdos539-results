/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FourLeafTreeModel
import Erdos539.GluingDiameter

namespace Erdos539Geometry
noncomputable section
open scoped Classical

theorem intervalVectors_nonempty {T : ℕ} (hT : 0 < T) : (intervalVectors T).Nonempty := by
  apply Finset.card_pos.mp
  rwa [intervalVectors_card]

theorem twoLeafTree_diameter (T : ℕ) :
    ∀ x ∈ twoLeafTree T (10 * T), ∀ y ∈ twoLeafTree T (10 * T), ∀ i,
      |x i - y i| ≤ (T : ℤ) + T * (10 * T) :=
  gluing_diameter (by positivity) T (intervalVectors_diameter T) (intervalVectors_diameter T)

theorem fourLeaf_child_separation {T : ℕ} (hT : 0 < T) :
    2 * ((T : ℤ) + T * (10 * T)) < (10 * T) ^ 2 := by
  have ht : (1 : ℤ) ≤ T := by exact_mod_cast hT
  nlinarith

theorem twoLeafTree_card {T : ℕ} (hT : 0 < T) :
    (twoLeafTree T (10 * T)).card = T ^ 3 := by
  have hgap := coordinateGap_of_diameter (Int.natCast_nonneg T)
    (show 2 * (T : ℤ) < 10 * T by omega) (intervalVectors_diameter T)
  rw [twoLeafTree, gluing_card _ _ (by positivity) hgap (), intervalVectors_card]
  ring

theorem twoLeafTree_nonempty {T : ℕ} (hT : 0 < T) :
    (twoLeafTree T (10 * T)).Nonempty := by
  apply Finset.card_pos.mp
  rw [twoLeafTree_card hT]
  positivity

theorem twoLeafTree_palette {T : ℕ} (hT : 0 < T) :
    (integerPositiveDifferences (twoLeafTree T (10 * T))).card =
      T ^ 2 + 2 * (T - 1) * (2 * T - 1) := by
  rw [twoLeafTree, gluing_integerPositiveDifferences_card_eq
    (intervalVectors_nonempty hT) (intervalVectors_nonempty hT) hT
    (Int.natCast_nonneg T) (show 2 * (T : ℤ) < 10 * T by omega)
    (intervalVectors_diameter T) (intervalVectors_diameter T) () (),
    intervalVectors_posDiff_card_eq hT, intervalVectors_differences_card_eq]
  ring

theorem twoLeafTree_differences {T : ℕ} (hT : 0 < T) :
    (integerDifferences (twoLeafTree T (10 * T))).card = (2 * T - 1) ^ 3 := by
  rw [twoLeafTree, gluing_integerDifferences_card_eq_of_diameter _ _
    (Int.natCast_nonneg T) (show 2 * (T : ℤ) < 10 * T by omega)
    (intervalVectors_diameter T) (), intervalVectors_differences_card_eq]
  ring

theorem fourLeafBranch_palette {T : ℕ} (hT : 0 < T) :
    (integerPositiveDifferences (fourLeafBranch T)).card =
      (T ^ 2 + 2 * (T - 1) * (2 * T - 1)) ^ 2 +
        2 * (T - 1) * (2 * T - 1) ^ 3 := by
  rw [fourLeafBranch_eq_tree, integerPositiveDifferences_reindex_card,
    fourLeafTree, gluing_integerPositiveDifferences_card_eq
    (twoLeafTree_nonempty hT) (twoLeafTree_nonempty hT) hT
    (show 0 ≤ (T : ℤ) + T * (10 * T) by positivity) (fourLeaf_child_separation hT)
    (twoLeafTree_diameter T) (twoLeafTree_diameter T) (Sum.inl ()) (Sum.inl ()),
    twoLeafTree_palette hT, twoLeafTree_differences hT]
  ring

theorem fourLeafBranch_differences {T : ℕ} (hT : 0 < T) :
    (integerDifferences (fourLeafBranch T)).card = (2 * T - 1) ^ 7 := by
  rw [fourLeafBranch_eq_tree, integerDifferences_reindex_card,
    fourLeafTree, gluing_integerDifferences_card_eq_of_diameter _ _
    (show 0 ≤ (T : ℤ) + T * (10 * T) by positivity) (fourLeaf_child_separation hT)
    (twoLeafTree_diameter T) (Sum.inl ()), twoLeafTree_differences hT]
  ring

theorem fourLeafBranch_palette_le {T : ℕ} (hT : 0 < T) :
    (integerPositiveDifferences (fourLeafBranch T)).card ≤ 41 * T ^ 4 := by
  rw [fourLeafBranch_palette hT]
  have ha : T ^ 2 + 2 * (T - 1) * (2 * T - 1) ≤ 5 * T ^ 2 := by
    have := Nat.mul_le_mul (Nat.sub_le T 1) (Nat.sub_le (2 * T) 1)
    nlinarith
  have hb : (2 * T - 1) ^ 3 ≤ 8 * T ^ 3 := by
    have := Nat.pow_le_pow_left (Nat.sub_le (2 * T) 1) 3
    nlinarith
  have hc := Nat.pow_le_pow_left ha 2
  have hd := Nat.mul_le_mul (Nat.sub_le T 1) hb
  nlinarith

end
end Erdos539Geometry
