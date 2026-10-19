/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FourLeafCounts
import Erdos539.GluingMaxFan

namespace Erdos539Geometry
noncomputable section
open scoped Classical

theorem twoLeafTree_maxFan {T : ℕ} (hT : 0 < T) :
    maxFan (integerRealSet (twoLeafTree T (10 * T))) = T ^ 2 + (T - 1) * T := by
  rw [twoLeafTree, maxFan_symmetric_gluing (intervalVectors_nonempty hT) hT
    (by positivity) (coordinateGap_of_diameter (Int.natCast_nonneg T)
      (show 2 * (T : ℤ) < 10 * T by omega) (intervalVectors_diameter T)) (),
    maxFan_eq_card_one_dimensional (), integerRealSet_card, intervalVectors_card]

theorem fourLeafBranch_maxFan {T : ℕ} (hT : 0 < T) :
    maxFan (integerRealSet (fourLeafBranch T)) =
      (T ^ 2 + (T - 1) * T) ^ 2 + (T - 1) * T ^ 3 := by
  rw [fourLeafBranch_eq_tree, integerRealSet_reindex, maxFan_reindexRealSet,
    fourLeafTree, maxFan_symmetric_gluing (twoLeafTree_nonempty hT) hT
    (by positivity) (coordinateGap_of_diameter
      (show 0 ≤ (T : ℤ) + T * (10 * T) by positivity)
      (fourLeaf_child_separation hT) (twoLeafTree_diameter T)) (Sum.inl ()),
    twoLeafTree_maxFan hT, twoLeafTree_card hT]

/-- The exact fan polynomial of the literal seven-digit branch. -/
theorem fourLeafBranch_maxFan_polynomial {T : ℕ} (hT : 0 < T) :
    (maxFan (integerRealSet (fourLeafBranch T)) : ℝ) =
      5 * (T : ℝ) ^ 4 - 5 * (T : ℝ) ^ 3 + (T : ℝ) ^ 2 := by
  rw [fourLeafBranch_maxFan hT]
  push_cast [Nat.cast_sub (show 1 ≤ T from hT)]
  ring

theorem fourLeafBranch_maxFan_bounds {T : ℕ} (hT : 0 < T) :
    T ^ 4 ≤ maxFan (integerRealSet (fourLeafBranch T)) ∧
      maxFan (integerRealSet (fourLeafBranch T)) ≤ 5 * T ^ 4 := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have h := fourLeafBranch_maxFan_polynomial hT
  have ht1 : 0 ≤ (T : ℝ) - 1 := by linarith
  have ht4 : 0 ≤ 4 * (T : ℝ) - 1 := by linarith
  have ht5 : 0 ≤ 5 * (T : ℝ) - 1 := by linarith
  constructor
  · have h0 : 0 ≤ (T : ℝ) ^ 2 * ((T : ℝ) - 1) * (4 * (T : ℝ) - 1) := by positivity
    have : (T : ℝ) ^ 4 ≤ maxFan (integerRealSet (fourLeafBranch T)) := by nlinarith
    exact_mod_cast this
  · have h0 : 0 ≤ (T : ℝ) ^ 2 * (5 * (T : ℝ) - 1) := by positivity
    have : (maxFan (integerRealSet (fourLeafBranch T)) : ℝ) ≤ 5 * (T : ℝ) ^ 4 := by nlinarith
    exact_mod_cast this

end
end Erdos539Geometry
