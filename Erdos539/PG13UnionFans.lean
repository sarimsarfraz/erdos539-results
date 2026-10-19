/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13CrossFans

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

set_option maxHeartbeats 800000 in
theorem pg13Union_fan_card {T : ℕ} (hT : 0 < T) {l : Fin 13}
    {a : Fin 13 → ℤ} (ha : a ∈ pg13Branch T l) :
    (integerFan (pg13Union T) a).card ≤
      maxFan (integerRealSet (fourLeafBranch T)) + 12 * T ^ 3 := by
  have hterm (m : Fin 13) : (integerFan (pg13Branch T m) a).card ≤
      if m = l then maxFan (integerRealSet (fourLeafBranch T)) else T ^ 3 := by
    by_cases hm : m = l
    · subst m
      rw [if_pos rfl, ← fan_integerRealSet_card]
      have h := card_fan_le_maxFan (mem_integerRealSet.mpr ⟨a, ha, rfl⟩)
      rwa [pg13Branch_maxFan] at h
    · rw [if_neg hm]
      exact pg13_cross_fan_card hT (Ne.symm hm) ha
  calc
    (integerFan (pg13Union T) a).card ≤ ∑ m : Fin 13, (integerFan (pg13Branch T m) a).card :=
      integerFan_biUnion_le Finset.univ (pg13Branch T) a
    _ ≤ ∑ m : Fin 13, if m = l then maxFan (integerRealSet (fourLeafBranch T)) else T ^ 3 :=
      Finset.sum_le_sum (fun m _ ↦ hterm m)
    _ = maxFan (integerRealSet (fourLeafBranch T)) + 12 * T ^ 3 := by
      rw [Finset.sum_ite]
      simp [Finset.filter_eq', Finset.filter_ne']

theorem pg13Union_maxFan_bound {T : ℕ} (hT : 0 < T) :
    maxFan (integerRealSet (pg13Union T)) ≤
      maxFan (integerRealSet (fourLeafBranch T)) + 12 * T ^ 3 := by
  apply Finset.sup_le
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_integerRealSet.mp hx
  obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp ha
  rw [fan_integerRealSet_card]
  exact pg13Union_fan_card hT hl

/-- The actual thirteen-coordinate integer union satisfies the stated
uniform maximum-fan bound for every T>=2. -/
theorem pg13Union_maxFan_le {T : ℕ} (hT : 2 ≤ T) :
    maxFan (integerRealSet (pg13Union T)) ≤ 11 * T ^ 4 := by
  have hp : 0 < T := by omega
  have hf := pg13Union_maxFan_bound hp
  have hb := (fourLeafBranch_maxFan_bounds hp).2
  have ht : 12 * T ^ 3 ≤ 6 * T ^ 4 := by
    have hh := Nat.mul_le_mul_right (T ^ 3) hT
    nlinarith
  omega

end
end Erdos539Geometry
