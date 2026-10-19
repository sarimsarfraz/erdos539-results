/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpExponents

namespace Erdos539Geometry

/-- The scalar-base-2/3 split recursion in the stationary cut note. -/
def stationaryCutExponent : ℕ → ℚ
  | 0 => 0
  | 1 => 2 / 3
  | n + 2 => (Finset.univ : Finset (Fin (n + 1))).inf' Finset.univ_nonempty
      (fun i ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (n + 1 - i.val)))
termination_by d => d

@[simp] theorem stationaryCutExponent_zero : stationaryCutExponent 0 = 0 := stationaryCutExponent.eq_1
@[simp] theorem stationaryCutExponent_one : stationaryCutExponent 1 = 2 / 3 := stationaryCutExponent.eq_2

theorem stationaryCutExponent_rec (n : ℕ) :
    stationaryCutExponent (n + 2) = (Finset.univ : Finset (Fin (n + 1))).inf' Finset.univ_nonempty
      (fun i ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (n + 1 - i.val))) := stationaryCutExponent.eq_3 n

end Erdos539Geometry
