/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntegerCountingCertificate

namespace Erdos539Geometry

def reflectionCounterexampleList : List ℤ :=
  [0, 5, 6, 7, 11, 12, 13, 14, 15, 19, 20, 28, 29, 35, 37, 40, 43, 45, 46, 47, 56, 59, 62, 64, 73, 74, 75, 80, 82, 85, 89, 90, 97, 99, 103, 105, 106, 107, 108, 109, 111, 113, 120, 122, 126, 127, 130, 132, 135, 142, 143, 147, 148, 151, 153, 155, 156, 162, 163, 165, 171, 173, 175, 178, 182, 185, 187, 189, 191, 193]

theorem reflectionCounterexampleList_nodup : reflectionCounterexampleList.Nodup := by decide +kernel

/-- The literal seventy-point scalar example from the captured source. -/
def reflectionCounterexample : Finset ℤ :=
  ⟨reflectionCounterexampleList, reflectionCounterexampleList_nodup⟩

theorem reflectionCounterexample_eq_toFinset :
    reflectionCounterexample = reflectionCounterexampleList.toFinset := by
  ext a
  simp [reflectionCounterexample]

theorem reflectionCounterexample_card : reflectionCounterexample.card = 70 := by decide +kernel

theorem reflectionCounterexample_bounds :
    ∀ a ∈ reflectionCounterexample, 0 ≤ a ∧ 2 * a < (387 : ℤ) := by decide +kernel

end Erdos539Geometry
