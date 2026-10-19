/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13MaskSets
import Erdos539.PG13DigitSupport
import Mathlib.Data.Nat.Bitwise

namespace Erdos539Geometry

theorem pg13_and_nonzero_iff (m : Fin 8192) (s : ℕ) :
    m.val &&& s ≠ 0 ↔ ∃ i : Fin 13, i ∈ pg13MaskSet m ∧ s.testBit i.val = true := by
  constructor
  · intro hn
    by_contra hh
    apply hn
    apply Nat.zero_of_testBit_eq_false
    intro k
    rw [Nat.testBit_and]
    by_cases hk : k < 13
    · have hnot : ¬(m.val.testBit k = true ∧ s.testBit k = true) := by
        intro hb
        exact hh ⟨⟨k, hk⟩, by simpa [pg13MaskSet] using hb.1, hb.2⟩
      cases hm : m.val.testBit k <;> cases hs : s.testBit k <;> simp_all
    · have hm : m.val.testBit k = false := Nat.testBit_eq_false_of_lt
        (m.isLt.trans_le (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 13 ≤ k)))
      simp [hm]
  · rintro ⟨i, hi, hs⟩ he
    have hm : m.val.testBit i.val = true := by simpa [pg13MaskSet] using hi
    have hbit : (m.val &&& s).testBit i.val = true := by simp [Nat.testBit_and, hm, hs]
    simp [he] at hbit

theorem pg13_support_mask_meets (m : Fin 8192) (l : Fin 13) (d : Fin 7) :
    m.val &&& pg13SupportMask l d ≠ 0 ↔
      ∃ j ∈ pg13MaskSet m, j ∈ pg13DigitSupport l d := by
  rw [pg13_and_nonzero_iff]
  simp only [pg13_digit_support_certificate.1, decide_eq_true_eq]

end Erdos539Geometry
