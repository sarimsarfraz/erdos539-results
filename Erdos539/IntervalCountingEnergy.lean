/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntegerCountingCertificate
import Erdos539.UniformEnergyWeight

namespace Erdos539Geometry
open scoped BigOperators Pointwise

noncomputable def scalarInterval (n : ℕ) : Finset ℤ := Finset.Ico 0 n

theorem scalarInterval_card (n : ℕ) : (scalarInterval n).card = n := by
  simp [scalarInterval]

theorem scalarInterval_nonempty {n : ℕ} (hn : 0 < n) : (scalarInterval n).Nonempty := by
  exact ⟨0, by simp [scalarInterval, hn]⟩

theorem scalarInterval_reflection_low (n w : ℕ) (hw : w < n) :
    integerReflection (scalarInterval n) w = Finset.Icc (0 : ℤ) w := by
  ext a
  simp only [integerReflection, Finset.mem_filter, scalarInterval, Finset.mem_Ico, Finset.mem_Icc]
  omega

theorem scalarInterval_reflection_high (n w : ℕ) :
    integerReflection (scalarInterval n) (n + w) = Finset.Icc ((w : ℤ) + 1) (n - 1) := by
  ext a
  simp only [integerReflection, Finset.mem_filter, scalarInterval, Finset.mem_Ico, Finset.mem_Icc]
  omega

theorem scalarInterval_reflection_low_card (n w : ℕ) (hw : w < n) :
    (integerReflection (scalarInterval n) w).card = w + 1 := by
  rw [scalarInterval_reflection_low n w hw]
  simp

theorem scalarInterval_reflection_high_card (n w : ℕ) (hw : w < n) :
    (integerReflection (scalarInterval n) (n + w)).card = n - 1 - w := by
  rw [scalarInterval_reflection_high n w, Int.card_Icc]
  omega

private theorem scalarInterval_square_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, (((i : ℝ) + 1) ^ 2 + (i : ℝ) ^ 2)) =
      (n : ℝ) * (2 * (n : ℝ) ^ 2 + 1) / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The exact triangular-representation count, proved for every interval
length; no finite numerical extrapolation is used. -/
theorem countingEnergy_scalarInterval (n : ℕ) :
    countingEnergy (scalarInterval n) = (n : ℝ) * (2 * (n : ℝ) ^ 2 + 1) / 3 := by
  classical
  rw [← integerIntervalEnergy_eq_counting (scalarInterval n) (n + n) (by
    intro a ha
    simp only [scalarInterval, Finset.mem_Ico] at ha
    omega)]
  unfold integerIntervalEnergy
  rw [Finset.sum_range_add]
  push_cast
  have hlo : (∑ w ∈ Finset.range n, ((integerReflection (scalarInterval n) w).card : ℝ) ^ 2) =
      ∑ w ∈ Finset.range n, ((w : ℝ) + 1) ^ 2 := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [scalarInterval_reflection_low_card n w (Finset.mem_range.mp hw)]
    push_cast
    rfl
  have hhi : (∑ w ∈ Finset.range n, ((integerReflection (scalarInterval n) (n + w)).card : ℝ) ^ 2) =
      ∑ w ∈ Finset.range n, (w : ℝ) ^ 2 := by
    calc
      _ = ∑ w ∈ Finset.range n, ((n - 1 - w : ℕ) : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [scalarInterval_reflection_high_card n w (Finset.mem_range.mp hw)]
      _ = _ := Finset.sum_range_reflect (fun w ↦ (w : ℝ) ^ 2) n
  rw [hlo, hhi, ← Finset.sum_add_distrib, scalarInterval_square_sum]

end Erdos539Geometry
