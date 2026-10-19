/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.InductionEstimates
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

def criticalAlpha (b : ℝ) : ℝ := (b + 1) / (2 * b)

/-- The logarithm of the critical objective, before division by 2b. -/
def criticalLogScore (b q lam : ℝ) : ℝ := 2 * b * Real.log q - (b + 1) * Real.log lam

def criticalObjective (b q lam : ℝ) : ℝ := q ^ (2 * b) / lam ^ (b + 1)

theorem criticalObjective_pos (b : ℝ) {q lam : ℝ} (hq : 0 < q) (hlam : 0 < lam) :
    0 < criticalObjective b q lam :=
  div_pos (Real.rpow_pos_of_pos hq _) (Real.rpow_pos_of_pos hlam _)

theorem log_criticalObjective (b : ℝ) {q lam : ℝ} (hq : 0 < q) (hlam : 0 < lam) :
    Real.log (criticalObjective b q lam) = criticalLogScore b q lam := by
  rw [criticalObjective, Real.log_div (Real.rpow_pos_of_pos hq _).ne'
    (Real.rpow_pos_of_pos hlam _).ne', Real.log_rpow hq, Real.log_rpow hlam]
  rfl

theorem criticalObjective_le_iff (b : ℝ) {q lam q' lam' : ℝ}
    (hq : 0 < q) (hlam : 0 < lam) (hq' : 0 < q') (hlam' : 0 < lam') :
    criticalObjective b q lam ≤ criticalObjective b q' lam' ↔
      criticalLogScore b q lam ≤ criticalLogScore b q' lam' := by
  rw [← log_criticalObjective b hq hlam, ← log_criticalObjective b hq' hlam']
  exact (Real.log_le_log_iff (criticalObjective_pos b hq hlam) (criticalObjective_pos b hq' hlam')).symm

/-- Every finite nonempty candidate family has a root minimizing this score.
Geometric closure and tie-breaking properties are separate obligations. -/
theorem exists_criticalLogScore_minimum {α : Type*} (C : Finset α) (hC : C.Nonempty)
    (q lam : α → ℝ) (b : ℝ) :
    ∃ t ∈ C, ∀ x ∈ C, criticalLogScore b (q t) (lam t) ≤ criticalLogScore b (q x) (lam x) :=
  Finset.exists_min_image C (fun x ↦ criticalLogScore b (q x) (lam x)) hC

def rootPotential (b qroot lamroot qchild lamchild : ℝ) : ℝ :=
  Real.log qchild - criticalAlpha b * Real.log lamchild -
    (Real.log qroot - criticalAlpha b * Real.log lamroot)

@[simp] theorem rootPotential_self (b q lam : ℝ) : rootPotential b q lam q lam = 0 := by
  simp [rootPotential]

theorem criticalAlpha_eq {b : ℝ} (hb : 0 < b) : criticalAlpha b = 1 / 2 + 1 / (2 * b) := by
  unfold criticalAlpha
  field_simp

theorem rootPotential_nonneg_of_minimal {b qroot lamroot qchild lamchild : ℝ}
    (hb : 0 < b)
    (hmin : criticalLogScore b qroot lamroot ≤ criticalLogScore b qchild lamchild) :
    0 ≤ rootPotential b qroot lamroot qchild lamchild := by
  have he : (2 * b) * rootPotential b qroot lamroot qchild lamchild =
      criticalLogScore b qchild lamchild - criticalLogScore b qroot lamroot := by
    unfold rootPotential criticalAlpha criticalLogScore
    field_simp
  nlinarith

/-- The exact inherited inequality retains the cost of changing the reference
parent. Nonnegativity is needed at the descendant, not at the intermediate parent. -/
theorem rootPotential_inherited {b qroot lamroot qB lamB qA lamA : ℝ}
    (hqB : 0 < qB) (hlamB : 0 < lamB) (hqA : 0 < qA) (hlamA : 0 < lamA)
    (hA : 0 ≤ rootPotential b qroot lamroot qA lamA) :
    Real.exp (-rootPotential b qroot lamroot qB lamB) * qB *
      (lamA / lamB) ^ criticalAlpha b ≤ qA := by
  have hratio : 0 < lamA / lamB := div_pos hlamA hlamB
  have hpow := Real.rpow_pos_of_pos hratio (criticalAlpha b)
  apply (Real.log_le_log_iff (mul_pos (mul_pos (Real.exp_pos _) hqB) hpow) hqA).mp
  rw [Real.log_mul (mul_pos (Real.exp_pos _) hqB).ne' hpow.ne',
    Real.log_mul (Real.exp_pos _).ne' hqB.ne', Real.log_exp,
    Real.log_rpow hratio, Real.log_div hlamA.ne' hlamB.ne']
  unfold rootPotential at hA ⊢
  nlinarith

theorem rootPotential_singleton_upper {b qroot lamroot : ℝ}
    (hb : 0 < b) (_hq : 0 < qroot) (hlam : 0 < lamroot) (hsize : lamroot ≤ qroot ^ 2) :
    rootPotential b qroot lamroot 1 1 ≤ Real.log lamroot / (2 * b) := by
  have hl := Real.log_le_log hlam hsize
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  rw [rootPotential, Real.log_one, mul_zero, sub_zero, zero_sub, criticalAlpha_eq hb]
  simp only [div_eq_mul_inv]
  nlinarith

theorem rootPotential_singleton_bounds {b qroot lamroot : ℝ}
    (hb : 0 < b) (hq : 0 < qroot) (hlam : 0 < lamroot) (hsize : lamroot ≤ qroot ^ 2)
    (hmin : criticalLogScore b qroot lamroot ≤ criticalLogScore b 1 1) :
    0 ≤ rootPotential b qroot lamroot 1 1 ∧
      rootPotential b qroot lamroot 1 1 ≤ Real.log lamroot / (2 * b) :=
  ⟨rootPotential_nonneg_of_minimal hb hmin, rootPotential_singleton_upper hb hq hlam hsize⟩

/-- Signed increments telescope. This says nothing about positive excursions
or sums of potential values in a branching recursion. -/
theorem potential_signed_telescope (δ : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range m, (δ (j + 1) - δ j) = δ m - δ 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

theorem rootPotential_path_bound {b qroot lamroot : ℝ}
    (hb : 0 < b) (hq : 0 < qroot) (hlam : 0 < lamroot) (hsize : lamroot ≤ qroot ^ 2)
    (q lam : ℕ → ℝ) (m : ℕ) (hq0 : q 0 = qroot) (hlam0 : lam 0 = lamroot)
    (hqm : q m = 1) (hlamm : lam m = 1) :
    ∑ j ∈ Finset.range m,
      (rootPotential b qroot lamroot (q (j + 1)) (lam (j + 1)) -
        rootPotential b qroot lamroot (q j) (lam j)) ≤ Real.log lamroot / (2 * b) := by
  rw [potential_signed_telescope (fun j ↦ rootPotential b qroot lamroot (q j) (lam j)) m,
    hq0, hlam0, rootPotential_self, sub_zero, hqm, hlamm]
  exact rootPotential_singleton_upper hb hq hlam hsize

end
end Erdos539Geometry
