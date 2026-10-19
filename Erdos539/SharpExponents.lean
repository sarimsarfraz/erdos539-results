/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.UniformExponents
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Rat.Cast.Order

namespace Erdos539Geometry

/-- The combination rule for the sharp fixed-dimensional exponents. -/
def combineExponent (a b : ℚ) : ℚ := (a + b) / (1 + a + b)

/-- The exact rational recursion u_d from the manuscript. The unused value
at dimension zero is set to one; all extremal results assume positive dimension. -/
def sharpExponent : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | n + 2 => (Finset.univ : Finset (Fin (n + 1))).inf' Finset.univ_nonempty
      (fun i ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (n + 1 - i.val)))
termination_by d => d

@[simp] theorem sharpExponent_zero : sharpExponent 0 = 1 := sharpExponent.eq_1
@[simp] theorem sharpExponent_one : sharpExponent 1 = 1 := sharpExponent.eq_2

theorem sharpExponent_rec (n : ℕ) :
    sharpExponent (n + 2) = (Finset.univ : Finset (Fin (n + 1))).inf' Finset.univ_nonempty
      (fun i ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (n + 1 - i.val))) :=
  sharpExponent.eq_3 n

/-- Every positive split is an admissible candidate in the exact minimum. -/
theorem sharpExponent_le_split {p s : ℕ} (hp : 0 < p) (hs : 0 < s) :
    sharpExponent (p + s) ≤ combineExponent (sharpExponent p) (sharpExponent s) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  have he : p.succ + s.succ = (p + s) + 2 := by omega
  rw [he, sharpExponent_rec]
  have h := Finset.inf'_le
    (fun i : Fin (p + s + 1) ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (p + s + 1 - i.val)))
    (Finset.mem_univ (⟨p, by omega⟩ : Fin (p + s + 1)))
  have hsub : p + s + 1 - p = s + 1 := by omega
  simpa only [hsub, Nat.succ_eq_add_one] using h

/-- A minimizing positive split actually exists in every dimension at least two. -/
theorem sharpExponent_attained {d : ℕ} (hd : 2 ≤ d) :
    ∃ p s : ℕ, 0 < p ∧ 0 < s ∧ p + s = d ∧
      sharpExponent d = combineExponent (sharpExponent p) (sharpExponent s) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hd
  have he : 2 + n = n + 2 := by omega
  rw [he, sharpExponent_rec]
  obtain ⟨i, _hi, hmin⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin (n + 1))))
    Finset.univ_nonempty
    (fun i ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (n + 1 - i.val)))
  exact ⟨i.val + 1, n + 1 - i.val, by omega, by omega, by omega, hmin⟩

theorem combineExponent_bounds {a b : ℚ} (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b) :
    1 / 2 ≤ combineExponent a b ∧ combineExponent a b < 1 := by
  have hden : 0 < 1 + a + b := by linarith
  constructor
  · apply (le_div_iff₀ hden).mpr
    linarith
  · apply (div_lt_one hden).mpr
    linarith

/-- Uniform elementary bounds on every recursively defined sharp exponent. -/
theorem sharpExponent_bounds (d : ℕ) : 1 / 2 ≤ sharpExponent d ∧ sharpExponent d ≤ 1 := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : d ≤ 1
    · rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> norm_num
    · obtain ⟨p, s, hp, hs, he, hmin⟩ := sharpExponent_attained (by omega : 2 ≤ d)
      have hip := ih p (by omega)
      have his := ih s (by omega)
      rw [hmin]
      have hb := combineExponent_bounds hip.1 his.1
      exact ⟨hb.1, hb.2.le⟩

theorem sharpExponent_pos (d : ℕ) : 0 < sharpExponent d :=
  (by norm_num : (0 : ℚ) < 1 / 2).trans_le (sharpExponent_bounds d).1

end Erdos539Geometry
