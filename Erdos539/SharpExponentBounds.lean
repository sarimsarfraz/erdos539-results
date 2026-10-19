/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpExponents

namespace Erdos539Geometry

/-- The sharp recursion dominates the simpler dimension-uniform exponent. -/
theorem sharpExponent_ge_uniform {d : ℕ} (hd : 0 < d) :
    uniformExponent d ≤ (sharpExponent d : ℝ) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hone : d = 1
    · subst d
      norm_num [uniformExponent]
    · obtain ⟨p, s, hp, hs, he, hmin⟩ := sharpExponent_attained (by omega : 2 ≤ d)
      have hip := ih p (by omega) hp
      have his := ih s (by omega) hs
      have hpd := uniformExponent_pos hp
      have hsd := uniformExponent_pos hs
      have hp' : (0 : ℝ) < sharpExponent p := by exact_mod_cast sharpExponent_pos p
      have hs' : (0 : ℝ) < sharpExponent s := by exact_mod_cast sharpExponent_pos s
      calc
        uniformExponent d = uniformExponent (p + s) := congrArg uniformExponent he.symm
        _ ≤ (uniformExponent p + uniformExponent s) / (1 + uniformExponent p + uniformExponent s) :=
          uniformExponent_split hp hs
        _ ≤ ((sharpExponent p : ℝ) + sharpExponent s) / (1 + (sharpExponent p : ℝ) + sharpExponent s) := by
          apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
          nlinarith
        _ = (sharpExponent d : ℝ) := by
          rw [hmin, combineExponent]
          push_cast
          rfl

/-- In particular every fixed dimension has a strictly super-square-root exponent. -/
theorem sharpExponent_gt_half {d : ℕ} (hd : 0 < d) :
    (1 / 2 : ℝ) < sharpExponent d := by
  have h := (uniformExponent_ge_half_add hd).trans (sharpExponent_ge_uniform hd)
  have hpos : (0 : ℝ) < 1 / (4 * (d : ℝ)) := by positivity
  linarith

end Erdos539Geometry
