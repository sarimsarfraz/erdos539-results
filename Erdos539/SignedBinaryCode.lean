/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CornerGeometry
import Mathlib.Tactic.Ring

namespace Erdos539Geometry
open scoped Classical
variable {ι : Type*}

def binaryDigit (b : Bool) : ℤ := if b then 1 else 0

def binarySign (b : Bool) : ℤ := if b then 1 else -1

/-- The literal superincreasing signed binary code, with powers of three. -/
def signedBinaryCode : (m : ℕ) → (Fin m → ι → Bool) → (Fin m → Bool) → ι → ℤ
  | 0, _, _, _ => 0
  | n + 1, σ, η, i => signedBinaryCode n (fun j ↦ σ j.castSucc) (fun j ↦ η j.castSucc) i +
      (3 : ℤ) ^ n * binaryDigit (η (Fin.last n)) * binarySign (σ (Fin.last n) i)

theorem binary_signed_difference_bound (a b s : Bool) :
    |binaryDigit a * binarySign s - binaryDigit b * binarySign s| ≤ 1 := by
  cases a <;> cases b <;> cases s <;> norm_num [binaryDigit, binarySign]

/-- All lower digits together have strictly less magnitude than the next
power of three. This holds separately in every coordinate. -/
theorem signedBinaryCode_difference_bound (m : ℕ) (σ : Fin m → ι → Bool)
    (η ξ : Fin m → Bool) (i : ι) :
    2 * |signedBinaryCode m σ η i - signedBinaryCode m σ ξ i| ≤ (3 : ℤ) ^ m - 1 := by
  induction m with
  | zero => simp [signedBinaryCode]
  | succ m ih =>
    have hlo := ih (fun j ↦ σ j.castSucc) (fun j ↦ η j.castSucc) (fun j ↦ ξ j.castSucc)
    have hd := binary_signed_difference_bound (η (Fin.last m)) (ξ (Fin.last m)) (σ (Fin.last m) i)
    have he : signedBinaryCode (m + 1) σ η i - signedBinaryCode (m + 1) σ ξ i =
        (signedBinaryCode m (fun j ↦ σ j.castSucc) (fun j ↦ η j.castSucc) i -
          signedBinaryCode m (fun j ↦ σ j.castSucc) (fun j ↦ ξ j.castSucc) i) +
        (3 : ℤ) ^ m * (binaryDigit (η (Fin.last m)) * binarySign (σ (Fin.last m) i) -
          binaryDigit (ξ (Fin.last m)) * binarySign (σ (Fin.last m) i)) := by
      simp only [signedBinaryCode]
      ring
    rw [he]
    have hp : (0 : ℤ) ≤ 3 ^ m := by positivity
    have ht := abs_add_le
      (signedBinaryCode m (fun j ↦ σ j.castSucc) (fun j ↦ η j.castSucc) i -
        signedBinaryCode m (fun j ↦ σ j.castSucc) (fun j ↦ ξ j.castSucc) i)
      ((3 : ℤ) ^ m * (binaryDigit (η (Fin.last m)) * binarySign (σ (Fin.last m) i) -
        binaryDigit (ξ (Fin.last m)) * binarySign (σ (Fin.last m) i)))
    rw [abs_mul, abs_of_nonneg hp] at ht
    have hh := mul_le_mul_of_nonneg_left hd hp
    rw [mul_one] at hh
    rw [pow_succ]
    nlinarith

/-- A differing digit controls the strict direction of every coordinate
comparison. The multiplier on the right is always either +1 or -1. -/
theorem signedBinaryCode_leading (m : ℕ) (σ : Fin m → ι → Bool)
    (η ξ : Fin m → Bool) (hne : η ≠ ξ) :
    ∃ j : Fin m, η j ≠ ξ j ∧ ∀ i,
      0 < (signedBinaryCode m σ ξ i - signedBinaryCode m σ η i) *
        ((binaryDigit (ξ j) - binaryDigit (η j)) * binarySign (σ j i)) := by
  induction m with
  | zero => exact False.elim (hne (funext fun j ↦ Fin.elim0 j))
  | succ m ih =>
    by_cases hl : η (Fin.last m) = ξ (Fin.last m)
    · have hi : (fun j : Fin m ↦ η j.castSucc) ≠ (fun j : Fin m ↦ ξ j.castSucc) := by
        intro he
        apply hne
        funext j
        exact Fin.lastCases hl (fun k ↦ congrFun he k) j
      obtain ⟨j, hj, hc⟩ := ih (fun j ↦ σ j.castSucc) (fun j ↦ η j.castSucc) (fun j ↦ ξ j.castSucc) hi
      refine ⟨j.castSucc, hj, ?_⟩
      intro i
      simp only [signedBinaryCode, hl]
      convert hc i using 1
      ring
    · refine ⟨Fin.last m, hl, ?_⟩
      intro i
      have hb := signedBinaryCode_difference_bound m (fun j ↦ σ j.castSucc)
        (fun j ↦ ξ j.castSucc) (fun j ↦ η j.castSucc) i
      have hlow := le_abs_self
        (signedBinaryCode m (fun j ↦ σ j.castSucc) (fun j ↦ ξ j.castSucc) i -
          signedBinaryCode m (fun j ↦ σ j.castSucc) (fun j ↦ η j.castSucc) i)
      have hlow' := neg_le_abs
        (signedBinaryCode m (fun j ↦ σ j.castSucc) (fun j ↦ ξ j.castSucc) i -
          signedBinaryCode m (fun j ↦ σ j.castSucc) (fun j ↦ η j.castSucc) i)
      cases hη : η (Fin.last m) <;> cases hξ : ξ (Fin.last m) <;>
        cases hs : σ (Fin.last m) i <;>
        simp only [hη, hξ, Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, not_true_eq_false] at hl
      all_goals
        simp only [signedBinaryCode, hη, hξ, hs, binaryDigit, binarySign,
          Bool.false_eq_true, ite_false, ite_true, mul_zero, mul_one, mul_neg_one,
          sub_zero, zero_sub, add_zero]
        nlinarith

end Erdos539Geometry
