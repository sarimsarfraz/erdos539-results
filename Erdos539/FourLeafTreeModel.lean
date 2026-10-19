/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FourLeafBranch
import Erdos539.GluingExactPositive
import Erdos539.IntervalExact
import Erdos539.IntegerReindex

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical

def fourLeafTreeEquiv : ((Unit ⊕ Unit) ⊕ (Unit ⊕ Unit)) ≃ Fin 4 where
  toFun i := match i with
    | .inl (.inl _) => 0
    | .inl (.inr _) => 1
    | .inr (.inl _) => 2
    | .inr (.inr _) => 3
  invFun i := if i = 0 then .inl (.inl ()) else if i = 1 then .inl (.inr ())
    else if i = 2 then .inr (.inl ()) else .inr (.inr ())
  left_inv i := by rcases i with (u | u) | (u | u) <;> cases u <;> rfl
  right_inv i := by fin_cases i <;> rfl

def twoLeafTree (T : ℕ) (B : ℤ) : Finset ((Unit ⊕ Unit) → ℤ) :=
  gluing (intervalVectors T) (intervalVectors T) T B

def fourLeafTree (T : ℕ) : Finset (((Unit ⊕ Unit) ⊕ (Unit ⊕ Unit)) → ℤ) :=
  gluing (twoLeafTree T (10 * T)) (twoLeafTree T (10 * T)) T ((10 * T) ^ 2)

theorem fourLeafLinear_tree (B : ℤ) (a : Fin 7 → ℤ) :
    fourLeafLinear B a = reindexInteger fourLeafTreeEquiv
      (glueVector (B ^ 2) (a 0)
        (glueVector B (a 1) (fun _ ↦ a 3) (fun _ ↦ a 4))
        (glueVector B (a 2) (fun _ ↦ a 5) (fun _ ↦ a 6))) := by
  funext i
  fin_cases i
  · change 1 * B ^ 2 * a 0 + 1 * B * a 1 + a 3 = (a 3 + a 1 * B) + a 0 * B ^ 2
    ring
  · change 1 * B ^ 2 * a 0 + (-1) * B * a 1 + a 4 = (a 4 - a 1 * B) + a 0 * B ^ 2
    ring
  · change (-1) * B ^ 2 * a 0 + 1 * B * a 2 + a 5 = (a 5 + a 2 * B) - a 0 * B ^ 2
    ring
  · change (-1) * B ^ 2 * a 0 + (-1) * B * a 2 + a 6 = (a 6 - a 2 * B) - a 0 * B ^ 2
    ring

theorem fourLeafBranch_eq_tree (T : ℕ) :
    fourLeafBranch T = (fourLeafTree T).image (reindexInteger fourLeafTreeEquiv) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨_, ?_, (fourLeafLinear_tree (10 * T) (fun j ↦ (a j : ℤ))).symm⟩
    apply mem_gluing.mpr
    refine ⟨(a 0).val, (a 0).isLt, _, ?_, _, ?_, rfl⟩
    · apply mem_gluing.mpr
      exact ⟨(a 1).val, (a 1).isLt, _, Finset.mem_image.mpr ⟨(a 3).val, Finset.mem_range.mpr (a 3).isLt, rfl⟩,
        _, Finset.mem_image.mpr ⟨(a 4).val, Finset.mem_range.mpr (a 4).isLt, rfl⟩, rfl⟩
    · apply mem_gluing.mpr
      exact ⟨(a 2).val, (a 2).isLt, _, Finset.mem_image.mpr ⟨(a 5).val, Finset.mem_range.mpr (a 5).isLt, rfl⟩,
        _, Finset.mem_image.mpr ⟨(a 6).val, Finset.mem_range.mpr (a 6).isLt, rfl⟩, rfl⟩
  · intro hx
    obtain ⟨tree, htree, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨r, hr, left, hleft, right, hright, rfl⟩ := mem_gluing.mp htree
    obtain ⟨s, hs, u, hu, v, hv, rfl⟩ := mem_gluing.mp hleft
    obtain ⟨t, ht, w, hw, z, hz, rfl⟩ := mem_gluing.mp hright
    obtain ⟨uDigit, huDigit, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨vDigit, hvDigit, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨wDigit, hwDigit, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨zDigit, hzDigit, rfl⟩ := Finset.mem_image.mp hz
    let a : Fin 7 → Fin T := fun i ↦ if i = 0 then ⟨r, hr⟩ else if i = 1 then ⟨s, hs⟩
      else if i = 2 then ⟨t, ht⟩ else if i = 3 then ⟨uDigit, Finset.mem_range.mp huDigit⟩
      else if i = 4 then ⟨vDigit, Finset.mem_range.mp hvDigit⟩ else if i = 5 then ⟨wDigit, Finset.mem_range.mp hwDigit⟩
      else ⟨zDigit, Finset.mem_range.mp hzDigit⟩
    refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
    rw [fourLeafEncode, fourLeafLinear_tree]
    simp [a]

end
end Erdos539Geometry
