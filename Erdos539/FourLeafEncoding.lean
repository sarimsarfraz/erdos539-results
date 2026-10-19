/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ThreeDigitDecoding

namespace Erdos539Geometry
open scoped BigOperators Pointwise

def fourLeafRootSign (i : Fin 4) : ℤ := if i.val < 2 then 1 else -1
def fourLeafSiblingSign (i : Fin 4) : ℤ := if i.val % 2 = 0 then 1 else -1
def fourLeafSibling (i : Fin 4) : Fin 7 := if i.val < 2 then 1 else 2
def fourLeafLeaf (i : Fin 4) : Fin 7 := ⟨i.val + 3, by omega⟩

/-- The seven-digit, four-coordinate linear branch in the obstruction. -/
def fourLeafLinear (B : ℤ) : (Fin 7 → ℤ) →+ (Fin 4 → ℤ) where
  toFun a i := fourLeafRootSign i * B ^ 2 * a 0 +
    fourLeafSiblingSign i * B * a (fourLeafSibling i) + a (fourLeafLeaf i)
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp only [Pi.add_apply]; ring

theorem fourLeaf_coordinate_recover {B : ℤ} (hB : 0 < B) {a b : Fin 7 → ℤ}
    (ha : ∀ j, 0 ≤ a j ∧ a j < B) (hb : ∀ j, 0 ≤ b j ∧ b j < B)
    (i : Fin 4) (he : fourLeafLinear B a i = fourLeafLinear B b i) :
    a 0 = b 0 ∧ a (fourLeafSibling i) = b (fourLeafSibling i) ∧
      a (fourLeafLeaf i) = b (fourLeafLeaf i) := by
  have hε : fourLeafRootSign i = 1 ∨ fourLeafRootSign i = -1 := by
    unfold fourLeafRootSign; split_ifs <;> simp
  have hδ : fourLeafSiblingSign i = 1 ∨ fourLeafSiblingSign i = -1 := by
    unfold fourLeafSiblingSign; split_ifs <;> simp
  obtain ⟨hl, hs, hr⟩ := signed_three_digit_recover hB (ha (fourLeafLeaf i)) (hb (fourLeafLeaf i))
    (ha (fourLeafSibling i)) (hb (fourLeafSibling i)) hε hδ he
  exact ⟨hr, hs, hl⟩

def fourLeafActiveDigits (I : Finset (Fin 4)) : Finset (Fin 7) :=
  I.biUnion (fun i ↦ {0, fourLeafSibling i, fourLeafLeaf i})

theorem fourLeaf_projection_eq_iff {B : ℤ} (hB : 0 < B) {a b : Fin 7 → ℤ}
    (ha : ∀ j, 0 ≤ a j ∧ a j < B) (hb : ∀ j, 0 ≤ b j ∧ b j < B)
    (I : Finset (Fin 4)) :
    (∀ i ∈ I, fourLeafLinear B a i = fourLeafLinear B b i) ↔
      ∀ j ∈ fourLeafActiveDigits I, a j = b j := by
  constructor
  · intro h j hj
    obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨hr, hs, hl⟩ := fourLeaf_coordinate_recover hB ha hb i (h i hi)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact hr
    · exact hs
    · exact hl
  · intro h i hi
    have hr := h 0 (Finset.mem_biUnion.mpr ⟨i, hi, by simp⟩)
    have hs := h (fourLeafSibling i) (Finset.mem_biUnion.mpr ⟨i, hi, by simp⟩)
    have hl := h (fourLeafLeaf i) (Finset.mem_biUnion.mpr ⟨i, hi, by simp⟩)
    change fourLeafRootSign i * B ^ 2 * a 0 + fourLeafSiblingSign i * B * a (fourLeafSibling i) +
      a (fourLeafLeaf i) = _
    rw [hr, hs, hl]
    rfl

theorem fourLeaf_all_digits : fourLeafActiveDigits Finset.univ = Finset.univ := by
  decide +kernel

theorem fourLeafLinear_injective_on_box {B : ℤ} (hB : 0 < B) {a b : Fin 7 → ℤ}
    (ha : ∀ j, 0 ≤ a j ∧ a j < B) (hb : ∀ j, 0 ≤ b j ∧ b j < B)
    (he : fourLeafLinear B a = fourLeafLinear B b) : a = b := by
  have h := (fourLeaf_projection_eq_iff hB ha hb Finset.univ).mp (fun i _ ↦ congrFun he i)
  rw [fourLeaf_all_digits] at h
  funext j
  exact h j (Finset.mem_univ j)

end Erdos539Geometry
