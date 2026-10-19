/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13ProjectionEntropy
import Erdos539.PG13MaskIntersection

namespace Erdos539Geometry
open scoped BigOperators

theorem list_countP_ofFn {α : Type*} (p : α → Bool) {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).countP p = ∑ i, if p (f i) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.countP_cons, Fin.sum_univ_succ, ih]
    split_ifs <;> omega

theorem pg13_digit_visible_iff (l : Fin 13) (I : Finset (Fin 13)) (d : Fin 7) :
    d ∈ fourLeafActiveDigits (pg13LocalCoordinates l I) ↔
      ∃ j ∈ I, j ∈ pg13DigitSupport l d := by
  simp only [fourLeafActiveDigits, Finset.mem_biUnion, pg13LocalCoordinates,
    Finset.mem_filter, Finset.mem_univ, true_and, pg13DigitSupport]
  constructor
  · rintro ⟨i, hi, hd⟩
    exact ⟨pg13LineEmbedding l i, hi, i, rfl, hd⟩
  · rintro ⟨j, hj, i, rfl, hd⟩
    exact ⟨i, hj, hd⟩

theorem pg13_active_mask_count (m : Fin 8192) (l : Fin 13) :
    (fourLeafActiveDigits (pg13LocalCoordinates l (pg13MaskSet m))).card =
      ∑ d : Fin 7, if m.val &&& pg13SupportMask l d != 0 then 1 else 0 := by
  have he : fourLeafActiveDigits (pg13LocalCoordinates l (pg13MaskSet m)) =
      Finset.univ.filter (fun d : Fin 7 ↦ m.val &&& pg13SupportMask l d ≠ 0) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pg13_digit_visible_iff,
      pg13_support_mask_meets]
  rw [he, Finset.card_filter]
  simp

/-- The finite certificate's numerical W is exactly the number of
independent digits observed in the literal thirteen embedded branches. -/
theorem pg13VisibleWeight_mask (m : Fin 8192) :
    pg13VisibleWeight (pg13MaskSet m) = pg13MaskWeight m.val := by
  rw [pg13MaskWeight, pg13_digit_support_certificate.2.countP_eq (fun s ↦ m.val &&& s != 0),
    List.countP_flatten, List.map_ofFn, List.sum_ofFn]
  simp only [pg13VisibleWeight, pg13_active_mask_count, Function.comp_apply, list_countP_ofFn]

theorem pg13VisibleWeight_setMask (I : Finset (Fin 13)) :
    pg13VisibleWeight I = pg13MaskWeight (pg13SetMask I).val := by
  rw [← pg13VisibleWeight_mask, pg13MaskSet_setMask]

end Erdos539Geometry
