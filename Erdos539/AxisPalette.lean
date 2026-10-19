/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalCoreStructure

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*}
local instance axisPaletteDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- An axis-parallel pair produces a nonzero palette color supported on
exactly that coordinate, irrespective of the orientation of the pair. -/
theorem exists_axis_palette_color {T : Finset (ι → ℝ)} {i : ι}
    (h : ∃ x ∈ T, ∃ y ∈ T, x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j) :
    ∃ z ∈ posDiff T, 0 < z i ∧ ∀ j, j ≠ i → z j = 0 := by
  obtain ⟨x, hx, y, hy, hxy, haxis⟩ := h
  rcases lt_or_gt_of_ne hxy with hi | hi
  · refine ⟨pdiff y x, mem_posDiff.mpr ⟨y, hy, x, hx, rfl⟩, ?_, ?_⟩
    · exact lt_of_lt_of_le (sub_pos.mpr hi) (le_max_left _ _)
    · intro j hj
      simp [pdiff, haxis j hj]
  · refine ⟨pdiff x y, mem_posDiff.mpr ⟨x, hx, y, hy, rfl⟩, ?_, ?_⟩
    · exact lt_of_lt_of_le (sub_pos.mpr hi) (le_max_left _ _)
    · intro j hj
      simp [pdiff, haxis j hj]

/-- The zero color and one nonzero axis color for each retained
coordinate are distinct actual members of the positive-difference palette. -/
theorem card_axis_mask_add_one_le_palette {T : Finset (ι → ℝ)} (hT : T.Nonempty)
    (I : Finset ι)
    (haxis : ∀ i ∈ I, ∃ x ∈ T, ∃ y ∈ T, x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j) :
    I.card + 1 ≤ (posDiff T).card := by
  have hcolor (i : I) : ∃ z ∈ posDiff T, 0 < z i.val ∧ ∀ j, j ≠ i.val → z j = 0 :=
    exists_axis_palette_color (haxis i.val i.property)
  choose z hz using hcolor
  have hzero : (0 : ι → ℝ) ∈ posDiff T := by
    obtain ⟨x, hx⟩ := hT
    exact mem_posDiff.mpr ⟨x, hx, x, hx, by ext j; simp [pdiff]⟩
  let g : Option I → posDiff T := fun u ↦ match u with
    | none => ⟨0, hzero⟩
    | some i => ⟨z i, (hz i).1⟩
  have hg : Function.Injective g := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some j =>
        have he := congrFun (congrArg Subtype.val hab) j.val
        change 0 = z j j.val at he
        exact False.elim ((ne_of_gt (hz j).2.1) he.symm)
    | some i =>
      cases b with
      | none =>
        have he := congrFun (congrArg Subtype.val hab) i.val
        change z i i.val = 0 at he
        exact False.elim ((ne_of_gt (hz i).2.1) he)
      | some j =>
        by_cases hij : i = j
        · rw [hij]
        · have hv : i.val ≠ j.val := fun he ↦ hij (Subtype.ext he)
          have he := congrFun (congrArg Subtype.val hab) i.val
          change z i i.val = z j i.val at he
          rw [(hz j).2.2 i.val hv] at he
          exact False.elim ((ne_of_gt (hz i).2.1) he)
  simpa only [Fintype.card_option, Fintype.card_coe] using Fintype.card_le_of_injective g hg

namespace IsProjectionCriticalCore
variable [Fintype ι] {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

theorem mask_card_add_one_le_palette (h : IsProjectionCriticalCore S b I T) (hb : 0 < b) :
    I.card + 1 ≤ (posDiff T).card :=
  card_axis_mask_add_one_le_palette h.nonempty I (fun _ hi ↦ h.axis_pair hb hi)

end IsProjectionCriticalCore
end
end Erdos539Geometry
