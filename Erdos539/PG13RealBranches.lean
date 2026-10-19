/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13PaletteLower
import Erdos539.PaletteEmbeddings

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

theorem pg13Branch_real_nonempty {T : ℕ} (hT : 0 < T) (l : Fin 13) :
    (integerRealSet (pg13Branch T l)).Nonempty :=
  integerRealSet_nonempty ((fourLeafBranch_nonempty hT).image _)

theorem pg13Branch_real_subset (T : ℕ) (l : Fin 13) :
    integerRealSet (pg13Branch T l) ⊆ integerRealSet (pg13Union T) := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_integerRealSet.mp hx
  exact mem_integerRealSet.mpr ⟨a, pg13Branch_subset_union T l ha, rfl⟩

theorem pg13Branch_real_palette {T : ℕ} (hT : 0 < T) (l : Fin 13) :
    (posDiff (integerRealSet (pg13Branch T l))).card ≤ 41 * T ^ 4 := by
  rw [pg13Branch_real, posDiff_translateRealSet, posDiff_coordinatePad,
    Finset.card_image_of_injective _ (coordinatePad_injective _), posDiff_integerRealSet_card]
  exact fourLeafBranch_palette_le hT

theorem pg13Union_real_palette_lower {T : ℕ} (hT : 0 < T) :
    T ^ 6 ≤ (posDiff (integerRealSet (pg13Union T))).card := by
  rw [posDiff_integerRealSet_card]
  exact pg13Union_palette_lower hT

theorem pg13Union_real_eq_biUnion (T : ℕ) :
    integerRealSet (pg13Union T) = Finset.univ.biUnion (fun l : Fin 13 ↦ integerRealSet (pg13Branch T l)) := by
  ext x
  simp only [mem_integerRealSet, pg13Union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  aesop

theorem pg13_real_branches_disjoint {T : ℕ} (hT : 0 < T) {l m : Fin 13} (hlm : l ≠ m) :
    Disjoint (integerRealSet (pg13Branch T l)) (integerRealSet (pg13Branch T m)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a, ha, he⟩ := mem_integerRealSet.mp hx
  obtain ⟨b, hb, he'⟩ := mem_integerRealSet.mp hy
  have hab : a = b := integerToReal_injective (he.trans he'.symm)
  subst b
  exact Finset.disjoint_left.mp (pg13Branches_disjoint hT hlm) ha hb

end
end Erdos539Geometry
