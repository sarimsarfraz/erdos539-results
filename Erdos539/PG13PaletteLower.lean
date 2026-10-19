/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13RetainedEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Classical

theorem pg13Branch_projection_card {T : ℕ} (hT : 0 < T) (l : Fin 13) (I : Finset (Fin 13)) :
    ((pg13Branch T l).image (fun x (j : I) ↦ x j.val)).card =
      T ^ (fourLeafActiveDigits (pg13LocalCoordinates l I)).card := by
  let f := (imageEndpoint (pg13Branch T l) (fun x (j : I) ↦ x j.val)) ∘
    (imageEndpoint (fourLeafBranch T) (pg13BranchEmbed T l))
  let g := imageEndpoint (fourLeafBranch T) (fun x (j : pg13LocalCoordinates l I) ↦ x j.val)
  have hf : Function.Surjective f :=
    (imageEndpoint_surjective _ _).comp (imageEndpoint_surjective _ _)
  have hg : Function.Surjective g := imageEndpoint_surjective _ _
  have hh (a b : fourLeafBranch T) : f a = f b ↔ g a = g b := by
    have he : f a = f b ↔ pg13UnionObservation T I (l, a) = pg13UnionObservation T I (l, b) := by
      constructor
      · intro h
        have hv := congrArg Subtype.val h
        exact Subtype.ext hv
      · intro h
        have hv := congrArg Subtype.val h
        exact Subtype.ext hv
    exact he.trans (pg13_branch_observation_fibers T l I a b)
  have h := finite_card_eq_of_same_fibers f g hf hg hh
  simpa only [Fintype.card_coe, fourLeafBranch_projection_card hT] using h

theorem pg13_three_coordinate_digits : ∀ l m : Fin 13, l ≠ m →
    (fourLeafActiveDigits (pg13LocalCoordinates l (pg13LineSet l \ pg13LineSet m))).card = 6 := by
  decide +kernel

theorem pg13_reverse_output_recovers {T : ℕ} (hT : 0 < T) (l m : Fin 13)
    {a x y : Fin 13 → ℤ} (ha : a ∈ pg13Branch T m)
    (hx : x ∈ pg13Branch T l) (hy : y ∈ pg13Branch T l)
    (h : intPdiff a x = intPdiff a y) :
    (fun j : ↥(pg13LineSet l \ pg13LineSet m) ↦ x j.val) =
      (fun j : ↥(pg13LineSet l \ pg13LineSet m) ↦ y j.val) := by
  funext j
  have hj := Finset.mem_sdiff.mp j.property
  have ha' := (pg13Branch_coordinate_bounds hT m ha j.val).2 hj.2
  have hx' := ((pg13Branch_coordinate_bounds hT l hx j.val).1 hj.1).2
  have hy' := ((pg13Branch_coordinate_bounds hT l hy j.val).1 hj.1).2
  have he := congrFun h j.val
  change max (a j.val - x j.val) 0 = max (a j.val - y j.val) 0 at he
  rw [max_eq_left (by omega), max_eq_left (by omega)] at he
  omega

/-- The full quotient palette sees T^6 outputs with varying anchors,
although every fixed forward anchor has only O(T^4) outputs. -/
theorem pg13Union_palette_lower {T : ℕ} (hT : 0 < T) :
    T ^ 6 ≤ (integerPositiveDifferences (pg13Union T)).card := by
  have hB : (pg13Branch T 1).Nonempty := (fourLeafBranch_nonempty hT).image _
  obtain ⟨a, ha⟩ := hB
  have hbound := card_image_le_of_fibers (pg13Branch T 0)
    (fun x (j : ↥(pg13LineSet 0 \ pg13LineSet 1)) ↦ x j.val)
    (fun x ↦ intPdiff a x) (fun _ hx _ hy he ↦ pg13_reverse_output_recovers hT 0 1 ha hx hy he)
  have hsub : (pg13Branch T 0).image (fun x ↦ intPdiff a x) ⊆
      integerPositiveDifferences (pg13Union T) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact mem_integerPositiveDifferences.mpr ⟨a, pg13Branch_subset_union T 1 ha,
      x, pg13Branch_subset_union T 0 hx, rfl⟩
  rw [pg13Branch_projection_card hT, pg13_three_coordinate_digits 0 1 (by decide)] at hbound
  exact hbound.trans (Finset.card_le_card hsub)

end
end Erdos539Geometry
