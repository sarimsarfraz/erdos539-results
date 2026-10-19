/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsCoordinateRecursion

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*}
local instance coordinateExistenceDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace GibbsRecursion

/-- Every nonempty physical mask admits a complete finite coordinate
recursion. The result is an actual tree with all nonempty fibers, not
a hypothesis that a suitable tree exists. -/
theorem exists_coordinate (B : Finset ι) (hB : B.Nonempty) (s : GibbsReference (ι → ℝ))
    (hfixed : s.FixedOutside B) : ∃ t : GibbsRecursion s, IsCoordinate B t := by
  induction B using Finset.strongInductionOn generalizing s with
  | _ B ih =>
    by_cases hcard : B.card = 1
    · exact ⟨.leaf s, .leaf s B hcard hfixed⟩
    obtain ⟨i, hi⟩ := hB
    have hIB : ({i} : Finset ι) ⊆ B := Finset.singleton_subset_iff.mpr hi
    have hJsmall : B \ {i} ⊂ B := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
      intro he
      have hmem : i ∈ B \ {i} := he.symm ▸ hi
      simp at hmem
    have hJ : (B \ {i}).Nonempty := by
      apply Finset.card_pos.mp
      have hc := Finset.card_sdiff_add_card_eq_card hIB
      have hb : 0 < B.card := Finset.card_pos.mpr ⟨i, hi⟩
      simp only [Finset.card_singleton] at hc
      omega
    have hf : ∀ y : s.support.image (maskCoordinatesHom {i}),
        ∃ t : GibbsRecursion (s.fiber (maskCoordinatesHom {i}) y), IsCoordinate (B \ {i}) t := by
      intro y
      exact ih (B \ {i}) hJsmall hJ _ (s.fiber_fixedOutside B {i} hfixed y)
    choose f hf using hf
    let p : GibbsRecursion (s.image (maskCoordinatesHom {i})) := .leaf _
    have hp : IsCoordinate {i} p := .leaf _ {i} (Finset.card_singleton i) (s.image_fixedOutside {i})
    exact ⟨.cut s (maskCoordinatesHom {i}) p f,
      .cut s B {i} hIB (Finset.singleton_nonempty i) hJ hfixed p f hp hf⟩

theorem exists_coordinate_realization_budget (B : Finset ι) (hB : B.Nonempty)
    (s : GibbsReference (ι → ℝ)) (hfixed : s.FixedOutside B) :
    ∃ (t : GibbsRecursion s) (x : t.Outcome), IsCoordinate B t ∧ t.leafCount x = B.card ∧
      t.cost (fun s φ _ ↦ s.cutCharge φ) GibbsReference.deficit x ≤ s.deficit := by
  obtain ⟨t, ht⟩ := exists_coordinate B hB s hfixed
  obtain ⟨x, hx⟩ := t.exists_realization_cut_budget
  exact ⟨t, x, ht, ht.leafCount_eq x, hx⟩

end GibbsRecursion
end
end Erdos539Geometry
