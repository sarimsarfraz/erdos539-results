/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13CutEntropy

namespace Erdos539Geometry
open scoped BigOperators

theorem pg13_empty_full_masks : pg13MaskSet ⟨0, by decide⟩ = ∅ ∧
    pg13MaskSet ⟨8191, by decide⟩ = Finset.univ := by decide +kernel

theorem pg13SetMask_nontrivial (I : Finset (Fin 13)) (hI : I.Nonempty) (hJ : Iᶜ.Nonempty) :
    0 < (pg13SetMask I).val ∧ (pg13SetMask I).val < 8191 := by
  have h0 : (pg13SetMask I).val ≠ 0 := by
    intro h
    have hm : pg13SetMask I = ⟨0, by decide⟩ := Fin.ext h
    have he : I = ∅ := by rw [← pg13MaskSet_setMask I, hm, pg13_empty_full_masks.1]
    exact hI.ne_empty he
  have hfull : (pg13SetMask I).val ≠ 8191 := by
    intro h
    have hm : pg13SetMask I = ⟨8191, by decide⟩ := Fin.ext h
    have he : I = Finset.univ := by rw [← pg13MaskSet_setMask I, hm, pg13_empty_full_masks.2]
    simp only [he, Finset.compl_univ, Finset.not_nonempty_empty] at hJ
  have hm := (pg13SetMask I).isLt
  omega

set_option maxHeartbeats 800000 in
theorem pg13_weighted_coefficient (I : Finset (Fin 13)) (hI : I.Nonempty) (hJ : Iᶜ.Nonempty) :
    (5400 / 4226183 : ℚ) ≤
      (stationaryCutExponent I.card * pg13VisibleWeight Iᶜ +
        stationaryCutExponent Iᶜ.card * pg13VisibleWeight I) / 13 -
          4 * (stationaryCutExponent I.card + stationaryCutExponent Iᶜ.card) := by
  obtain ⟨h0, hfull⟩ := pg13SetMask_nontrivial I hI hJ
  have h := pg13_all_nontrivial_cut_gap (pg13SetMask I) h0 hfull
  have hc : pg13MaskCard (pg13SetMask I).val = I.card := by
    rw [pg13MaskCard_eq, pg13MaskSet_setMask]
  have hj : Iᶜ.card = 13 - I.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hwj := pg13VisibleWeight_mask (pg13ComplementMask (pg13SetMask I))
  rw [pg13MaskSet_complement, pg13MaskSet_setMask] at hwj
  change pg13VisibleWeight Iᶜ = pg13MaskWeight (pg13MaskComplement (pg13SetMask I).val) at hwj
  rwa [hc, ← hj, ← pg13VisibleWeight_setMask I, ← hwj] at h

theorem pg13_cut_exponent_bounds (d : Fin 14) :
    0 ≤ stationaryCutExponent d.val ∧ stationaryCutExponent d.val ≤ 2 / 3 := by
  have h : ∀ k : Fin 14, (0 : ℚ) ≤ pg13ExponentTable[k.val]! ∧ pg13ExponentTable[k.val]! ≤ 2 / 3 := by
    decide +kernel
  simpa only [pg13ExponentTable_eq] using h d

end Erdos539Geometry
