/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13Mask63

namespace Erdos539Geometry

theorem pg13_all_masks (m : Fin 8192) : PG13MaskCertificate m.val := by
  have h : ∀ b : Fin 64, ∀ k : Fin 128, PG13MaskCertificate (b.val * 128 + k.val) := by
    intro b k
    fin_cases b
    · exact pg13_mask_batch_00 k
    · exact pg13_mask_batch_01 k
    · exact pg13_mask_batch_02 k
    · exact pg13_mask_batch_03 k
    · exact pg13_mask_batch_04 k
    · exact pg13_mask_batch_05 k
    · exact pg13_mask_batch_06 k
    · exact pg13_mask_batch_07 k
    · exact pg13_mask_batch_08 k
    · exact pg13_mask_batch_09 k
    · exact pg13_mask_batch_10 k
    · exact pg13_mask_batch_11 k
    · exact pg13_mask_batch_12 k
    · exact pg13_mask_batch_13 k
    · exact pg13_mask_batch_14 k
    · exact pg13_mask_batch_15 k
    · exact pg13_mask_batch_16 k
    · exact pg13_mask_batch_17 k
    · exact pg13_mask_batch_18 k
    · exact pg13_mask_batch_19 k
    · exact pg13_mask_batch_20 k
    · exact pg13_mask_batch_21 k
    · exact pg13_mask_batch_22 k
    · exact pg13_mask_batch_23 k
    · exact pg13_mask_batch_24 k
    · exact pg13_mask_batch_25 k
    · exact pg13_mask_batch_26 k
    · exact pg13_mask_batch_27 k
    · exact pg13_mask_batch_28 k
    · exact pg13_mask_batch_29 k
    · exact pg13_mask_batch_30 k
    · exact pg13_mask_batch_31 k
    · exact pg13_mask_batch_32 k
    · exact pg13_mask_batch_33 k
    · exact pg13_mask_batch_34 k
    · exact pg13_mask_batch_35 k
    · exact pg13_mask_batch_36 k
    · exact pg13_mask_batch_37 k
    · exact pg13_mask_batch_38 k
    · exact pg13_mask_batch_39 k
    · exact pg13_mask_batch_40 k
    · exact pg13_mask_batch_41 k
    · exact pg13_mask_batch_42 k
    · exact pg13_mask_batch_43 k
    · exact pg13_mask_batch_44 k
    · exact pg13_mask_batch_45 k
    · exact pg13_mask_batch_46 k
    · exact pg13_mask_batch_47 k
    · exact pg13_mask_batch_48 k
    · exact pg13_mask_batch_49 k
    · exact pg13_mask_batch_50 k
    · exact pg13_mask_batch_51 k
    · exact pg13_mask_batch_52 k
    · exact pg13_mask_batch_53 k
    · exact pg13_mask_batch_54 k
    · exact pg13_mask_batch_55 k
    · exact pg13_mask_batch_56 k
    · exact pg13_mask_batch_57 k
    · exact pg13_mask_batch_58 k
    · exact pg13_mask_batch_59 k
    · exact pg13_mask_batch_60 k
    · exact pg13_mask_batch_61 k
    · exact pg13_mask_batch_62 k
    · exact pg13_mask_batch_63 k
  let b : Fin 64 := ⟨m.val / 128, by omega⟩
  let k : Fin 128 := ⟨m.val % 128, Nat.mod_lt _ (by decide)⟩
  have hm : b.val * 128 + k.val = m.val := by dsimp [b, k]; omega
  simpa only [hm] using h b k

/-- Exact rational gap for all 8190 nontrivial coordinate masks. -/
theorem pg13_all_nontrivial_cut_gap (m : Fin 8192) (h0 : 0 < m.val) (hfull : m.val < 8191) :
    (5400 / 4226183 : ℚ) ≤
      (stationaryCutExponent (pg13MaskCard m.val) * pg13MaskWeight (pg13MaskComplement m.val) +
        stationaryCutExponent (13 - pg13MaskCard m.val) * pg13MaskWeight m.val) / 13 -
        4 * (stationaryCutExponent (pg13MaskCard m.val) + stationaryCutExponent (13 - pg13MaskCard m.val)) := by
  have h := (pg13_all_masks m).2.2.2 h0 hfull
  have hp : pg13MaskCard m.val < 14 := by have := (pg13_all_masks m).1; omega
  have hs : 13 - pg13MaskCard m.val < 14 := by omega
  have ha := pg13ExponentTable_eq (⟨pg13MaskCard m.val, hp⟩ : Fin 14)
  have hb := pg13ExponentTable_eq (⟨13 - pg13MaskCard m.val, hs⟩ : Fin 14)
  change pg13ExponentTable[pg13MaskCard m.val]! = _ at ha
  change pg13ExponentTable[13 - pg13MaskCard m.val]! = _ at hb
  simpa only [pg13CutGap, ha, hb] using h

theorem pg13_all_cut_weight (m : Fin 8192) :
    56 ≤ max (pg13MaskWeight m.val) (pg13MaskWeight (pg13MaskComplement m.val)) :=
  (pg13_all_masks m).2.2.1

theorem pg13_minimum_witness : pg13CutGap 126 = (5400 / 4226183 : ℚ) ∧
    pg13MaskCard 126 = 6 ∧ pg13MaskWeight 126 = 48 ∧
    pg13MaskWeight (pg13MaskComplement 126) = 56 := by decide +kernel

end Erdos539Geometry
