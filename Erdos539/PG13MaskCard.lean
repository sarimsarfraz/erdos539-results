/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13MaskSets

namespace Erdos539Geometry

theorem pg13MaskCard_eq (m : Fin 8192) : pg13MaskCard m.val = (pg13MaskSet m).card := by
  have he : (List.range 13 |>.filter (fun k ↦ m.val.testBit k)).toFinset =
      (Finset.range 13).filter (fun k ↦ m.val.testBit k) := by
    ext k
    simp
  have hi : (Finset.range 13).filter (fun k ↦ m.val.testBit k) =
      (pg13MaskSet m).image Fin.val := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image,
      pg13MaskSet, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hk, hb⟩
      exact ⟨⟨k, hk⟩, hb, rfl⟩
    · rintro ⟨i, hb, rfl⟩
      exact ⟨i.isLt, hb⟩
  rw [pg13MaskCard, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_range (n := 13)).filter _),
    he, hi, Finset.card_image_of_injective _ Fin.val_injective]

def pg13ComplementMask (m : Fin 8192) : Fin 8192 :=
  ⟨pg13MaskComplement m.val,
    Nat.xor_lt_two_pow (show 8191 < 2 ^ 13 by decide) (show m.val < 2 ^ 13 from m.isLt)⟩

theorem pg13_full_bits : ∀ i : Fin 13, (8191 : ℕ).testBit i.val = true := by decide +kernel

theorem pg13MaskSet_complement (m : Fin 8192) :
    pg13MaskSet (pg13ComplementMask m) = (pg13MaskSet m)ᶜ := by
  ext i
  simp [pg13MaskSet, pg13ComplementMask, pg13MaskComplement, Nat.testBit_xor, pg13_full_bits]

end Erdos539Geometry
