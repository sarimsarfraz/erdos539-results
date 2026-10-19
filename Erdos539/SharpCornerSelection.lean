/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CornerMultiplicity
import Erdos539.FiniteUniformMulticover

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*} [Fintype ι]

/-- The exact two-corner selector constant from the manuscript. The
proof is finite incidence counting, retaining coordinate ties. -/
theorem exists_large_corner_slice_sharp_of_coordinate {S : Finset (ι → ℝ)}
    (hS : S.Nonempty) (i : ι) :
    ∃ a ∈ S, ∃ b ∈ S,
      S.card ≤ 2 ^ (2 ^ Fintype.card ι + 2) * (cornerSlice S a b).card := by
  let r := 2 ^ (2 ^ (Fintype.card ι - 1))
  let B := (S ×ˢ S).sup (fun ab ↦ (cornerSlice S ab.1 ab.2).card)
  have hr : 2 ≤ r := by
    dsimp only [r]
    have hp : 1 ≤ 2 ^ (Fintype.card ι - 1) := Nat.succ_le_of_lt (pow_pos (by decide) _)
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hp
  have hB (a : ι → ℝ) (ha : a ∈ S) (b : ι → ℝ) (hb : b ∈ S) : (cornerSlice S a b).card ≤ B := by
    exact Finset.le_sup (b := (a, b)) (f := fun ab ↦ (cornerSlice S ab.1 ab.2).card)
      (Finset.mem_product.mpr ⟨ha, hb⟩)
  have hBpos : 1 ≤ B := by
    obtain ⟨a, ha⟩ := hS
    have hp : 0 < (cornerSlice S a a).card := Finset.card_pos.mpr
      ⟨a, mem_cornerSlice.mpr ⟨ha, inCornerBox_left a a⟩⟩
    exact (Nat.succ_le_iff.mpr hp).trans (hB a ha a ha)
  have hsize : S.card ≤ 4 * r ^ 2 * B := by
    by_cases hN : 2 * r ≤ S.card
    · apply triple_multicover_size_bound S (cornerEdges S) hr hN hBpos
        (fun _ he ↦ cornerEdges_spec S he)
      · intro U hU
        obtain ⟨hUS, hc⟩ := Finset.mem_powersetCard.mp hU
        have hne (e : Finset (ι → ℝ)) (he : e ∈ cornerEdges S) : e.Nonempty := by
          apply Finset.card_pos.mp
          rw [(cornerEdges_spec S he).2]
          decide
        have he := cover_induced_edge_count S (cornerEdges S) r hne (cornerEdges_cover S i) U hUS
        omega
      · exact (two_mul_card_cornerEdges_le_triples S).trans (card_cornerTriples_le S hB)
    · have hrpow : r ≤ r ^ 2 := by nlinarith
      nlinarith
  obtain ⟨ab, hab, he⟩ := Finset.exists_mem_eq_sup (S ×ˢ S) (hS.product hS)
    (fun ab ↦ (cornerSlice S ab.1 ab.2).card)
  have hd : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hexp : 2 ^ Fintype.card ι = 2 * 2 ^ (Fintype.card ι - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hd]
    rw [pow_add]
    norm_num
    ring
  have hconstant : 4 * r ^ 2 = 2 ^ (2 ^ Fintype.card ι + 2) := by
    dsimp only [r]
    rw [← pow_mul, hexp, pow_add]
    norm_num
    rw [Nat.mul_comm (2 ^ (Fintype.card ι - 1)) 2]
    ring
  refine ⟨ab.1, (Finset.mem_product.mp hab).1, ab.2, (Finset.mem_product.mp hab).2, ?_⟩
  dsimp only [B] at hsize
  rwa [he, hconstant] at hsize

/-- Zero-dimensional finite supports are included in the exact selector. -/
theorem exists_large_corner_slice_sharp {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    ∃ a ∈ S, ∃ b ∈ S,
      S.card ≤ 2 ^ (2 ^ Fintype.card ι + 2) * (cornerSlice S a b).card := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    obtain ⟨a, ha⟩ := hS
    refine ⟨a, ha, a, ha, ?_⟩
    have he : cornerSlice S a a = S := by
      ext x
      simp only [mem_cornerSlice, and_iff_left_iff_imp]
      intro _ i
      exact isEmptyElim i
    rw [he]
    have hp : 1 ≤ 2 ^ (2 ^ Fintype.card ι + 2) := Nat.succ_le_of_lt (pow_pos (by decide) _)
    nlinarith
  | inr h =>
    letI := h
    exact exists_large_corner_slice_sharp_of_coordinate hS (Classical.choice h)

end
end Erdos539Geometry
