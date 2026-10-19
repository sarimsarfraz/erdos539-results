/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CornerGeometry
import Erdos539.FiniteTripleCover

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*}

/-- Ordered corners together with a point between them; repetitions allowed. -/
def cornerTriples (S : Finset (ι → ℝ)) : Finset (((ι → ℝ) × (ι → ℝ)) × (ι → ℝ)) :=
  ((S ×ˢ S) ×ˢ S).filter (fun t ↦ InCornerBox t.1.1 t.1.2 t.2)

def cornerTripleSet (t : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ)) : Finset (ι → ℝ) :=
  {t.1.1, t.1.2, t.2}

def cornerEdges (S : Finset (ι → ℝ)) : Finset (Finset (ι → ℝ)) :=
  ((cornerTriples S).image cornerTripleSet).filter (fun e ↦ e.card = 3)

theorem cornerEdges_spec (S : Finset (ι → ℝ)) {e : Finset (ι → ℝ)} (he : e ∈ cornerEdges S) :
    e ⊆ S ∧ e.card = 3 := by
  classical
  obtain ⟨him, hc⟩ := Finset.mem_filter.mp he
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp him
  obtain ⟨hp, _hb⟩ := Finset.mem_filter.mp ht
  obtain ⟨hab, hz⟩ := Finset.mem_product.mp hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  exact ⟨by simp only [cornerTripleSet, Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨ha, hb, hz⟩, hc⟩

theorem card_cornerEdges_le (S : Finset (ι → ℝ)) {B : ℕ}
    (hB : ∀ a ∈ S, ∀ b ∈ S, (cornerSlice S a b).card ≤ B) :
    (cornerEdges S).card ≤ S.card ^ 2 * B := by
  classical
  have ht : (cornerTriples S).card ≤ S.card ^ 2 * B := by
    have maps : (cornerTriples S : Set (((ι → ℝ) × (ι → ℝ)) × (ι → ℝ))).MapsTo
        Prod.fst (↑(S ×ˢ S) : Set ((ι → ℝ) × (ι → ℝ))) := by
      intro t ht
      exact (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1
    rw [card_eq_sum_card_parent (cornerTriples S) Prod.fst (S ×ˢ S) maps]
    calc
      _ ≤ ∑ _ab ∈ S ×ˢ S, B := by
        apply Finset.sum_le_sum
        intro ab hab
        have hf := Finset.card_le_card_of_injOn Prod.snd
          (s := fiber (cornerTriples S) Prod.fst ab) (t := cornerSlice S ab.1 ab.2) ?_ ?_
        · exact hf.trans (hB ab.1 (Finset.mem_product.mp hab).1 ab.2 (Finset.mem_product.mp hab).2)
        · intro t ht
          obtain ⟨ht, he⟩ := mem_fiber.mp ht
          obtain ⟨hp, hb⟩ := Finset.mem_filter.mp ht
          apply mem_cornerSlice.mpr
          refine ⟨(Finset.mem_product.mp hp).2, ?_⟩
          simpa only [he] using hb
        · intro t ht u hu he
          have h1 := (mem_fiber.mp ht).2
          have h2 := (mem_fiber.mp hu).2
          exact Prod.ext (h1.trans h2.symm) he
      _ = _ := by simp [pow_two]
  exact (Finset.card_filter_le _ _).trans ((Finset.card_image_le).trans ht)

variable [Fintype ι]

theorem cornerEdges_cover (S : Finset (ι → ℝ)) (i : ι) :
    ∀ U ∈ S.powersetCard (2 ^ (2 ^ (Fintype.card ι - 1)) + 1),
      ∃ e ∈ cornerEdges S, e ⊆ U := by
  classical
  letI : DecidableEq (ι → ℝ) := Classical.decEq _
  letI : DecidableEq (Finset (ι → ℝ)) := @Finset.decidableEq _ (Classical.decEq _)
  intro U hU
  obtain ⟨hUS, hc⟩ := Finset.mem_powersetCard.mp hU
  obtain ⟨a, ha, b, hb, c, hcU, hab, hbc, hac, hbox⟩ :=
    exists_corner_triple_of_large U i (by omega)
  refine ⟨cornerTripleSet ((a, c), b), ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨((a, c), b), ?_, rfl⟩, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hUS ha, hUS hcU⟩, hUS hb⟩, hbox⟩
    · simp [cornerTripleSet, hab, hac, Ne.symm hbc]
  · simp only [cornerTripleSet, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨ha, hcU, hb⟩

/-- Deterministic box selection from triple incidence counting. Its slightly
weaker density than random alteration still gives the requested final fan constant. -/
theorem exists_large_corner_slice {S : Finset (ι → ℝ)} (hS : S.Nonempty) (i : ι) :
    ∃ a ∈ S, ∃ b ∈ S,
      S.card ≤ 2 ^ (3 * 2 ^ (Fintype.card ι - 1) + 5) * (cornerSlice S a b).card := by
  classical
  let r := 2 ^ (2 ^ (Fintype.card ι - 1))
  let k := r + 1
  let B := (S ×ˢ S).sup (fun ab ↦ (cornerSlice S ab.1 ab.2).card)
  have hr : 2 ≤ r := by
    dsimp only [r]
    have hp : 1 ≤ 2 ^ (Fintype.card ι - 1) := Nat.succ_le_of_lt (pow_pos (by decide) _)
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hp
  have hB (a : ι → ℝ) (ha : a ∈ S) (b : ι → ℝ) (hb : b ∈ S) : (cornerSlice S a b).card ≤ B := by
    dsimp only [B]
    exact Finset.le_sup (b := (a, b)) (f := fun ab ↦ (cornerSlice S ab.1 ab.2).card) (Finset.mem_product.mpr ⟨ha, hb⟩)
  have hBpos : 1 ≤ B := by
    obtain ⟨a, ha⟩ := hS
    have hp : 0 < (cornerSlice S a a).card := Finset.card_pos.mpr
      ⟨a, mem_cornerSlice.mpr ⟨ha, inCornerBox_left a a⟩⟩
    exact (Nat.succ_le_iff.mpr hp).trans (hB a ha a ha)
  have hsize : S.card ≤ 32 * r ^ 3 * B := by
    by_cases hkN : k ≤ S.card
    · by_cases hN : 4 ≤ S.card
      · have hh := triple_cover_size_bound S (cornerEdges S) (by dsimp only [k]; omega) hkN hN
          (fun _ he ↦ cornerEdges_spec S he) (cornerEdges_cover S i) (card_cornerEdges_le S hB)
        have hk : k ≤ 2 * r := by dsimp only [k]; omega
        calc
          S.card ≤ 4 * k ^ 3 * B := hh
          _ ≤ 4 * (2 * r) ^ 3 * B := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk 3))
          _ = _ := by ring
      · have hp : 1 ≤ r ^ 3 := Nat.succ_le_of_lt (pow_pos (by omega) _)
        nlinarith
    · have hp : r ≤ r ^ 3 := by
        simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < r) (by decide : 1 ≤ 3)
      dsimp only [k] at hkN
      nlinarith
  obtain ⟨ab, hab, he⟩ := Finset.exists_mem_eq_sup (S ×ˢ S) (hS.product hS)
    (fun ab ↦ (cornerSlice S ab.1 ab.2).card)
  have hconstant : 32 * r ^ 3 = 2 ^ (3 * 2 ^ (Fintype.card ι - 1) + 5) := by
    dsimp only [r]
    rw [← pow_mul, pow_add]
    norm_num
    ring_nf
  refine ⟨ab.1, (Finset.mem_product.mp hab).1, ab.2, (Finset.mem_product.mp hab).2, ?_⟩
  dsimp only [B] at hsize
  rwa [he, hconstant] at hsize

end
end Erdos539Geometry
