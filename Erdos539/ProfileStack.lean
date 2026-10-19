/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PrefixTreeBasics

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical

/-- Suffix profiles admitted by at least one actual child. -/
def profileSuffixes {d : ℕ} (L : Finset ℝ) (G : ℝ → Finset (Fin d → ℕ)) : Finset (Fin d → ℕ) :=
  L.biUnion G

/-- Number of original child labels admitting one common suffix profile. -/
def profileMultiplicity {d : ℕ} (L : Finset ℝ) (G : ℝ → Finset (Fin d → ℕ)) (a : Fin d → ℕ) : ℕ :=
  (L.filter (fun t ↦ a ∈ G t)).card

/-- Exact feasible profiles at a parent: the first entry is the branching
number minus one, followed by a suffix profile shared by the selected children. -/
def profileStack {d : ℕ} (L : Finset ℝ) (G : ℝ → Finset (Fin d → ℕ)) : Finset (Fin (d + 1) → ℕ) :=
  (profileSuffixes L G).biUnion (fun a ↦ (Finset.range (profileMultiplicity L G a)).image (fun (j : ℕ) ↦ (Fin.cons j a : Fin (d + 1) → ℕ)))

@[simp] theorem mem_profileStack {d : ℕ} {L : Finset ℝ} {G : ℝ → Finset (Fin d → ℕ)}
    {a : Fin (d + 1) → ℕ} : a ∈ profileStack L G ↔ a 0 < profileMultiplicity L G (Fin.tail a) := by
  constructor
  · intro ha
    obtain ⟨b, _hb, hj⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hj
    have h0 := congrFun he 0
    have ht := congrArg Fin.tail he
    simp only [Fin.cons_zero] at h0
    simp only [Fin.tail_cons] at ht
    simpa only [← h0, ← ht] using Finset.mem_range.mp hj
  · intro ha
    have hc : 0 < (L.filter (fun t ↦ Fin.tail a ∈ G t)).card := lt_of_le_of_lt (Nat.zero_le _) ha
    obtain ⟨t, ht⟩ := Finset.card_pos.mp hc
    have hs : Fin.tail a ∈ profileSuffixes L G :=
      Finset.mem_biUnion.mpr ⟨t, (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2⟩
    exact Finset.mem_biUnion.mpr ⟨Fin.tail a, hs,
      Finset.mem_image.mpr ⟨a 0, Finset.mem_range.mpr ha, Fin.cons_self_tail a⟩⟩

theorem profileStack_card {d : ℕ} (L : Finset ℝ) (G : ℝ → Finset (Fin d → ℕ)) :
    (profileStack L G).card = ∑ t ∈ L, (G t).card := by
  have hdis : (profileSuffixes L G : Set (Fin d → ℕ)).PairwiseDisjoint
      (fun a ↦ (Finset.range (profileMultiplicity L G a)).image (fun (j : ℕ) ↦ (Fin.cons j a : Fin (d + 1) → ℕ))) := by
    intro a _ha b _hb hab
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    obtain ⟨j, _hj, hjx⟩ := Finset.mem_image.mp hxa
    obtain ⟨k, _hk, hkx⟩ := Finset.mem_image.mp hxb
    have hh := congrArg Fin.tail (hjx.trans hkx.symm)
    exact hab (by simpa only [Fin.tail_cons] using hh)
  rw [profileStack, Finset.card_biUnion hdis]
  have him (a : Fin d → ℕ) :
      ((Finset.range (profileMultiplicity L G a)).image (fun (j : ℕ) ↦ (Fin.cons j a : Fin (d + 1) → ℕ))).card = profileMultiplicity L G a := by
    have hi : Function.Injective (fun (j : ℕ) ↦ (Fin.cons j a : Fin (d + 1) → ℕ)) := by
      intro j k h
      simpa only [Fin.cons_zero] using congrFun h 0
    rw [Finset.card_image_of_injective _ hi, Finset.card_range]
  simp_rw [him, profileMultiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have he : (profileSuffixes L G).filter (fun a ↦ a ∈ G t) = G t := by
    ext a
    constructor
    · intro ha
      exact (Finset.mem_filter.mp ha).2
    · intro ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨t, ht, ha⟩, ha⟩
  rw [← Finset.sum_filter, he]

theorem profileMultiplicity_mono {d : ℕ} {L L' : Finset ℝ} {G G' : ℝ → Finset (Fin d → ℕ)}
    (hL : L ⊆ L') (hG : ∀ t ∈ L, G t ⊆ G' t) (a : Fin d → ℕ) :
    profileMultiplicity L G a ≤ profileMultiplicity L' G' a := by
  apply Finset.card_le_card
  intro t ht
  obtain ⟨ht, ha⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hL ht, hG t ht ha⟩

theorem profileStack_mono {d : ℕ} {L L' : Finset ℝ} {G G' : ℝ → Finset (Fin d → ℕ)}
    (hL : L ⊆ L') (hG : ∀ t ∈ L, G t ⊆ G' t) : profileStack L G ⊆ profileStack L' G' := by
  intro a ha
  exact mem_profileStack.mpr ((mem_profileStack.mp ha).trans_le (profileMultiplicity_mono hL hG _))

end
end Erdos539Geometry
