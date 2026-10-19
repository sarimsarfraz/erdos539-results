/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PairCounting
import Mathlib.Data.Nat.Choose.Basic

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {α : Type*}

/-- Count k-subsets containing a prescribed j-subset, by deleting that subset. -/
theorem card_containing_subsets_le (S e : Finset α) {k j : ℕ}
    (he : e ⊆ S) (hej : e.card = j) :
    ((S.powersetCard k).filter (fun U ↦ e ⊆ U)).card ≤ (S.card - j).choose (k - j) := by
  have h := Finset.card_le_card_of_injOn (fun U : Finset α ↦ U \ e)
    (s := (S.powersetCard k).filter (fun U ↦ e ⊆ U))
    (t := (S \ e).powersetCard (k - j)) ?_ ?_
  · simpa only [Finset.card_powersetCard, Finset.card_sdiff_of_subset he, hej] using h
  · intro U hU
    obtain ⟨hUk, heU⟩ := Finset.mem_filter.mp hU
    obtain ⟨hUS, hUc⟩ := Finset.mem_powersetCard.mp hUk
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.sdiff_subset_sdiff hUS (Finset.Subset.refl e), ?_⟩
    rw [Finset.card_sdiff_of_subset heU, hUc, hej]
  · intro U hU V hV huv
    have heU := (Finset.mem_filter.mp hU).2
    have heV := (Finset.mem_filter.mp hV).2
    have hh := congrArg (fun W : Finset α ↦ W ∪ e) huv
    simpa only [Finset.sdiff_union_of_subset heU, Finset.sdiff_union_of_subset heV] using hh

/-- A family of j-subsets meeting every k-subset has the usual counting density. -/
theorem uniform_cover_choose_bound (S : Finset α) (E : Finset (Finset α)) {j k : ℕ}
    (hjk : j ≤ k) (hkN : k ≤ S.card)
    (hE : ∀ e ∈ E, e ⊆ S ∧ e.card = j)
    (hcover : ∀ U ∈ S.powersetCard k, ∃ e ∈ E, e ⊆ U) :
    S.card.choose j ≤ E.card * k.choose j := by
  have hsub : S.powersetCard k ⊆ E.biUnion (fun e ↦ (S.powersetCard k).filter (fun U ↦ e ⊆ U)) := by
    intro U hU
    obtain ⟨e, he, heU⟩ := hcover U hU
    exact Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_filter.mpr ⟨hU, heU⟩⟩
  have hcount : S.card.choose k ≤ E.card * (S.card - j).choose (k - j) := by
    calc
      _ = (S.powersetCard k).card := (Finset.card_powersetCard _ _).symm
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ e ∈ E, ((S.powersetCard k).filter (fun U ↦ e ⊆ U)).card := Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ E, (S.card - j).choose (k - j) := by
        apply Finset.sum_le_sum
        intro e he
        exact card_containing_subsets_le S e (hE e he).1 (hE e he).2
      _ = _ := by simp
  have hmul := Nat.mul_le_mul_right (k.choose j) hcount
  rw [Nat.choose_mul hjk] at hmul
  have hpos : 0 < (S.card - j).choose (k - j) := Nat.choose_pos (Nat.sub_le_sub_right hkN j)
  have hfinal : S.card.choose j * (S.card - j).choose (k - j) ≤
      (E.card * k.choose j) * (S.card - j).choose (k - j) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm ((S.card - j).choose (k - j)) (k.choose j)] using hmul
  exact Nat.le_of_mul_le_mul_right hfinal hpos

/-- A convenient polynomial consequence for triples. Keeping this over natural
numbers avoids probabilistic or asymptotic inputs in the box-selection step. -/
theorem triple_cover_size_bound (S : Finset α) (E : Finset (Finset α)) {k B : ℕ}
    (hk : 3 ≤ k) (hkN : k ≤ S.card) (hN : 4 ≤ S.card)
    (hE : ∀ e ∈ E, e ⊆ S ∧ e.card = 3)
    (hcover : ∀ U ∈ S.powersetCard k, ∃ e ∈ E, e ⊆ U)
    (hsize : E.card ≤ S.card ^ 2 * B) :
    S.card ≤ 4 * k ^ 3 * B := by
  have hc := uniform_cover_choose_bound S E hk hkN hE hcover
  have hfall (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose n 3
    norm_num [Nat.descFactorial_succ, Nat.factorial] at h
    nlinarith
  have hm := Nat.mul_le_mul_left 6 hc
  rw [← Nat.mul_assoc, hfall] at hm
  have hm' : S.card * (S.card - 1) * (S.card - 2) ≤ E.card * (k * (k - 1) * (k - 2)) := by
    simpa only [Nat.mul_assoc, Nat.mul_left_comm 6 E.card, hfall] using hm
  have hkprod : k * (k - 1) * (k - 2) ≤ k ^ 3 := by
    calc
      _ ≤ k * k * k := Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (Nat.sub_le _ _)
      _ = _ := by ring
  have hup := hm'.trans ((Nat.mul_le_mul hsize hkprod))
  have hlo : S.card ^ 3 ≤ 4 * (S.card * (S.card - 1) * (S.card - 2)) := by
    have h1 : S.card ≤ 2 * (S.card - 1) := by omega
    have h2 : S.card ≤ 2 * (S.card - 2) := by omega
    have h := Nat.mul_le_mul_left S.card (Nat.mul_le_mul h1 h2)
    nlinarith
  have hall : S.card ^ 2 * S.card ≤ S.card ^ 2 * (4 * k ^ 3 * B) := by nlinarith
  exact Nat.le_of_mul_le_mul_left hall (by positivity)

end
end Erdos539Geometry
