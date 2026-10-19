/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteTripleCover

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {α : Type*}

/-- Double counting with a prescribed multiplicity in every k-subset. -/
theorem uniform_multicover_choose_bound (S : Finset α) (E : Finset (Finset α)) {j k r : ℕ}
    (hjk : j ≤ k) (hkN : k ≤ S.card)
    (hE : ∀ e ∈ E, e ⊆ S ∧ e.card = j)
    (hcover : ∀ U ∈ S.powersetCard k, r ≤ (E.filter (fun e ↦ e ⊆ U)).card) :
    r * S.card.choose j ≤ E.card * k.choose j := by
  have hcount : r * S.card.choose k ≤ E.card * (S.card - j).choose (k - j) := by
    calc
      _ = ∑ _U ∈ S.powersetCard k, r := by simp; ring
      _ ≤ ∑ U ∈ S.powersetCard k, (E.filter (fun e ↦ e ⊆ U)).card :=
        Finset.sum_le_sum hcover
      _ = ∑ e ∈ E, ((S.powersetCard k).filter (fun U ↦ e ⊆ U)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
      _ ≤ ∑ _e ∈ E, (S.card - j).choose (k - j) := by
        apply Finset.sum_le_sum
        intro e he
        exact card_containing_subsets_le S e (hE e he).1 (hE e he).2
      _ = _ := by simp
  have hmul := Nat.mul_le_mul_right (k.choose j) hcount
  have hchoose := Nat.choose_mul (n := S.card) hjk
  have hpos : 0 < (S.card - j).choose (k - j) := Nat.choose_pos (Nat.sub_le_sub_right hkN j)
  have hfinal : (r * S.card.choose j) * (S.card - j).choose (k - j) ≤
      (E.card * k.choose j) * (S.card - j).choose (k - j) := by
    calc
      _ = r * (S.card.choose k * k.choose j) := by rw [hchoose]; ring
      _ ≤ (E.card * (S.card - j).choose (k - j)) * k.choose j := by
        simpa only [mul_assoc] using hmul
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hfinal hpos

/-- Delete one selected vertex per edge. The remainder has no edge, so
the independence bound forces at least |U|-r edges inside U. -/
theorem cover_induced_edge_count (S : Finset α) (E : Finset (Finset α)) (r : ℕ)
    (hne : ∀ e ∈ E, e.Nonempty)
    (hcover : ∀ W ∈ S.powersetCard (r + 1), ∃ e ∈ E, e ⊆ W)
    (U : Finset α) (hUS : U ⊆ S) :
    U.card ≤ r + (E.filter (fun e ↦ e ⊆ U)).card := by
  let F := E.filter (fun e ↦ e ⊆ U)
  have hF (e : F) : e.val.Nonempty := hne e.val (Finset.mem_filter.mp e.property).1
  let v : F → α := fun e ↦ Classical.choose (hF e)
  have hv (e : F) : v e ∈ e.val := Classical.choose_spec (hF e)
  let V := Finset.univ.image v
  have hV : V.card ≤ F.card := by
    exact (Finset.card_image_le).trans_eq (by simp)
  have hA : (U \ V).card ≤ r := by
    by_contra hnot
    obtain ⟨W, hW, hcard⟩ := Finset.exists_subset_card_eq (show r + 1 ≤ (U \ V).card by omega)
    have hWS := hW.trans (Finset.sdiff_subset.trans hUS)
    obtain ⟨e, he, heW⟩ := hcover W (Finset.mem_powersetCard.mpr ⟨hWS, hcard⟩)
    have heF : e ∈ F := Finset.mem_filter.mpr ⟨he, heW.trans (hW.trans Finset.sdiff_subset)⟩
    let t : F := ⟨e, heF⟩
    have ht : v t ∈ U \ V := hW (heW (hv t))
    exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩)
  have hU : U ⊆ (U \ V) ∪ V := by
    intro x hx
    by_cases hxV : x ∈ V
    · exact Finset.mem_union_right _ hxV
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxV⟩)
  have hc := (Finset.card_le_card hU).trans (Finset.card_union_le _ _)
  change U.card ≤ r + F.card
  omega

/-- The exact quadratic independence-number bound needed by the sharper
box selector. A factor two comes from exchanging the ordered corners. -/
theorem triple_multicover_size_bound (S : Finset α) (E : Finset (Finset α)) {r B : ℕ}
    (hr : 2 ≤ r) (hrN : 2 * r ≤ S.card) (hB : 1 ≤ B)
    (hE : ∀ e ∈ E, e ⊆ S ∧ e.card = 3)
    (hcover : ∀ U ∈ S.powersetCard (2 * r), r ≤ (E.filter (fun e ↦ e ⊆ U)).card)
    (hsize : 2 * E.card ≤ S.card ^ 2 * B) :
    S.card ≤ 4 * r ^ 2 * B := by
  have hc := uniform_multicover_choose_bound S E (by omega : 3 ≤ 2 * r) hrN hE hcover
  have hfall (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose n 3
    norm_num [Nat.descFactorial_succ, Nat.factorial] at h
    nlinarith
  have hm := Nat.mul_le_mul_left 12 hc
  have h1 : 2 * r * (S.card * (S.card - 1) * (S.card - 2)) ≤
      2 * E.card * (2 * r * (2 * r - 1) * (2 * r - 2)) := by
    nlinarith [hfall S.card, hfall (2 * r)]
  have h2 := h1.trans (Nat.mul_le_mul_right _ hsize)
  have h3 : S.card * (S.card - 1) * (S.card - 2) ≤
      S.card ^ 2 * B * ((2 * r - 1) * (2 * r - 2)) := by
    have hm :
      2 * r * (S.card * (S.card - 1) * (S.card - 2)) ≤
      2 * r * (S.card ^ 2 * B * ((2 * r - 1) * (2 * r - 2))) := by nlinarith only [h2]
    exact Nat.le_of_mul_le_mul_left hm (by positivity)
  have hN : 4 ≤ S.card := by omega
  have hn1 : S.card - 1 + 1 = S.card := by omega
  have hn2 : S.card - 2 + 2 = S.card := by omega
  have h4 : S.card * S.card ≤ S.card * (B * ((2 * r - 1) * (2 * r - 2)) + 3) := by
    have hn := Nat.le_of_mul_le_mul_left
      (by nlinarith [h3] : S.card * ((S.card - 1) * (S.card - 2)) ≤
        S.card * (S.card * B * ((2 * r - 1) * (2 * r - 2)))) (by omega)
    nlinarith
  have h5 := Nat.le_of_mul_le_mul_left h4 (by omega : 0 < S.card)
  have hr1 : 2 * r - 1 + 1 = 2 * r := by omega
  have hr2 : 2 * r - 2 + 2 = 2 * r := by omega
  have hcoef : (2 * r - 1) * (2 * r - 2) + 4 ≤ 4 * r ^ 2 := by nlinarith
  have hcoefB := Nat.mul_le_mul_left B hcoef
  nlinarith

end
end Erdos539Geometry
