/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.OrthantExpansion

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Points above one actual anchor give distinct members of its forward fan. -/
theorem upper_set_card_le_fan {G F : Finset (ι → ℝ)} {a : ι → ℝ}
    (hGF : G ⊆ F) (hGa : ∀ x ∈ G, ∀ i, a i ≤ x i) : G.card ≤ (fan F a).card := by
  apply Finset.card_le_card_of_injOn (fun x ↦ pdiff x a)
  · intro x hx
    exact mem_fan.mpr ⟨x, hGF hx, rfl⟩
  · intro x hx y hy hxy
    funext i
    have hh := congrFun hxy i
    change max (x i - a i) 0 = max (y i - a i) 0 at hh
    rw [max_eq_left (sub_nonneg.mpr (hGa x hx i)), max_eq_left (sub_nonneg.mpr (hGa y hy i))] at hh
    linarith

/-- HLP's successive upper-tail deletion yields a single original anchor,
with the exact product-of-projections bound and no imported proof assumption. -/
theorem exists_orthant_anchor {F : Finset (ι → ℝ)} (hF : F.Nonempty)
    (hd : 0 < Fintype.card ι) :
    ∃ a ∈ F, F.card ^ Fintype.card ι ≤
      Fintype.card ι ^ Fintype.card ι *
        (∏ i : ι, (F.image (lineProjection i)).card) * (fan F a).card := by
  classical
  let n := F.card
  let d := Fintype.card ι
  let Q := fun i : ι ↦ (F.image (lineProjection i)).card
  let k := fun i : ι ↦ (n - 1) / (d * Q i)
  let is := (Finset.univ : Finset ι).toList
  have hn : 0 < n := hF.card_pos
  have hQ (i : ι) : 0 < Q i := (hF.image (lineProjection i)).card_pos
  have hk (i : ι) : k i * Q i ≤ (n - 1) / d := by
    apply (Nat.le_div_iff_mul_le hd).mpr
    have h := Nat.div_mul_le_self (n - 1) (d * Q i)
    change k i * (d * Q i) ≤ n - 1 at h
    nlinarith
  have hsum : ∑ i : ι, k i * Q i ≤ n - 1 := by
    have h := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset ι)) ↦ hk i)
    have he : (∑ _i : ι, (n - 1) / d) = d * ((n - 1) / d) := by simp [d]
    rw [he] at h
    exact h.trans (Nat.mul_div_le (n - 1) d)
  have hbudget := trimCoordinates_card_budget F k is
  dsimp only [is] at hbudget
  rw [Finset.sum_map_toList] at hbudget
  have hT : (trimCoordinates F k is).Nonempty := by
    apply Finset.card_pos.mp
    change n ≤ (trimCoordinates F k is).card + ∑ i : ι, k i * Q i at hbudget
    omega
  obtain ⟨a, ha⟩ := hT
  obtain ⟨G, hGF, hGa, _hGoff, hGcard⟩ := trimCoordinates_expansion F k is (Finset.nodup_toList _) ha
  dsimp only [is] at hGcard
  rw [Finset.prod_map_toList] at hGcard
  have hfan : (∏ i : ι, (k i + 1)) ≤ (fan F a).card := hGcard.trans (upper_set_card_le_fan hGF hGa)
  have hlower (i : ι) : n ≤ (k i + 1) * d * Q i := by
    have hp : 0 < d * Q i := Nat.mul_pos hd (hQ i)
    have h := (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self ((n - 1) / (d * Q i)))
    change n - 1 < (k i + 1) * (d * Q i) at h
    have he : (k i + 1) * (d * Q i) = (k i + 1) * d * Q i := by ring
    rw [he] at h
    omega
  have hprod := Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le n) (fun i (_hi : i ∈ (Finset.univ : Finset ι)) ↦ hlower i)
  simp only [Finset.prod_const, Finset.card_univ, Finset.prod_mul_distrib] at hprod
  refine ⟨a, trimCoordinates_subset F k is ha, ?_⟩
  change n ^ d ≤ d ^ d * (∏ i : ι, Q i) * (fan F a).card
  calc
    n ^ d ≤ (∏ i : ι, (k i + 1)) * d ^ d * (∏ i : ι, Q i) := hprod
    _ ≤ (fan F a).card * d ^ d * (∏ i : ι, Q i) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hfan)
    _ = _ := by ring

/-- Exact division form of the anchored projection inequality used in the remarks. -/
theorem orthant_projection_fan_bound {F : Finset (ι → ℝ)} (hF : F.Nonempty)
    (hd : 0 < Fintype.card ι) :
    (F.card : ℝ) ^ Fintype.card ι /
      ((Fintype.card ι : ℝ) ^ Fintype.card ι *
        ∏ i : ι, ((F.image (lineProjection i)).card : ℝ)) ≤ maxFan F := by
  obtain ⟨a, ha, h⟩ := exists_orthant_anchor hF hd
  have hp : (0 : ℝ) < (Fintype.card ι : ℝ) ^ Fintype.card ι *
      ∏ i : ι, ((F.image (lineProjection i)).card : ℝ) := by
    apply mul_pos
    · exact pow_pos (by exact_mod_cast hd) _
    · exact Finset.prod_pos (fun i _ ↦ by exact_mod_cast (hF.image (lineProjection i)).card_pos)
  apply (div_le_iff₀ hp).mpr
  have h' := h.trans (Nat.mul_le_mul_left _ (card_fan_le_maxFan ha))
  have hh : (F.card : ℝ) ^ Fintype.card ι ≤
      (Fintype.card ι : ℝ) ^ Fintype.card ι *
        (∏ i : ι, ((F.image (lineProjection i)).card : ℝ)) * maxFan F := by exact_mod_cast h'
  nlinarith

end
end Erdos539Geometry
