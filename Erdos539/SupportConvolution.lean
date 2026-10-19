/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.TensorConvolution

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]

theorem sumRepresentatives_card_eq (E : Finset (ι → ℕ)) (z : ι → ℕ) :
    (fiber (E ×ˢ E) (fun p ↦ p.1 + p.2) z).card = (sumRepresentatives E z).card := by
  apply Finset.card_bij (fun p _ ↦ p.1)
  · intro p hp
    obtain ⟨hp, he⟩ := mem_fiber.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨ha, ?_, ?_⟩
    · intro i
      have hi := congrFun he i
      change p.1 i ≤ z i
      change p.1 i + p.2 i = z i at hi
      omega
    · have he' : z - p.1 = p.2 := by
        funext i
        have hi := congrFun he i
        change z i - p.1 i = p.2 i
        change p.1 i + p.2 i = z i at hi
        omega
      rwa [he']
  · intro p hp q hq he
    have hp' := (mem_fiber.mp hp).2
    have hq' := (mem_fiber.mp hq).2
    apply Prod.ext he
    funext i
    have hi := congrFun hp' i
    have hj := congrFun hq' i
    have hk := congrFun he i
    change p.1 i + p.2 i = z i at hi
    change q.1 i + q.2 i = z i at hj
    omega
  · intro a ha
    obtain ⟨ha, haz, hb⟩ := Finset.mem_filter.mp ha
    refine ⟨(a, z - a), mem_fiber.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩, rfl⟩
    funext i
    exact Nat.add_sub_cancel' (haz i)

theorem sum_sumRepresentatives_card (E : Finset (ι → ℕ)) :
    ∑ z ∈ E + E, (sumRepresentatives E z).card = E.card ^ 2 := by
  have hm : (↑(E ×ˢ E) : Set ((ι → ℕ) × (ι → ℕ))).MapsTo (fun p ↦ p.1 + p.2) (↑(E + E)) := by
    intro p hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_add.mpr ⟨p.1, ha, p.2, hb, rfl⟩
  have h := card_eq_sum_card_parent (E ×ˢ E) (fun p ↦ p.1 + p.2) (E + E) hm
  simp_rw [sumRepresentatives_card_eq] at h
  simpa only [Finset.card_product, pow_two] using h.symm

theorem activeCoordinates_add_card_le (a b : ι → ℕ) :
    (activeCoordinates (a + b)).card ≤ (activeCoordinates a).card + (activeCoordinates b).card := by
  have hs : activeCoordinates (a + b) ⊆ activeCoordinates a ∪ activeCoordinates b := by
    intro i hi
    have hi' : 0 < a i + b i := (Finset.mem_filter.mp hi).2
    by_cases ha : 0 < a i
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

/-- The count of all pairs is bounded using the support of their sum. -/
theorem restricted_support_convolution {E : Finset (ι → ℕ)} {r : ℕ}
    (hr : ∀ a ∈ E, (activeCoordinates a).card ≤ r) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ a ∈ E, (boxVolume a : ℝ) ≤ M) :
    (E.card : ℝ) ^ 2 ≤ 16 ^ r * M * (E + E).card := by
  calc
    _ = ∑ z ∈ E + E, ((sumRepresentatives E z).card : ℝ) := by
      exact_mod_cast (sum_sumRepresentatives_card E).symm
    _ ≤ ∑ _z ∈ E + E, 16 ^ r * M := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
      have hs : (activeCoordinates (a + b)).card ≤ 2 * r := by
        have h := activeCoordinates_add_card_le a b
        have := hr a ha
        have := hr b hb
        omega
      have hp : (4 : ℝ) ^ (activeCoordinates (a + b)).card ≤ 16 ^ r := by
        calc
          _ ≤ (4 : ℝ) ^ (2 * r) := pow_le_pow_right₀ (by norm_num) hs
          _ = _ := by rw [pow_mul]; norm_num
      exact (sumRepresentatives_card_le hM0 hM (a + b)).trans (by nlinarith)
    _ = _ := by simp [mul_comm]

end
end Erdos539Geometry
