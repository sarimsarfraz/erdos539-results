/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CorrelationPairings
import Erdos539.ReferenceUniformRoot

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def countingIndicator (A : Finset G) (x : G) : ℝ := if x ∈ A then 1 else 0

theorem weightedEnergy_countingIndicator {A S : Finset G} (hA : A ⊆ S) :
    weightedEnergy S (countingIndicator A) = countingEnergy A := by
  rw [← weightedEnergy_support hA (countingIndicator A) (fun x _ hx ↦ by simp [countingIndicator, hx])]
  exact weightedEnergy_congr A (fun x hx ↦ by simp [countingIndicator, hx])

/-- Mixed differences are counted with literal indicator weights in a
common ambient support; no equality of the two sets is required. -/
theorem weightedCorrelation_countingIndicator {A B S : Finset G} (hA : A ⊆ S) (hB : B ⊆ S) (z : G) :
    weightedCorrelation S (countingIndicator A) (countingIndicator B) z =
      ((fiber (A ×ˢ B) (fun p ↦ p.1 - p.2) z).card : ℝ) := by
  have hf : fiber (A ×ˢ B) (fun p ↦ p.1 - p.2) z ⊆ fiber (S ×ˢ S) (fun p ↦ p.1 - p.2) z := by
    intro p hp
    obtain ⟨hp, he⟩ := mem_fiber.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    exact mem_fiber.mpr ⟨Finset.mem_product.mpr ⟨hA ha, hB hb⟩, he⟩
  unfold weightedCorrelation
  calc
    _ = ∑ p ∈ fiber (A ×ˢ B) (fun p ↦ p.1 - p.2) z, countingIndicator A p.1 * countingIndicator B p.2 := by
      symm
      apply Finset.sum_subset hf
      intro p hp hn
      have hpz := (mem_fiber.mp hp).2
      by_cases ha : p.1 ∈ A
      · have hb : p.2 ∉ B := fun hb ↦ hn (mem_fiber.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hpz⟩)
        simp [countingIndicator, hb]
      · simp [countingIndicator, ha]
    _ = _ := by
      have he : ∀ p ∈ fiber (A ×ˢ B) (fun p ↦ p.1 - p.2) z,
          countingIndicator A p.1 * countingIndicator B p.2 = 1 := by
        intro p hp
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp (mem_fiber.mp hp).1
        simp [countingIndicator, ha, hb]
      simp_rw [Finset.sum_congr rfl he]
      simp

def mixedCountingEnergy (A B : Finset G) : ℝ :=
  ∑ z ∈ A - B, (((fiber (A ×ˢ B) (fun p ↦ p.1 - p.2) z).card : ℝ) ^ 2)

theorem mixedCountingEnergy_eq_difference {A B S : Finset G} (hA : A ⊆ S) (hB : B ⊆ S) :
    mixedCountingEnergy A B = differenceMixedEnergy S (countingIndicator A) (countingIndicator B)
      (countingIndicator A) (countingIndicator B) := by
  unfold mixedCountingEnergy differenceMixedEnergy
  simp_rw [weightedCorrelation_countingIndicator hA hB, ← pow_two]
  apply Finset.sum_subset (Finset.sub_subset_sub hA hB)
  intro z _ hz
  have he : fiber (A ×ˢ B) (fun p ↦ p.1 - p.2) z = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp, he⟩ := mem_fiber.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    exact hz (Finset.mem_sub.mpr ⟨p.1, ha, p.2, hb, he⟩)
  simp [he]

/-- Cauchy--Schwarz for the two actual difference-representation functions. -/
theorem mixedCountingEnergy_sq_le (A B : Finset G) :
    mixedCountingEnergy A B ^ 2 ≤ countingEnergy A * countingEnergy B := by
  rw [mixedCountingEnergy_eq_difference (Finset.subset_union_left : A ⊆ A ∪ B) Finset.subset_union_right,
    differenceMixedEnergy_eq_mixed]
  have h := crossWeightedEnergy_sq_le (A ∪ B) (countingIndicator A) (countingIndicator B)
  rwa [weightedEnergy_countingIndicator Finset.subset_union_left,
    weightedEnergy_countingIndicator Finset.subset_union_right] at h

theorem mixedCountingEnergy_nonneg (A B : Finset G) : 0 ≤ mixedCountingEnergy A B :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem sum_mixed_difference_representations (A B : Finset G) :
    (∑ z ∈ A - B, ((fiber (A ×ˢ B) (fun p ↦ p.1 - p.2) z).card : ℝ)) = (A.card : ℝ) * B.card := by
  calc
    _ = ∑ z ∈ A - B, ∑ _p ∈ fiber (A ×ˢ B) (fun p ↦ p.1 - p.2) z, (1 : ℝ) := by simp
    _ = ∑ _p ∈ A ×ˢ B, (1 : ℝ) := by
      refine @Finset.sum_fiberwise_of_maps_to (G × G) G ℝ _ (A ×ˢ B) (A - B)
        (Classical.decEq G) (fun p ↦ p.1 - p.2) ?_ (fun _ ↦ 1)
      intro p hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      exact Finset.mem_sub.mpr ⟨p.1, ha, p.2, hb, rfl⟩
    _ = _ := by simp

theorem card_product_sq_le_mixedCountingEnergy (A B : Finset G) :
    (A.card : ℝ) ^ 2 * (B.card : ℝ) ^ 2 ≤ (A - B).card * mixedCountingEnergy A B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (A - B) (fun _ ↦ (1 : ℝ))
    (fun z ↦ ((fiber (A ×ˢ B) (fun p ↦ p.1 - p.2) z).card : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [sum_mixed_difference_representations, mul_pow] at h
  exact h

theorem mixedCountingEnergy_le_sqrt (A B : Finset G) :
    mixedCountingEnergy A B ≤ Real.sqrt (countingEnergy A) * Real.sqrt (countingEnergy B) := by
  apply (sq_le_sq₀ (mixedCountingEnergy_nonneg A B) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (show 0 ≤ countingEnergy A from weightedEnergy_nonneg A (fun _ ↦ 1)),
    Real.sq_sqrt (show 0 ≤ countingEnergy B from weightedEnergy_nonneg B (fun _ ↦ 1))]
  exact mixedCountingEnergy_sq_le A B

/-- The quantity beta_F = |F|^2 / sqrt(E(F)) in the collective bound. -/
def countingEnergyScale (A : Finset G) : ℝ := (A.card : ℝ) ^ 2 / Real.sqrt (countingEnergy A)

theorem countingEnergyScale_nonneg (A : Finset G) : 0 ≤ countingEnergyScale A :=
  div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)

theorem countingEnergyScale_sq (A : Finset G) :
    countingEnergyScale A ^ 2 = (A.card : ℝ) ^ 4 / countingEnergy A := by
  rw [countingEnergyScale, div_pow, Real.sq_sqrt (show 0 ≤ countingEnergy A from weightedEnergy_nonneg A (fun _ ↦ 1))]
  congr 1
  ring

/-- Mixed differences of two nonempty actual sets dominate the product
of their individual counting-energy scales. -/
theorem countingEnergyScale_mul_le_sub {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) :
    countingEnergyScale A * countingEnergyScale B ≤ (A - B).card := by
  unfold countingEnergyScale
  rw [div_mul_div_comm]
  apply (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr (countingEnergy_pos hA))
    (Real.sqrt_pos.mpr (countingEnergy_pos hB)))).mpr
  exact (card_product_sq_le_mixedCountingEnergy A B).trans
    (mul_le_mul_of_nonneg_left (mixedCountingEnergy_le_sqrt A B) (Nat.cast_nonneg _))

end
end Erdos539Geometry
