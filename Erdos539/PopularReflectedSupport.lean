/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectedSupportCertificate
import Erdos539.ReferenceUniformRoot

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem weightedConvolution_one_eq_reflected_card (S : Finset G) (z : G) :
    weightedConvolution S (fun _ ↦ 1) (fun _ ↦ 1) z = ((reflectedSupport S z).card : ℝ) := by
  simp only [weightedConvolution, Finset.sum_const, nsmul_eq_mul, mul_one,
    sumFiber_card_eq_representation_card, reflectedSupport]

theorem countingEnergy_eq_reflected_square_sum (S : Finset G) :
    countingEnergy S = ∑ z ∈ S + S, ((reflectedSupport S z).card : ℝ) ^ 2 := by
  simp only [countingEnergy, weightedEnergy, weightedConvolution_one_eq_reflected_card]

theorem sum_reflectedSupport_card (S : Finset G) :
    (∑ z ∈ S + S, ((reflectedSupport S z).card : ℝ)) = (S.card : ℝ) ^ 2 := by
  have h := sum_weighted_fibers S (fun _ ↦ (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_product, Nat.cast_mul,
    sumFiber_card_eq_representation_card] at h
  simpa only [reflectedSupport, pow_two] using h

/-- The popular sum supplies a literal reflected intersection of size
at least E(S)/|S|^2, with its actual sum center. -/
theorem exists_popular_reflectedSupport {S : Finset G} (hS : S.Nonempty) :
    ∃ w ∈ S + S, countingEnergy S / (S.card : ℝ) ^ 2 ≤ (reflectedSupport S w).card := by
  obtain ⟨w, hw, hm⟩ := (S + S).exists_max_image (fun z ↦ (reflectedSupport S z).card) (hS.add hS)
  refine ⟨w, hw, ?_⟩
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
  rw [countingEnergy_eq_reflected_square_sum, ← sum_reflectedSupport_card, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hc : ((reflectedSupport S z).card : ℝ) ≤ (reflectedSupport S w).card := by exact_mod_cast hm z hz
  simpa only [pow_two] using mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)

def popularReflectedCenter (S : Finset G) (hS : S.Nonempty) : G :=
  Classical.choose (exists_popular_reflectedSupport hS)

theorem popularReflectedCenter_bound (S : Finset G) (hS : S.Nonempty) :
    countingEnergy S / (S.card : ℝ) ^ 2 ≤ (reflectedSupport S (popularReflectedCenter S hS)).card :=
  (Classical.choose_spec (exists_popular_reflectedSupport hS)).2

end
end Erdos539Geometry
