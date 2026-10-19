/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyTransport
import Erdos539.StationaryLawCorrelation

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Partition function for an arbitrary finite weight, without a norm
maximization or l2-normalization assumption. -/
def weightedGibbsPartition (S : Finset G) (f : S → ℝ) : ℝ :=
  weightedEnergy S (extendWeight S f)

def weightedGibbsMass (S : Finset G) (f : S → ℝ) (a b c d : S) : ℝ :=
  additiveQuadrupleWeight S f a b c d / weightedGibbsPartition S f

def weightedGibbsEndpoint (S : Finset G) (f : S → ℝ) (a : S) : ℝ :=
  ∑ b, ∑ c, ∑ d, weightedGibbsMass S f a b c d

theorem weightedGibbsPartition_eq_sum (S : Finset G) (f : S → ℝ) :
    weightedGibbsPartition S f = ∑ a, ∑ b, ∑ c, ∑ d, additiveQuadrupleWeight S f a b c d := by
  exact weightedEnergy_subtype S f

theorem weightedGibbsPartition_pos {S : Finset G} (hS : S.Nonempty)
    {f : S → ℝ} (hf : ∀ x, 0 < f x) : 0 < weightedGibbsPartition S f := by
  obtain ⟨a, ha⟩ := hS
  have hp : 0 < ∑ x : S, f x ^ 2 := lt_of_lt_of_le (sq_pos_of_pos (hf ⟨a, ha⟩))
    (Finset.single_le_sum (fun x _ ↦ sq_nonneg (f x)) (Finset.mem_univ (⟨a, ha⟩ : S)))
  have h := weightedEnergy_ge_squareSum_sq S (extendWeight S f)
  rw [weightSquareSum_extend] at h
  exact (sq_pos_of_pos hp).trans_le h

theorem weightedGibbsMass_nonneg {S : Finset G} {f : S → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a b c d : S) : 0 ≤ weightedGibbsMass S f a b c d := by
  apply div_nonneg _ (weightedEnergy_nonneg _ _)
  unfold additiveQuadrupleWeight
  split_ifs
  · exact mul_nonneg (mul_nonneg (hf a) (hf b)) (mul_nonneg (hf c) (hf d))
  · rfl

theorem weightedGibbsMass_swap_left (S : Finset G) (f : S → ℝ) (a b c d : S) :
    weightedGibbsMass S f a b c d = weightedGibbsMass S f b a c d := by
  rw [weightedGibbsMass, weightedGibbsMass, additiveQuadrupleWeight_swap_left]

theorem weightedGibbsMass_swap_right (S : Finset G) (f : S → ℝ) (a b c d : S) :
    weightedGibbsMass S f a b c d = weightedGibbsMass S f a b d c := by
  rw [weightedGibbsMass, weightedGibbsMass, additiveQuadrupleWeight_swap_right]

theorem weightedGibbsMass_swap_sides (S : Finset G) (f : S → ℝ) (a b c d : S) :
    weightedGibbsMass S f a b c d = weightedGibbsMass S f c d a b := by
  rw [weightedGibbsMass, weightedGibbsMass, additiveQuadrupleWeight_swap_sides]

theorem weightedGibbsMass_second (S : Finset G) (f : S → ℝ) (b : S) :
    (∑ a, ∑ c, ∑ d, weightedGibbsMass S f a b c d) = weightedGibbsEndpoint S f b := by
  simp_rw [weightedGibbsMass_swap_left S f _ b]
  rfl

theorem weightedGibbsMass_third (S : Finset G) (f : S → ℝ) (c : S) :
    (∑ a, ∑ b, ∑ d, weightedGibbsMass S f a b c d) = weightedGibbsEndpoint S f c := by
  simp_rw [weightedGibbsMass_swap_sides S f _ _ c]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  rfl

theorem weightedGibbsMass_fourth (S : Finset G) (f : S → ℝ) (d : S) :
    (∑ a, ∑ b, ∑ c, weightedGibbsMass S f a b c d) = weightedGibbsEndpoint S f d := by
  simp_rw [weightedGibbsMass_swap_right S f _ _ _ d]
  exact weightedGibbsMass_third S f d

/-- A general nonnegative Gibbs weight has identical endpoint marginals;
this symmetry does not assert that its weights maximize ordinary energy. -/
def weightedGibbsLaw (S : Finset G) (f : S → ℝ) (hf : ∀ x, 0 ≤ f x) :
    StationaryAdditiveLaw S (weightedGibbsEndpoint S f) where
  mass := weightedGibbsMass S f
  nonneg := weightedGibbsMass_nonneg hf
  supported := by
    intro a b c d h
    simp [weightedGibbsMass, additiveQuadrupleWeight, h]
  first := fun _ ↦ rfl
  second := weightedGibbsMass_second S f
  third := weightedGibbsMass_third S f
  fourth := weightedGibbsMass_fourth S f

theorem weightedGibbsEndpoint_nonneg {S : Finset G} {f : S → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a : S) : 0 ≤ weightedGibbsEndpoint S f a :=
  Finset.sum_nonneg (fun b _ ↦ Finset.sum_nonneg (fun c _ ↦
    Finset.sum_nonneg (fun d _ ↦ weightedGibbsMass_nonneg hf a b c d)))

theorem weightedGibbsEndpoint_sum {S : Finset G} {f : S → ℝ}
    (hZ : weightedGibbsPartition S f ≠ 0) : ∑ a, weightedGibbsEndpoint S f a = 1 := by
  simp only [weightedGibbsEndpoint, weightedGibbsMass, div_eq_mul_inv, ← Finset.sum_mul]
  rw [← weightedGibbsPartition_eq_sum, mul_inv_cancel₀ hZ]

theorem weightedGibbsEndpoint_pos {S : Finset G} {f : S → ℝ}
    (hf : ∀ x, 0 < f x) (hZ : 0 < weightedGibbsPartition S f) (a : S) :
    0 < weightedGibbsEndpoint S f a := by
  have hd : 0 < weightedGibbsMass S f a a a a := by
    simp only [weightedGibbsMass, additiveQuadrupleWeight]
    exact div_pos (mul_pos (mul_pos (hf a) (hf a)) (mul_pos (hf a) (hf a))) hZ
  exact hd.trans_le (single_le_three_sum _
    (fun b c d ↦ weightedGibbsMass_nonneg (fun x ↦ (hf x).le) a b c d) a a a)

end
end Erdos539Geometry
