/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinateHan
import Erdos539.FiniteLogJensen

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance stationarySweepLogDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance stationarySweepLogProjectionDecidableEq (S : Finset (ι → ℝ)) (I : Finset ι) :
    DecidableEq (projection S I) := Classical.decEq _

theorem conditionalWeight_entropy_nonneg {α β : Type*} [Fintype α]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (f : α → β) (b : β) :
    0 ≤ finiteEntropy (conditionalWeight ν f b) := by
  by_cases hb : finitePush ν f b = 0
  · simp [finiteEntropy, conditionalWeight, hb]
  · exact finiteEntropy_nonneg _ (conditionalWeight_nonneg ν hν f b)
      (conditionalWeight_sum ν f b hb)

/-- Jensen averaging in each actual outside-coordinate fiber. -/
theorem coordinateFiberCapacity_log_lower (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) (i : ι) :
    coordinateConditionalEntropy S ν i - 2 * Real.log (coordinateConditionalEntropy S ν i + 2) - 3 ≤
      coordinateFiberCapacity S ν i := by
  let f := outsideEndpoint S i
  let p := finitePush ν f
  let H := fun b ↦ finiteEntropy (conditionalWeight ν f b)
  have hp : ∀ b, 0 ≤ p b := finitePush_nonneg ν f hν
  have hmass : ∑ b, p b = 1 := by rw [finitePush_sum, hs]
  have hH (b : projection S (Finset.univ.erase i)) : 0 ≤ H b :=
    conditionalWeight_entropy_nonneg ν hν f b
  have havg : ∑ b, p b * H b = coordinateConditionalEntropy S ν i :=
    (coordinateConditionalEntropy_eq_fiber_average S ν hν i).symm
  have hj := finite_log_jensen p (fun b ↦ H b + 2) hp hmass (fun b ↦ by linarith [hH b])
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hmass, one_mul, havg] at hj
  have hpoint (b : projection S (Finset.univ.erase i)) :
      p b * (H b - 2 * Real.log (H b + 2) - 3) ≤
      p b * stationaryCapacity (conditionalWeight ν f b)
        (fun a x ↦ scalarCoordinateChannel S i a.val x.val) := by
    by_cases hb : p b = 0
    · simp only [hb, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (outsideFiber_scalar_bounds S ν hν i b hb).1 (hp b)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ ↦ hpoint b)
  have halg (b : projection S (Finset.univ.erase i)) :
      p b * (H b - 2 * Real.log (H b + 2) - 3) =
        p b * H b - 2 * (p b * Real.log (H b + 2)) - p b * 3 := by ring
  simp only [halg, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    hmass, one_mul, havg] at h
  change coordinateConditionalEntropy S ν i -
    2 * (∑ b, p b * Real.log (H b + 2)) - 3 ≤ coordinateFiberCapacity S ν i at h
  linarith

/-- The exact logarithmic simultaneous-sweep bound. No independent
coordinates or replacement of the original law is assumed. -/
theorem stationary_sweep_log_bound (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) :
    (∑ i, coordinateConditionalEntropy S ν i) ≤ stationaryFanCapacity S ν +
      2 * (Fintype.card ι : ℝ) * Real.log (finiteEntropy ν / Fintype.card ι + 2) +
      3 * (Fintype.card ι : ℝ) := by
  by_cases hc : Fintype.card ι = 0
  · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp only [Finset.univ_eq_empty, Finset.sum_empty, hc, Nat.cast_zero, mul_zero,
      zero_mul, add_zero]
    exact (stationaryFanCapacity_bounds S ν hν hs).1
  · have hcpos : 0 < Fintype.card ι := Nat.pos_of_ne_zero hc
    have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hcpos
    have hnonneg (i : ι) := coordinateConditionalEntropy_nonneg S ν hν i
    have hj := finite_sum_log_le (fun i ↦ coordinateConditionalEntropy S ν i + 2)
      (fun i ↦ by linarith [hnonneg i]) hcpos
    have he : (∑ i, (coordinateConditionalEntropy S ν i + 2)) / (Fintype.card ι : ℝ) =
        (∑ i, coordinateConditionalEntropy S ν i) / Fintype.card ι + 2 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    rw [he] at hj
    have hhan := coordinate_han S ν hν hs
    have hpos : 0 < (∑ i, coordinateConditionalEntropy S ν i) / (Fintype.card ι : ℝ) + 2 := by
      have hn := Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ hnonneg i)
      positivity
    have harg : (∑ i, coordinateConditionalEntropy S ν i) / (Fintype.card ι : ℝ) + 2 ≤
        finiteEntropy ν / Fintype.card ι + 2 := by
      linarith [div_le_div_of_nonneg_right hhan hd.le]
    have hlog := Real.log_le_log hpos harg
    have hm := mul_le_mul_of_nonneg_left hlog hd.le
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ ↦ coordinateFiberCapacity_log_lower S ν hν hs i)
    have hcap := stationaryFanCapacity_fiber_sweep S ν hν hs
    change (∑ i, coordinateFiberCapacity S ν i) ≤ stationaryFanCapacity S ν at hcap
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h
    nlinarith

end
end Erdos539Geometry
