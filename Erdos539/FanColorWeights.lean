/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ChannelMaxWeights
import Erdos539.QuadrupleFanEncoding
import Erdos539.WeightedTransferGap

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι : Type*}
local instance fanColorWeightsDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- Positive-coordinate supports are disjoint. -/
def FanColorsDisjoint {S : Finset (ι → ℝ)} (z w : posDiff S) : Prop :=
  ∀ i, z.val i = 0 ∨ w.val i = 0

def fanRowWeight (S : Finset (ι → ℝ)) (f g : S → ℝ) (c : S) (z : posDiff S) : ℝ :=
  (f c ^ 2 / g c) * channelMaxWeight (positiveDifferenceChannel S) g c z

/-- The source's h(z), defined from actual class maxima. -/
def fanColorWeight (S : Finset (ι → ℝ)) (f g : S → ℝ) (z : posDiff S) : ℝ :=
  ∑ c, fanRowWeight S f g c z

def disjointFanColorSum (S : Finset (ι → ℝ)) (f g : S → ℝ) : ℝ :=
  ∑ z : posDiff S, ∑ w : posDiff S,
    if FanColorsDisjoint z w then fanColorWeight S f g z * fanColorWeight S f g w else 0

def encodedFanWeight (S : Finset (ι → ℝ)) (f g : S → ℝ)
    (y : (S × posDiff S) × (S × posDiff S)) : ℝ :=
  if FanColorsDisjoint y.1.2 y.2.2 then
    fanRowWeight S f g y.1.1 y.1.2 * fanRowWeight S f g y.2.1 y.2.2 else 0

theorem fanRowWeight_nonneg (S : Finset (ι → ℝ)) (f g : S → ℝ) (hg : ∀ a, 0 < g a)
    (c : S) (z : posDiff S) : 0 ≤ fanRowWeight S f g c z :=
  mul_nonneg (div_nonneg (sq_nonneg _) (hg c).le) (channelReference_nonneg _ _ _ _)

theorem fanColorWeight_nonneg (S : Finset (ι → ℝ)) (f g : S → ℝ) (hg : ∀ a, 0 < g a)
    (z : posDiff S) : 0 ≤ fanColorWeight S f g z :=
  Finset.sum_nonneg (fun c _ ↦ fanRowWeight_nonneg S f g hg c z)

theorem encodedFanWeight_nonneg (S : Finset (ι → ℝ)) (f g : S → ℝ) (hg : ∀ a, 0 < g a)
    (y : (S × posDiff S) × (S × posDiff S)) : 0 ≤ encodedFanWeight S f g y := by
  unfold encodedFanWeight
  split_ifs
  · exact mul_nonneg (fanRowWeight_nonneg S f g hg _ _) (fanRowWeight_nonneg S f g hg _ _)
  · rfl

theorem fanColorWeight_sum (S : Finset (ι → ℝ)) (f g : S → ℝ) :
    (∑ z, fanColorWeight S f g z) =
      ∑ c, f c ^ 2 * channelWeightRatio (positiveDifferenceChannel S) g c := by
  unfold fanColorWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp only [fanRowWeight, ← Finset.mul_sum, channelWeightRatio, channelWeightSum]
  ring

theorem quadrupleFanEncoding_disjoint {S : Finset (ι → ℝ)}
    (t : (S × S) × (S × S)) (ht : t.1.1.val + t.1.2.val = t.2.1.val + t.2.2.val) :
    FanColorsDisjoint (quadrupleFanEncoding S t).1.2 (quadrupleFanEncoding S t).2.2 := by
  intro i
  have hi := congrFun ht i
  change t.1.1.val i + t.1.2.val i = t.2.1.val i + t.2.2.val i at hi
  change max (t.1.1.val i - t.2.1.val i) 0 = 0 ∨ max (t.1.2.val i - t.2.2.val i) 0 = 0
  by_cases h : t.1.1.val i ≤ t.2.1.val i
  · exact Or.inl (max_eq_right (by linarith))
  · exact Or.inr (max_eq_right (by linarith))

theorem quadrupleFanEncoding_injective_additive {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (u v : (S × S) × (S × S))
    (hu : u.1.1.val + u.1.2.val = u.2.1.val + u.2.2.val)
    (hv : v.1.1.val + v.1.2.val = v.2.1.val + v.2.2.val)
    (he : quadrupleFanEncoding S u = quadrupleFanEncoding S v) : u = v := by
  let f : S → ℝ := fun _ ↦ 1
  have hf : ∀ a, 0 < f a := fun _ ↦ by norm_num [f]
  have hZ := weightedGibbsPartition_pos hS hf
  let Q := weightedGibbsLaw S f (fun a ↦ (hf a).le)
  apply Q.fan_encoding_injective_on_support u v _ _ he
  · simp [Q, StationaryAdditiveLaw.flat, weightedGibbsLaw, weightedGibbsMass,
      additiveQuadrupleWeight, hu, f, hZ.ne']
  · simp [Q, StationaryAdditiveLaw.flat, weightedGibbsLaw, weightedGibbsMass,
      additiveQuadrupleWeight, hv, f, hZ.ne']

/-- Summing the encoded anchor weights gives exactly the disjoint-color
sum, including unavailable classes (whose weights are zero). -/
theorem encodedFanWeight_sum (S : Finset (ι → ℝ)) (f g : S → ℝ) :
    (∑ y, encodedFanWeight S f g y) = disjointFanColorSum S f g := by
  simp only [Fintype.sum_prod_type, encodedFanWeight, disjointFanColorSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  calc
    (∑ c, ∑ d, ∑ w, if FanColorsDisjoint z w then fanRowWeight S f g c z * fanRowWeight S f g d w else 0) =
        ∑ c, ∑ w, ∑ d, if FanColorsDisjoint z w then fanRowWeight S f g c z * fanRowWeight S f g d w else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ w, ∑ c, ∑ d, if FanColorsDisjoint z w then fanRowWeight S f g c z * fanRowWeight S f g d w else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases h : FanColorsDisjoint z w
      · simp only [if_pos h, ← Finset.mul_sum, ← Finset.sum_mul, fanColorWeight]
      · simp [h]

end
end Erdos539Geometry
