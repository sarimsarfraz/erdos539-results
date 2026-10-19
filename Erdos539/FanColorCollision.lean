/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedFanColorBound
import Erdos539.FiniteLabelCollision

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local instance fanColorCollisionDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

omit [Fintype ι] [Nonempty ι] in
theorem fanColor_nonneg {S : Finset (ι → ℝ)} (z : posDiff S) (i : ι) : 0 ≤ z.val i := by
  obtain ⟨a, _, b, _, he⟩ := mem_posDiff.mp z.property
  rw [← he]
  exact le_max_right _ _

omit [Fintype ι] [Nonempty ι] in
theorem fanColor_exists_positive {S : Finset (ι → ℝ)} (z : posDiff S) (hz : z.val ≠ 0) :
    ∃ i, 0 < z.val i := by
  by_contra hn
  apply hz
  funext i
  exact le_antisymm (le_of_not_gt (fun hi ↦ hn ⟨i, hi⟩)) (fanColor_nonneg z i)

/-- Assign every nonzero color to one of its positive coordinates. -/
def fanColorLabel {S : Finset (ι → ℝ)} (z : posDiff S) : ι :=
  if hz : z.val = 0 then Classical.choice inferInstance else (fanColor_exists_positive z hz).choose

omit [Fintype ι] in
theorem fanColorLabel_pos {S : Finset (ι → ℝ)} (z : posDiff S) (hz : z.val ≠ 0) :
    0 < z.val (fanColorLabel z) := by
  simp only [fanColorLabel, dif_neg hz]
  exact (fanColor_exists_positive z hz).choose_spec

def nonzeroFanColorWeight (S : Finset (ι → ℝ)) (f g : S → ℝ) (z : posDiff S) : ℝ :=
  if z.val = 0 then 0 else fanColorWeight S f g z

omit [Fintype ι] in
/-- Equal assigned positive coordinates force an excluded color pair. -/
theorem fanColor_collision_le_gap {S : Finset (ι → ℝ)} (f g : S → ℝ) (hg : ∀ a, 0 < g a)
    (z w : posDiff S) :
    (if fanColorLabel w = fanColorLabel z then
      nonzeroFanColorWeight S f g z * nonzeroFanColorWeight S f g w else 0) ≤
      fanColorWeight S f g z * fanColorWeight S f g w -
        (if FanColorsDisjoint z w then fanColorWeight S f g z * fanColorWeight S f g w else 0) := by
  have hn : 0 ≤ fanColorWeight S f g z * fanColorWeight S f g w :=
    mul_nonneg (fanColorWeight_nonneg S f g hg z) (fanColorWeight_nonneg S f g hg w)
  have hgap : 0 ≤ fanColorWeight S f g z * fanColorWeight S f g w -
      (if FanColorsDisjoint z w then fanColorWeight S f g z * fanColorWeight S f g w else 0) := by
    split_ifs <;> linarith
  by_cases hz : z.val = 0
  · simpa [nonzeroFanColorWeight, hz] using hgap
  by_cases hw : w.val = 0
  · simpa [nonzeroFanColorWeight, hw] using hgap
  by_cases he : fanColorLabel w = fanColorLabel z
  · have hnot : ¬FanColorsDisjoint z w := by
      intro hd
      have hzpos := fanColorLabel_pos z hz
      have hwpos := fanColorLabel_pos w hw
      rw [he] at hwpos
      rcases hd (fanColorLabel z) with h | h <;> linarith
    simp [nonzeroFanColorWeight, hz, hw, he, hnot]
  · simpa [he] using hgap

/-- The source's quantitative excluded-color refinement. -/
theorem disjointFanColorSum_le_square_sub_nonzero {S : Finset (ι → ℝ)}
    (f g : S → ℝ) (hg : ∀ a, 0 < g a) :
    disjointFanColorSum S f g ≤ (∑ z, fanColorWeight S f g z) ^ 2 -
      (∑ z, nonzeroFanColorWeight S f g z) ^ 2 / (Fintype.card ι : ℝ) := by
  have h := finite_label_collision_bound (nonzeroFanColorWeight S f g) (fun z ↦ fanColorLabel z)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun z _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun w _ ↦ fanColor_collision_le_gap f g hg z w))
  have he : (∑ z, ∑ w, (fanColorWeight S f g z * fanColorWeight S f g w -
      (if FanColorsDisjoint z w then fanColorWeight S f g z * fanColorWeight S f g w else 0))) =
      (∑ z, fanColorWeight S f g z) ^ 2 - disjointFanColorSum S f g := by
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, pow_two,
      disjointFanColorSum]
  rw [he] at hsum
  linarith

theorem weightedEnergy_le_fan_square_sub_nonzero {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (f g : S → ℝ) (hg : ∀ a, 0 < g a) :
    weightedGibbsPartition S f ≤
      (∑ c, f c ^ 2 * channelWeightRatio (positiveDifferenceChannel S) g c) ^ 2 -
      (∑ z, nonzeroFanColorWeight S f g z) ^ 2 / (Fintype.card ι : ℝ) := by
  have h := disjointFanColorSum_le_square_sub_nonzero f g hg
  rw [fanColorWeight_sum S f g] at h
  exact ((weighted_fan_color_chain hS f g hg).1.trans (weighted_fan_color_chain hS f g hg).2.1).trans h

end
end Erdos539Geometry
