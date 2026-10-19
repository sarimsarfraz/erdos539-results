/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FanColorCollision

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local instance fanColorStrictnessDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

omit [Fintype ι] [Nonempty ι] in
theorem fanColorWeight_pos_at_output {S : Finset (ι → ℝ)}
    (f g : S → ℝ) (hf : ∀ a, 0 < f a) (hg : ∀ a, 0 < g a) (c a : S) :
    0 < fanColorWeight S f g (positiveDifferenceChannel S c a) := by
  have hm := (channelMaxWeight_spec (positiveDifferenceChannel S) g hg c
    (mem_channelOutputs (positiveDifferenceChannel S) c a)).2 a rfl
  have hr : 0 < fanRowWeight S f g c (positiveDifferenceChannel S c a) :=
    mul_pos (div_pos (sq_pos_of_pos (hf c)) (hg c)) ((hg a).trans_le hm)
  exact hr.trans_le (Finset.single_le_sum
    (fun b _ ↦ fanRowWeight_nonneg S f g hg b _) (Finset.mem_univ c))

omit [Fintype ι] [Nonempty ι] in
theorem exists_nonzero_fan_output {S : Finset (ι → ℝ)} (hS : S.Nontrivial) :
    ∃ c a : S, (positiveDifferenceChannel S c a).val ≠ 0 := by
  obtain ⟨a, ha, b, hb, hab⟩ := hS
  have hex : ∃ i, a i ≠ b i := by
    by_contra h
    apply hab
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  rcases lt_or_gt_of_ne hi with h | h
  · refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    intro he
    have he' := congrFun he i
    change max (b i - a i) 0 = 0 at he'
    rw [max_eq_left (by linarith)] at he'
    linarith
  · refine ⟨⟨b, hb⟩, ⟨a, ha⟩, ?_⟩
    intro he
    have he' := congrFun he i
    change max (a i - b i) 0 = 0 at he'
    rw [max_eq_left (by linarith)] at he'
    linarith

omit [Fintype ι] [Nonempty ι] in
theorem nonzeroFanColorWeight_sum_pos {S : Finset (ι → ℝ)} (hS : S.Nontrivial)
    (f g : S → ℝ) (hf : ∀ a, 0 < f a) (hg : ∀ a, 0 < g a) :
    0 < ∑ z, nonzeroFanColorWeight S f g z := by
  obtain ⟨c, a, hca⟩ := exists_nonzero_fan_output hS
  have hn : ∀ z, 0 ≤ nonzeroFanColorWeight S f g z := by
    intro z
    unfold nonzeroFanColorWeight
    split_ifs
    · rfl
    · exact fanColorWeight_nonneg S f g hg z
  have hp : 0 < nonzeroFanColorWeight S f g (positiveDifferenceChannel S c a) := by
    rw [nonzeroFanColorWeight, if_neg hca]
    exact fanColorWeight_pos_at_output f g hf hg c a
  exact hp.trans_le (Finset.single_le_sum (fun z _ ↦ hn z) (Finset.mem_univ _))

/-- Positive weights on a nonsingleton support make the final disjoint-color
inequality strict. This is only qualitative strictness, not a power gain. -/
theorem disjointFanColorSum_lt_square {S : Finset (ι → ℝ)} (hS : S.Nontrivial)
    (f g : S → ℝ) (hf : ∀ a, 0 < f a) (hg : ∀ a, 0 < g a) :
    disjointFanColorSum S f g < (∑ z, fanColorWeight S f g z) ^ 2 := by
  have h := disjointFanColorSum_le_square_sub_nonzero f g hg
  have hp := nonzeroFanColorWeight_sum_pos hS f g hf hg
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hgap := div_pos (sq_pos_of_pos hp) hd
  linarith

theorem weightedEnergy_lt_fan_ratio_square {S : Finset (ι → ℝ)} (hS : S.Nontrivial)
    (f g : S → ℝ) (hf : ∀ a, 0 < f a) (hg : ∀ a, 0 < g a) :
    weightedGibbsPartition S f <
      (∑ c, f c ^ 2 * channelWeightRatio (positiveDifferenceChannel S) g c) ^ 2 := by
  have h := disjointFanColorSum_lt_square hS f g hf hg
  rw [fanColorWeight_sum] at h
  exact ((weighted_fan_color_chain hS.nonempty f g hg).1.trans
    (weighted_fan_color_chain hS.nonempty f g hg).2.1).trans_lt h

end
end Erdos539Geometry
