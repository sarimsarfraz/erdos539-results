/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyFiniteSums
import Erdos539.SidonLabelAlgebra
import Erdos539.FiberEnergy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G ι : Type*} [AddCommGroup G] [DecidableEq G] [Fintype ι]

/-- Component-pair sums are disjoint for distinct unordered label pairs,
including diagonal pairs. Labels need not be additive coordinates. -/
def SeparatedSumLabels (S : Finset G) (label : G → ι) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → SameUnorderedPair (label a) (label b) (label c) (label d)

omit [AddCommGroup G] [DecidableEq G] [Fintype ι] in
def componentWeight (label : G → ι) (w : G → ℝ) (i : ι) (x : G) : ℝ :=
  if label x = i then w x else 0

omit [AddCommGroup G] [DecidableEq G] in
theorem sum_componentWeight (label : G → ι) (w : G → ℝ) :
    (fun x ↦ ∑ i, componentWeight label w i x) = w := by
  funext x
  simp [componentWeight]

/-- Literal component expansion of additive energy. -/
theorem weightedEnergy_component_expansion (S : Finset G) (label : G → ι) (w : G → ℝ) :
    weightedEnergy S w = ∑ i, ∑ j, ∑ k, ∑ l,
      mixedWeightedEnergy S (componentWeight label w i) (componentWeight label w j)
        (componentWeight label w k) (componentWeight label w l) := by
  have he : weightedEnergy S w = mixedWeightedEnergy S
      (fun x ↦ ∑ i, componentWeight label w i x) (fun x ↦ ∑ i, componentWeight label w i x)
      (fun x ↦ ∑ i, componentWeight label w i x) (fun x ↦ ∑ i, componentWeight label w i x) := by
    rw [sum_componentWeight, mixedWeightedEnergy_self]
  rw [he]
  simp_rw [mixedWeightedEnergy_sum_first, mixedWeightedEnergy_sum_second,
    mixedWeightedEnergy_sum_third, mixedWeightedEnergy_sum_fourth]

omit [Fintype ι] in
/-- Separation makes all unmatched component quadruples vanish exactly. -/
theorem separated_mixedEnergy_zero {S : Finset G} {label : G → ι}
    (hsep : SeparatedSumLabels S label) (w : G → ℝ) {i j k l : ι}
    (hbad : ¬ SameUnorderedPair i j k l) :
    mixedWeightedEnergy S (componentWeight label w i) (componentWeight label w j)
      (componentWeight label w k) (componentWeight label w l) = 0 := by
  rw [mixedWeightedEnergy_eq_quadruples]
  simp only [Finset.sum_product]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro c hc
  apply Finset.sum_eq_zero
  intro d hd
  by_cases he : a + b = c + d
  · rw [if_pos he]
    by_cases hai : label a = i
    · by_cases hbj : label b = j
      · by_cases hck : label c = k
        · by_cases hdl : label d = l
          · have hs := hsep a ha b hb c hc d hd he
            rw [hai, hbj, hck, hdl] at hs
            exact False.elim (hbad hs)
          · simp [componentWeight, hdl]
        · simp [componentWeight, hck]
      · simp [componentWeight, hbj]
    · simp [componentWeight, hai]
  · simp only [if_neg he]

/-- Actual component energy bounds aggregate through the checked Sidon
label expression; no restricted weight is assumed to optimize its component. -/
theorem separated_energy_le_label_expression {S : Finset G} {label : G → ι}
    (hsep : SeparatedSumLabels S label) (w : G → ℝ) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (henergy : ∀ i, weightedEnergy S (componentWeight label w i) ≤ v i ^ 4) :
    weightedEnergy S w ≤ 2 * (∑ i, v i ^ 2) ^ 2 - ∑ i, v i ^ 4 := by
  rw [weightedEnergy_component_expansion S label, ← unordered_pair_energy]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro l _
  by_cases h : SameUnorderedPair i j k l
  · rw [if_pos h]
    have hm := mixedWeightedEnergy_le_common_bound S
      (componentWeight label w i) (componentWeight label w j)
      (componentWeight label w k) (componentWeight label w l)
      (M := 1) (by norm_num) (hv i) (hv j) (hv k) (hv l)
      (by simpa only [one_mul] using henergy i) (by simpa only [one_mul] using henergy j)
      (by simpa only [one_mul] using henergy k) (by simpa only [one_mul] using henergy l)
    simpa only [one_mul, mul_assoc] using hm
  · rw [if_neg h, separated_mixedEnergy_zero hsep w h]

/-- The integer-certified rational Sidon inequality applied to separated
components of an arbitrary finite additive support. -/
theorem separated_energy_rational_bound {S : Finset G} {label : G → ι}
    (hsep : SeparatedSumLabels S label) (w : G → ℝ) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (henergy : ∀ i, weightedEnergy S (componentWeight label w i) ≤ v i ^ 4) :
    weightedEnergy S w ≤ (∑ i, v i ^ (20 / 13 : ℝ)) ^ (13 / 5 : ℝ) := by
  exact (separated_energy_le_label_expression hsep w v hv henergy).trans
    (rational_sidon_energy_bound Finset.univ v (fun i _ ↦ hv i))

end
end Erdos539Geometry
