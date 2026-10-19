/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.OrderedLayerFans
import Erdos539.LayerEstimates

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical

/-- Count interior layers by their two side totals and charge the two endpoints separately. -/
theorem layer_sum_bound {τ : Type*} [LinearOrder τ] (L : Finset τ)
    (a b : τ → ℝ) {lo hi : τ} (hlo : lo ∈ L) (hhi : hi ∈ L)
    (hmin : ∀ i ∈ L, lo ≤ i) (hmax : ∀ i ∈ L, i ≤ hi)
    {P E q : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (ha : ∀ i ∈ L, 0 ≤ a i) (hb : ∀ i ∈ L, 0 ≤ b i)
    (hend : ∀ i ∈ L, a i * b i ≤ E)
    (hint : ∀ i ∈ L, a i * b i ≤ P * (a i + b i))
    (hleft : ∑ i ∈ L.filter (fun i ↦ lo < i), a i ≤ q)
    (hright : ∑ i ∈ L.filter (fun i ↦ i < hi), b i ≤ q) :
    ∑ i ∈ L, a i * b i ≤ 2 * q * P + 2 * E := by
  classical
  have hpoint (i : τ) (hiL : i ∈ L) :
      a i * b i ≤ (if i = lo then E else 0) + (if i = hi then E else 0) +
        P * ((if lo < i then a i else 0) + (if i < hi then b i else 0)) := by
    by_cases hil : i = lo
    · rw [if_pos hil]
      have h₁ : 0 ≤ (if i = hi then E else 0) := by split_ifs <;> positivity
      have h₂ : 0 ≤ P * ((if lo < i then a i else 0) + (if i < hi then b i else 0)) := by
        apply mul_nonneg hP
        apply add_nonneg
        · split_ifs <;> first | exact ha i hiL | positivity
        · split_ifs <;> first | exact hb i hiL | positivity
      linarith [hend i hiL]
    by_cases hih : i = hi
    · rw [if_neg hil, if_pos hih, zero_add]
      have h₂ : 0 ≤ P * ((if lo < i then a i else 0) + (if i < hi then b i else 0)) := by
        apply mul_nonneg hP
        apply add_nonneg
        · split_ifs <;> first | exact ha i hiL | positivity
        · split_ifs <;> first | exact hb i hiL | positivity
      linarith [hend i hiL]
    have hli : lo < i := lt_of_le_of_ne (hmin i hiL) (Ne.symm hil)
    have hih' : i < hi := lt_of_le_of_ne (hmax i hiL) hih
    simpa only [if_neg hil, if_neg hih, if_pos hli, if_pos hih', zero_add] using hint i hiL
  calc
    _ ≤ ∑ i ∈ L, ((if i = lo then E else 0) + (if i = hi then E else 0) +
        P * ((if lo < i then a i else 0) + (if i < hi then b i else 0))) := Finset.sum_le_sum hpoint
    _ = 2 * E + P * ((∑ i ∈ L.filter (fun i ↦ lo < i), a i) +
        ∑ i ∈ L.filter (fun i ↦ i < hi), b i) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', hlo, hhi, if_true, Finset.sum_filter]
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (add_le_add hleft hright) hP
      nlinarith

end
end Erdos539Geometry
