/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FinitePushTriples
import Erdos539.FiniteDataProcessing

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

structure StationaryTripleLaw (α : Type*) [Fintype α] (ν : α → ℝ) where
  mass : (α × α) × α → ℝ
  nonneg : ∀ z, 0 ≤ mass z
  first : finitePush mass (fun z ↦ z.1.1) = ν
  second : finitePush mass (fun z ↦ z.1.2) = ν
  third : finitePush mass Prod.snd = ν

namespace StationaryTripleLaw
variable {α β : Type*} [Fintype α] [Fintype β] {ν : α → ℝ}

theorem positive_endpoints (Q : StationaryTripleLaw α ν) {z : (α × α) × α}
    (hz : Q.mass z ≠ 0) : 0 < ν z.1.1 ∧ 0 < ν z.1.2 ∧ 0 < ν z.2 := by
  have hp : 0 < Q.mass z := lt_of_le_of_ne (Q.nonneg z) (Ne.symm hz)
  have h₁ := le_finitePush Q.mass (fun z ↦ z.1.1) Q.nonneg z
  have h₂ := le_finitePush Q.mass (fun z ↦ z.1.2) Q.nonneg z
  have h₃ := le_finitePush Q.mass Prod.snd Q.nonneg z
  rw [Q.first] at h₁
  rw [Q.second] at h₂
  rw [Q.third] at h₃
  exact ⟨hp.trans_le h₁, hp.trans_le h₂, hp.trans_le h₃⟩

theorem reference_pos (Q : StationaryTripleLaw α ν) {z : (α × α) × α}
    (hz : Q.mass z ≠ 0) : 0 < independentTriple ν z := by
  obtain ⟨ha, hb, hc⟩ := Q.positive_endpoints hz
  exact mul_pos (mul_pos ha hb) hc

theorem endpoint_expectation (Q : StationaryTripleLaw α ν) (g : α → ℝ) :
    (∑ z, Q.mass z * (g z.1.1 + g z.1.2 + g z.2)) = 3 * ∑ a, ν a * g a := by
  have h₁ := finitePush_expectation Q.mass (fun z ↦ z.1.1) g
  have h₂ := finitePush_expectation Q.mass (fun z ↦ z.1.2) g
  have h₃ := finitePush_expectation Q.mass Prod.snd g
  rw [Q.first] at h₁
  rw [Q.second] at h₂
  rw [Q.third] at h₃
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← h₁, ← h₂, ← h₃]
  ring

/-- Total correlation is literally relative entropy against the product
of the three actual endpoint marginals. -/
theorem relativeEntropy_eq (Q : StationaryTripleLaw α ν) :
    finiteRelEntropy Q.mass (independentTriple ν) = 3 * finiteEntropy ν - finiteEntropy Q.mass := by
  have hlog : ∀ z, Q.mass z * Real.log (independentTriple ν z) =
      Q.mass z * (Real.log (ν z.1.1) + Real.log (ν z.1.2) + Real.log (ν z.2)) := by
    intro z
    by_cases hz : Q.mass z = 0
    · simp [hz]
    obtain ⟨ha, hb, hc⟩ := Q.positive_endpoints hz
    dsimp only [independentTriple]
    rw [Real.log_mul (mul_ne_zero ha.ne' hb.ne') hc.ne', Real.log_mul ha.ne' hb.ne']
  simp only [finiteRelEntropy, mul_sub, Finset.sum_sub_distrib, hlog]
  rw [Q.endpoint_expectation (fun x ↦ Real.log (ν x))]
  simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

def map (Q : StationaryTripleLaw α ν) (e : α → β) : StationaryTripleLaw β (finitePush ν e) where
  mass := finitePush Q.mass (mapThree e)
  nonneg := finitePush_nonneg Q.mass (mapThree e) Q.nonneg
  first := by
    rw [finitePush_comp]
    change finitePush Q.mass (e ∘ (fun z ↦ z.1.1)) = _
    rw [← finitePush_comp, Q.first]
  second := by
    rw [finitePush_comp]
    change finitePush Q.mass (e ∘ (fun z ↦ z.1.2)) = _
    rw [← finitePush_comp, Q.second]
  third := by
    rw [finitePush_comp]
    change finitePush Q.mass (e ∘ Prod.snd) = _
    rw [← finitePush_comp, Q.third]

/-- The same endpoint map on each coordinate decreases total correlation. -/
theorem correlation_map_le (Q : StationaryTripleLaw α ν) (hν : ∀ a, 0 ≤ ν a) (e : α → β) :
    3 * finiteEntropy (finitePush ν e) - finiteEntropy (Q.map e).mass ≤
      3 * finiteEntropy ν - finiteEntropy Q.mass := by
  rw [← (Q.map e).relativeEntropy_eq, ← Q.relativeEntropy_eq]
  change finiteRelEntropy (finitePush Q.mass (mapThree e)) (independentTriple (finitePush ν e)) ≤ _
  rw [← finitePush_independentTriple]
  exact finiteRelEntropy_push_le Q.mass (independentTriple ν) (mapThree e) Q.nonneg
    (fun z ↦ mul_nonneg (mul_nonneg (hν z.1.1) (hν z.1.2)) (hν z.2)) (fun _ hz ↦ Q.reference_pos hz)

theorem correlation_nonneg (Q : StationaryTripleLaw α ν)
    (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) :
    0 ≤ 3 * finiteEntropy ν - finiteEntropy Q.mass := by
  have hmass : ∑ z, Q.mass z = 1 := by
    rw [← finitePush_sum Q.mass (fun z ↦ z.1.1), Q.first, hs]
  have href : ∑ z, independentTriple ν z = 1 := by
    simp only [independentTriple, Fintype.sum_prod_type, ← Finset.mul_sum, hs, mul_one]
  rw [← Q.relativeEntropy_eq]
  exact finiteRelEntropy_nonneg Q.mass (independentTriple ν) Q.nonneg
    (fun z ↦ mul_nonneg (mul_nonneg (hν z.1.1) (hν z.1.2)) (hν z.2)) hmass href
    (fun _ hz ↦ Q.reference_pos hz)

end StationaryTripleLaw
end
end Erdos539Geometry
