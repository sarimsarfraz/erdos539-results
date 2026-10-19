/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteProbabilityPush

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι : Type*} [Fintype ι]
local instance finiteBernoulliSampleDecidableEq : DecidableEq (ι → Bool) := Classical.decEq _

def bernoulliAtom (α : ℝ) (b : Bool) : ℝ := if b then α else 1 - α

/-- A finite product law on actual Boolean selections of the underlying sites. -/
def finiteBernoulliWeight (α : ℝ) (ω : ι → Bool) : ℝ := ∏ i, bernoulliAtom α (ω i)

theorem finiteBernoulliWeight_nonneg {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (ω : ι → Bool) :
    0 ≤ finiteBernoulliWeight α ω := by
  apply Finset.prod_nonneg
  intro i _
  simp only [bernoulliAtom]
  split <;> linarith

theorem finiteBernoulli_prod_expectation (α : ℝ) (f : ι → Bool → ℝ) :
    (∑ ω, finiteBernoulliWeight α ω * ∏ i, f i (ω i)) =
      ∏ i, ((1 - α) * f i false + α * f i true) := by
  simp only [finiteBernoulliWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b ↦ bernoulliAtom α b * f i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp [bernoulliAtom, add_comm]

theorem finiteBernoulliWeight_sum (α : ℝ) : (∑ ω : ι → Bool, finiteBernoulliWeight α ω) = 1 := by
  have h := finiteBernoulli_prod_expectation α (fun (_ : ι) (_ : Bool) ↦ (1 : ℝ))
  simpa using h

/-- Indicator that every site of A was selected. -/
def bernoulliAll (A : Finset ι) (ω : ι → Bool) : ℝ := ∏ i ∈ A, if ω i then 1 else 0

theorem bernoulliAll_eq_indicator (A : Finset ι) (ω : ι → Bool) :
    bernoulliAll A ω = if ∀ i ∈ A, ω i = true then 1 else 0 := by
  by_cases h : ∀ i ∈ A, ω i = true
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h i hi]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi, hω⟩ := h
    apply Finset.prod_eq_zero hi
    simp [hω]

theorem bernoulliAll_zero_or_one (A : Finset ι) (ω : ι → Bool) :
    bernoulliAll A ω = 0 ∨ bernoulliAll A ω = 1 := by
  rw [bernoulliAll_eq_indicator]
  split <;> simp

theorem finiteBernoulli_all_expectation (α : ℝ) (A : Finset ι) :
    (∑ ω, finiteBernoulliWeight α ω * bernoulliAll A ω) = α ^ A.card := by
  have h := finiteBernoulli_prod_expectation α
    (fun i b ↦ if i ∈ A then (if b then (1 : ℝ) else 0) else 1)
  have hl (ω : ι → Bool) :
      (∏ i, if i ∈ A then (if ω i then (1 : ℝ) else 0) else 1) = bernoulliAll A ω :=
    Finset.prod_ite_mem_eq A _
  simp_rw [hl] at h
  rw [h]
  have hr (i : ι) :
      (1 - α) * (if i ∈ A then (if false then (1 : ℝ) else 0) else 1) +
        α * (if i ∈ A then (if true then (1 : ℝ) else 0) else 1) = if i ∈ A then α else 1 := by
    by_cases hi : i ∈ A <;> simp only [hi, if_true, if_false, Bool.false_eq_true,
      mul_zero, mul_one, zero_add]
    ring
  calc
    _ = ∏ i : ι, if i ∈ A then α else 1 := Finset.prod_congr rfl (fun i _ ↦ hr i)
    _ = α ^ A.card := by simp

end
end Erdos539Geometry
