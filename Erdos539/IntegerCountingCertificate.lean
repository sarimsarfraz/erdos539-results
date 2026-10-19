/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PopularReflectedSupport

namespace Erdos539Geometry
open scoped BigOperators Pointwise

/-- Computable integer reflection, using the standard integer decision
procedures so that finite certificates reduce in Lean's kernel. -/
def integerReflection (S : Finset ℤ) (w : ℤ) : Finset ℤ :=
  S.filter (fun a ↦ w - a ∈ S)

theorem integerReflection_eq (S : Finset ℤ) (w : ℤ) :
    integerReflection S w = reflectedSupport S w := by
  classical
  ext a
  simp [integerReflection, reflectedSupport]

/-- Exact counting energy over a supplied nonnegative sum interval. -/
def integerIntervalEnergy (S : Finset ℤ) (B : ℕ) : ℕ :=
  ∑ w ∈ Finset.range B, (integerReflection S w).card ^ 2

theorem integerIntervalEnergy_eq_counting (S : Finset ℤ) (B : ℕ)
    (hS : ∀ a ∈ S, 0 ≤ a ∧ 2 * a < B) :
    (integerIntervalEnergy S B : ℝ) = countingEnergy S := by
  classical
  let W : Finset ℤ := (Finset.range B).image (fun n : ℕ ↦ (n : ℤ))
  have hsub : S + S ⊆ W := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hw
    have ha' := hS a ha
    have hb' := hS b hb
    have hn : 0 ≤ a + b := by omega
    apply Finset.mem_image.mpr
    refine ⟨(a + b).toNat, Finset.mem_range.mpr ?_, Int.toNat_of_nonneg hn⟩
    omega
  rw [countingEnergy_eq_reflected_square_sum]
  have he : (integerIntervalEnergy S B : ℝ) =
      ∑ w ∈ W, ((reflectedSupport S w).card : ℝ) ^ 2 := by
    unfold integerIntervalEnergy W
    rw [Finset.sum_image]
    · simp only [Nat.cast_sum, Nat.cast_pow, integerReflection_eq]
    · intro a _ b _ he
      exact Int.ofNat.inj he
  rw [he]
  symm
  apply Finset.sum_subset hsub
  intro w _ hw
  have hz : reflectedSupport S w = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨ha, hb⟩ := Finset.mem_filter.mp ha
    exact hw (Finset.mem_add.mpr ⟨a, ha, w - a, hb, by omega⟩)
  simp [hz]

end Erdos539Geometry
