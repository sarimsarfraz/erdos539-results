/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyHereditary

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G ι : Type*} [AddCommGroup G] [DecidableEq G] [Fintype ι]

/-- Overlaps in a finite cover are allowed; arbitrary preliminary deletion
is encoded by the inclusion rather than an equality with the union. -/
theorem sqrt_energyNorm_le_cover {E : Finset G} (C : ι → Finset G)
    (hcover : ∀ x ∈ E, ∃ i, x ∈ C i) :
    Real.sqrt (energyNorm E) ≤ ∑ i, Real.sqrt (energyNorm (C i)) := by
  by_cases hE : E.Nonempty
  · obtain ⟨f, hf, hfn, hopt⟩ := energyNorm_attained hE
    let μ : ι → ℝ := fun i ↦ weightSquareSum (E ∩ C i) (extendWeight E f)
    have hμ : ∀ i, 0 ≤ μ i := fun i ↦ weightSquareSum_nonneg _ _
    have hmass : 1 ≤ ∑ i, μ i := by
      rw [← hfn, ← weightSquareSum_extend]
      change (∑ x ∈ E, extendWeight E f x ^ 2) ≤
        ∑ i, ∑ x ∈ E ∩ C i, extendWeight E f x ^ 2
      simp only [← Finset.filter_mem_eq_inter, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨i, hi⟩ := hcover x hx
      calc
        _ = if x ∈ C i then extendWeight E f x ^ 2 else 0 := by rw [if_pos hi]
        _ ≤ ∑ j, if x ∈ C j then extendWeight E f x ^ 2 else 0 :=
          Finset.single_le_sum (f := fun j ↦ if x ∈ C j then extendWeight E f x ^ 2 else (0 : ℝ))
            (fun j _ ↦ by dsimp only; split <;> positivity) (Finset.mem_univ i)
    have hi : ∀ i, Real.sqrt (energyNorm E) * μ i ≤ Real.sqrt (energyNorm (C i)) := by
      intro i
      have hh := (energyNorm_hereditary (Finset.inter_subset_left (s₂ := C i)) hE
        ⟨hf, hfn⟩ hopt).trans (energyNorm_mono (Finset.inter_subset_right (s₁ := E)))
      have hsq := Real.sq_sqrt (energyNorm_nonneg E)
      have hsq' := Real.sq_sqrt (energyNorm_nonneg (C i))
      have hp := Real.sqrt_nonneg (energyNorm (C i))
      have hm := mul_nonneg (Real.sqrt_nonneg (energyNorm E)) (hμ i)
      change energyNorm E * μ i ^ 2 ≤ energyNorm (C i) at hh
      nlinarith
    calc
      _ ≤ Real.sqrt (energyNorm E) * ∑ i, μ i := by
        simpa using mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg (energyNorm E))
      _ = ∑ i, Real.sqrt (energyNorm E) * μ i := Finset.mul_sum ..
      _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ hi i)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hE, energyNorm_empty, Real.sqrt_zero]
    exact Finset.sum_nonneg (fun i _ ↦ Real.sqrt_nonneg _)

/-- A cover by k supports of norm at most R has norm at most k^2 R. -/
theorem energyNorm_le_card_sq_mul_of_cover {E : Finset G} (C : ι → Finset G)
    (hcover : ∀ x ∈ E, ∃ i, x ∈ C i) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ i, energyNorm (C i) ≤ R) :
    energyNorm E ≤ (Fintype.card ι : ℝ) ^ 2 * R := by
  have hh := (sqrt_energyNorm_le_cover C hcover).trans
    (Finset.sum_le_sum (fun i _ ↦ Real.sqrt_le_sqrt (hbound i)))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  have hp := mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card ι)) (Real.sqrt_nonneg R)
  have he := Real.sq_sqrt (energyNorm_nonneg E)
  have hr := Real.sq_sqrt hR
  nlinarith [Real.sqrt_nonneg (energyNorm E), sq_nonneg ((Fintype.card ι : ℝ) * Real.sqrt R - Real.sqrt (energyNorm E))]

end
end Erdos539Geometry
