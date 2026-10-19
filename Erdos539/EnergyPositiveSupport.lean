/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyHereditary

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def positiveWeightSupport (S : Finset G) (f : S → ℝ) : Finset G :=
  S.filter (fun x ↦ 0 < extendWeight S f x)

omit [AddCommGroup G] in
theorem positiveWeightSupport_subset (S : Finset G) (f : S → ℝ) :
    positiveWeightSupport S f ⊆ S := Finset.filter_subset _ _

omit [AddCommGroup G] in
theorem extendWeight_eq_zero_off_positiveSupport {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) {x : G} (hx : x ∈ S)
    (hxp : x ∉ positiveWeightSupport S f) : extendWeight S f x = 0 := by
  have hn : 0 ≤ extendWeight S f x := by simpa only [extendWeight, dif_pos hx] using hf.1 ⟨x, hx⟩
  have hp : ¬ 0 < extendWeight S f x := fun h ↦ hxp (Finset.mem_filter.mpr ⟨hx, h⟩)
  exact le_antisymm (le_of_not_gt hp) hn

omit [AddCommGroup G] in
theorem positiveWeightSupport_mass {S : Finset G} {f : S → ℝ} (hf : f ∈ admissibleWeights S) :
    weightSquareSum (positiveWeightSupport S f) (extendWeight S f) = 1 := by
  rw [weightSquareSum_support (positiveWeightSupport_subset S f) _
    (fun _ hx hxp ↦ extendWeight_eq_zero_off_positiveSupport hf hx hxp), weightSquareSum_extend]
  exact hf.2

omit [AddCommGroup G] in
theorem positiveWeightSupport_nonempty {S : Finset G} {f : S → ℝ} (hf : f ∈ admissibleWeights S) :
    (positiveWeightSupport S f).Nonempty := by
  by_contra h
  have hm := positiveWeightSupport_mass hf
  rw [Finset.not_nonempty_iff_eq_empty.mp h] at hm
  simp [weightSquareSum] at hm

theorem energyNorm_positiveWeightSupport {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    energyNorm (positiveWeightSupport S f) = energyNorm S := by
  have hret := energyNorm_hereditary (positiveWeightSupport_subset S f) hS hf hE
  rw [positiveWeightSupport_mass hf, one_pow, mul_one] at hret
  exact le_antisymm (energyNorm_mono (positiveWeightSupport_subset S f)) hret

end
end Erdos539Geometry
