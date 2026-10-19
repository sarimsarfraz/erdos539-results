/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReferenceUniformRoot
import Erdos539.EnergyMonotonicity
import Erdos539.EnergySupport

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A pointwise weight lower bound on a literal subset gives its full
counting energy as a lower bound, including every additive quadruple. -/
theorem weightedEnergy_ge_subset_constant {A S : Finset G} (hAS : A ⊆ S)
    (f : S → ℝ) (hf : ∀ a, 0 ≤ f a) {q : ℝ} (hq : 0 ≤ q)
    (hlower : ∀ a : S, a.val ∈ A → q ≤ f a) :
    q ^ 4 * countingEnergy A ≤ weightedGibbsPartition S f := by
  let w : G → ℝ := fun x ↦ if x ∈ A then q else 0
  have he : weightedEnergy A w = q ^ 4 * countingEnergy A := by
    calc
      _ = weightedEnergy A (fun _ ↦ q) := weightedEnergy_congr A (by intro x hx; simp [w, hx])
      _ = _ := by simpa only [mul_one, countingEnergy] using weightedEnergy_scale A (fun _ ↦ 1) q
  have heS := weightedEnergy_support hAS w (by intro x _ hx; simp [w, hx])
  rw [← he, heS]
  apply weightedEnergy_mono S
  · intro x _
    dsimp [w]
    split_ifs
    · exact hq
    · rfl
  · intro x hx
    simp only [w, extendWeight, dif_pos hx]
    split_ifs with hxa
    · exact hlower ⟨x, hx⟩ hxa
    · exact hf ⟨x, hx⟩

end
end Erdos539Geometry
