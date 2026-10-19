/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyTransport

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical Pointwise
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

/-- A collision-free additive encoding preserves arbitrary weighted energy. -/
theorem weightedEnergy_image_of_sum_injective (S : Finset G) (φ : G →+ H)
    (hi : Set.InjOn φ S) (hs : Set.InjOn φ (↑(S + S) : Set G))
    (g : S.image φ → ℝ) :
    weightedEnergy (S.image φ) (extendWeight (S.image φ) g) =
      weightedEnergy S (extendWeight S (fun x ↦ g (supportImageEquiv S φ hi x))) := by
  let e := supportImageEquiv S φ hi
  rw [weightedEnergy_subtype, weightedEnergy_subtype]
  symm
  apply Fintype.sum_equiv e
  intro a
  apply Fintype.sum_equiv e
  intro b
  apply Fintype.sum_equiv e
  intro c
  apply Fintype.sum_equiv e
  intro d
  have he : a.val + b.val = c.val + d.val ↔
      (e a).val + (e b).val = (e c).val + (e d).val := by
    change _ ↔ φ a.val + φ b.val = φ c.val + φ d.val
    rw [← map_add, ← map_add]
    exact ⟨congrArg φ, hs (Finset.mem_add.mpr ⟨a, a.property, b, b.property, rfl⟩)
      (Finset.mem_add.mpr ⟨c, c.property, d, d.property, rfl⟩)⟩
  simp only [he]
  rfl

theorem energyNorm_image_of_sum_injective (S : Finset G) (φ : G →+ H)
    (hi : Set.InjOn φ S) (hs : Set.InjOn φ (↑(S + S) : Set G)) :
    energyNorm (S.image φ) = energyNorm S := by
  apply le_antisymm _ (energyNorm_le_injective_image φ hi)
  by_cases hS : S.Nonempty
  · obtain ⟨g, hg, hgn, hE⟩ := energyNorm_attained (hS.image φ)
    let e := supportImageEquiv S φ hi
    have hf : (fun x ↦ g (e x)) ∈ admissibleWeights S := by
      refine ⟨fun x ↦ hg (e x), ?_⟩
      rw [e.sum_comp (fun y ↦ g y ^ 2), hgn]
    rw [← hE, weightedEnergy_image_of_sum_injective S φ hi hs]
    exact energyNorm_ge_admissible hf
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS, energyNorm_empty]

theorem energyNorm_image_of_injective (S : Finset G) (φ : G →+ H)
    (hi : Function.Injective φ) : energyNorm (S.image φ) = energyNorm S :=
  energyNorm_image_of_sum_injective S φ hi.injOn hi.injOn

end
end Erdos539Geometry
