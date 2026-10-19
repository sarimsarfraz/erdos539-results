/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.QuadrupleLaw

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

omit [AddCommGroup G] [AddCommGroup H] [DecidableEq G] in
def supportImageEquiv (S : Finset G) (φ : G → H) (hinj : Set.InjOn φ S) : S ≃ S.image φ :=
  Equiv.ofBijective (fun x ↦ ⟨φ x, Finset.mem_image.mpr ⟨x, x.property, rfl⟩⟩) (by
    constructor
    · intro x y h
      exact Subtype.ext (hinj x.property y.property (congrArg Subtype.val h))
    · intro y
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)

omit [AddCommGroup G] [AddCommGroup H] [DecidableEq G] in
@[simp] theorem supportImageEquiv_val (S : Finset G) (φ : G → H) (hinj : Set.InjOn φ S) (x : S) :
    (supportImageEquiv S φ hinj x).val = φ x := rfl

theorem weightedEnergy_subtype (S : Finset G) (f : S → ℝ) :
    weightedEnergy S (extendWeight S f) =
      ∑ a : S, ∑ b : S, ∑ c : S, ∑ d : S,
        if a.val + b.val = c.val + d.val then (f a * f b) * (f c * f d) else 0 := by
  rw [← mixedWeightedEnergy_self, mixedWeightedEnergy_subtype]

/-- Pushing weights through an injective-on-support additive map retains
all old additive quadruples. It may introduce new ones. -/
theorem weightedEnergy_le_injective_image (S : Finset G) (φ : G →+ H)
    (hinj : Set.InjOn φ S) (f : S → ℝ) (hf : ∀ x, 0 ≤ f x) :
    weightedEnergy S (extendWeight S f) ≤
      weightedEnergy (S.image φ) (extendWeight (S.image φ)
        (fun y ↦ f ((supportImageEquiv S φ hinj).symm y))) := by
  let e := supportImageEquiv S φ hinj
  let g : S.image φ → ℝ := fun y ↦ f (e.symm y)
  have hge : ∀ x : S, g (e x) = f x := by intro x; simp [g]
  have he : ∀ x : S, (e x).val = φ x := fun _ ↦ rfl
  rw [weightedEnergy_subtype, weightedEnergy_subtype]
  change _ ≤ ∑ a, ∑ b, ∑ c, ∑ d,
    if a.val + b.val = c.val + d.val then (g a * g b) * (g c * g d) else 0
  have hreindex : (∑ a : S, ∑ b : S, ∑ c : S, ∑ d : S,
      if (e a).val + (e b).val = (e c).val + (e d).val then
        (g (e a) * g (e b)) * (g (e c) * g (e d)) else 0) =
      ∑ a, ∑ b, ∑ c, ∑ d,
        if a.val + b.val = c.val + d.val then (g a * g b) * (g c * g d) else 0 := by
    apply Fintype.sum_equiv e
    intro a
    apply Fintype.sum_equiv e
    intro b
    apply Fintype.sum_equiv e
    intro c
    apply Fintype.sum_equiv e
    intro d
    rfl
  rw [← hreindex]
  simp only [hge, he]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro c _
  apply Finset.sum_le_sum
  intro d _
  by_cases habcd : a.val + b.val = c.val + d.val
  · have hm : φ a.val + φ b.val = φ c.val + φ d.val := by
      simpa only [map_add] using congrArg φ habcd
    simp only [if_pos habcd, if_pos hm, le_refl]
  · rw [if_neg habcd]
    split_ifs
    · exact mul_nonneg (mul_nonneg (hf a) (hf b)) (mul_nonneg (hf c) (hf d))
    · rfl

/-- The literal finite norm cannot decrease under an additive map that is
injective on the support. Global injectivity is not required. -/
theorem energyNorm_le_injective_image {S : Finset G} (φ : G →+ H)
    (hinj : Set.InjOn φ S) : energyNorm S ≤ energyNorm (S.image φ) := by
  by_cases hS : S.Nonempty
  · obtain ⟨f, hf, hnorm, hE⟩ := energyNorm_attained hS
    let e := supportImageEquiv S φ hinj
    let g : S.image φ → ℝ := fun y ↦ f (e.symm y)
    have hg : g ∈ admissibleWeights (S.image φ) := by
      refine ⟨fun y ↦ hf (e.symm y), ?_⟩
      have heq := e.symm.sum_comp (fun x ↦ f x ^ 2)
      change (∑ y, f (e.symm y) ^ 2) = 1
      rw [heq, hnorm]
    have h := weightedEnergy_le_injective_image S φ hinj f hf
    rw [hE] at h
    exact h.trans (energyNorm_ge_admissible hg)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, energyNorm_empty]
    exact energyNorm_nonneg _

end
end Erdos539Geometry
