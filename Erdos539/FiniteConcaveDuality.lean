/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

namespace Erdos539Geometry
noncomputable section
open scoped Pointwise

/-- The hypograph of a continuous concave finite-dimensional objective,
after applying a linear constraint map. -/
def constrainedHypograph {α β : Type*} (C : Set (α → ℝ))
    (A : (α → ℝ) →ₗ[ℝ] (β → ℝ)) (f : (α → ℝ) → ℝ) : Set ((β → ℝ) × ℝ) :=
  {q | ∃ p ∈ C, A p = q.1 ∧ q.2 ≤ f p}

theorem constrainedHypograph_convex {α β : Type*} (C : Set (α → ℝ))
    (A : (α → ℝ) →ₗ[ℝ] (β → ℝ)) (f : (α → ℝ) → ℝ)
    (hf : ConcaveOn ℝ C f) : Convex ℝ (constrainedHypograph C A f) := by
  rintro x ⟨p, hp, hpx, hxf⟩ y ⟨q, hq, hqy, hyf⟩ a b ha hb hab
  refine ⟨a • p + b • q, hf.1 hp hq ha hb hab, ?_, ?_⟩
  · simp only [map_add, map_smul, hpx, hqy, Prod.fst_add, Prod.smul_fst]
  · exact (add_le_add (mul_le_mul_of_nonneg_left hxf ha)
      (mul_le_mul_of_nonneg_left hyf hb)).trans (hf.2 hp hq ha hb hab)

theorem constrainedHypograph_isClosed {α β : Type*} [Fintype α] [Fintype β]
    (C : Set (α → ℝ)) (hC : IsCompact C)
    (A : (α → ℝ) →ₗ[ℝ] (β → ℝ)) (f : (α → ℝ) → ℝ) (hf : Continuous f) :
    IsClosed (constrainedHypograph C A f) := by
  let G : Set ((β → ℝ) × ℝ) := (fun p ↦ (A p, f p)) '' C
  let D : Set ((β → ℝ) × ℝ) := {q | q.1 = 0 ∧ q.2 ≤ 0}
  have hG : IsCompact G := hC.image (A.continuous_of_finiteDimensional.prodMk hf)
  have hD : IsClosed D := (isClosed_eq continuous_fst continuous_const).inter
    (isClosed_le continuous_snd continuous_const)
  have he : constrainedHypograph C A f = G + D := by
    ext q
    constructor
    · rintro ⟨p, hp, hA, hq⟩
      refine Set.mem_add.mpr ⟨(A p, f p), ⟨p, hp, rfl⟩,
        (0, q.2 - f p), ⟨rfl, sub_nonpos.mpr hq⟩, ?_⟩
      apply Prod.ext
      · simpa using hA
      · simp
    · rintro ⟨x, ⟨p, hp, rfl⟩, y, ⟨hy, hy0⟩, rfl⟩
      refine ⟨p, hp, ?_, ?_⟩
      · simp [hy]
      · change f p + y.2 ≤ f p
        linarith
  rw [he]
  exact hD.add_left_of_isCompact hG

/-- Approximate Lagrange potentials for a finite continuous concave
maximization problem. This needs neither interior points nor an attained
dual minimizer, so zero coordinates in a prescribed marginal are allowed. -/
theorem finite_concave_approximate_dual {α β : Type*} [Fintype α] [Fintype β]
    (C : Set (α → ℝ)) (hC : IsCompact C)
    (A : (α → ℝ) →ₗ[ℝ] (β → ℝ)) (f : (α → ℝ) → ℝ)
    (hf : Continuous f) (hconc : ConcaveOn ℝ C f)
    (b : β → ℝ) (F : ℝ) (p₀ : α → ℝ)
    (hp₀ : p₀ ∈ C) (hA₀ : A p₀ = b) (hf₀ : f p₀ = F)
    (hmax : ∀ p ∈ C, A p = b → f p ≤ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : (β → ℝ) →ₗ[ℝ] ℝ, ∀ p ∈ C, f p + t b - t (A p) < F + ε := by
  have hn : (b, F + ε) ∉ constrainedHypograph C A f := by
    rintro ⟨p, hp, hA, hfp⟩
    have hm := hmax p hp hA
    linarith
  obtain ⟨l, u, hlu, hul⟩ := geometric_hahn_banach_closed_point
    (constrainedHypograph_convex C A f hconc)
    (constrainedHypograph_isClosed C hC A f hf) hn
  let c : ℝ := l (0, 1)
  have hdecomp (v : β → ℝ) (z : ℝ) : l (v, z) = l (v, 0) + z * c := by
    have he : (v, z) = (v, 0) + z • (0, 1) := by ext <;> simp
    rw [he, map_add, map_smul]
    rfl
  have hp₀mem : (b, F) ∈ constrainedHypograph C A f :=
    ⟨p₀, hp₀, hA₀, hf₀.ge⟩
  have hc : 0 < c := by
    have hlt := (hlu (b, F) hp₀mem).trans hul
    rw [hdecomp b F, hdecomp b (F + ε)] at hlt
    nlinarith
  let v : (β → ℝ) →ₗ[ℝ] ℝ := l.toLinearMap.comp (LinearMap.inl ℝ (β → ℝ) ℝ)
  let t : (β → ℝ) →ₗ[ℝ] ℝ := (-c⁻¹) • v
  refine ⟨t, ?_⟩
  intro p hp
  have hlt := (hlu (A p, f p) ⟨p, hp, rfl, le_rfl⟩).trans hul
  rw [hdecomp (A p) (f p), hdecomp b (F + ε)] at hlt
  have ht (x : β → ℝ) : t x = -l (x, 0) / c := by
    dsimp [t, v]
    ring
  rw [ht, ht]
  apply (mul_lt_mul_iff_right₀ hc).mp
  field_simp
  nlinarith

end
end Erdos539Geometry
