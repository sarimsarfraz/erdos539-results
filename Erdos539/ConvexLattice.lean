/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.MidpointBound
import Mathlib.Analysis.Convex.Basic

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι M : Type*} [AddCommGroup M]

/-- A full convex intersection is midpoint-closed relative to its actual group. -/
theorem convex_preimage_midpointClosed (e : M →ₗ[ℤ] (ι → ℝ))
    {C : Set (ι → ℝ)} (hC : Convex ℝ C) {F : Finset M}
    (hF : ∀ x, x ∈ F ↔ e x ∈ C) : GroupMidpointClosed F := by
  intro x hx y hy z hz
  apply (hF z).mpr
  have hm := hC.midpoint_mem ((hF x).mp hx) ((hF y).mp hy)
  have heq : midpoint ℝ (e x) (e y) = e z := by
    have hadd := congrArg e hz
    simp only [two_zsmul, map_add] at hadd
    have hh := midpoint_add_self ℝ (e x) (e y)
    rw [hadd] at hh
    funext i
    have hi := congrFun hh i
    change midpoint ℝ (e x) (e y) i + midpoint ℝ (e x) (e y) i = e z i + e z i at hi
    linarith
  rwa [heq] at hm

/-- Literal finite subsets of a real coordinate space, relatively midpoint-closed
in a finite free integral subgroup, satisfy the sharp rank-dependent bound. -/
theorem subgroup_midpoint_fan_bound [Fintype ι]
    (Γ : Submodule ℤ (ι → ℝ)) [Module.Free ℤ Γ] [Module.Finite ℤ Γ]
    {S : Finset (ι → ℝ)} (hS : S.Nonempty) (hSΓ : ∀ x ∈ S, x ∈ Γ)
    (hmid : ∀ x ∈ S, ∀ y ∈ S, ∀ z : Γ, x + y = (2 : ℤ) • z.val → z.val ∈ S)
    (hd : 0 < Fintype.card ι) :
    (S.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) /
      (2 : ℝ) ^ (Fintype.card ι + 3 * Module.finrank ℤ Γ) ≤ maxFan S := by
  classical
  let F := S.preimage Γ.subtype Subtype.val_injective.injOn
  have hF : F.Nonempty := by
    obtain ⟨x, hx⟩ := hS
    exact ⟨⟨x, hSΓ x hx⟩, Finset.mem_preimage.mpr hx⟩
  have himage : F.image Γ.subtype = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_preimage.mp hy
    · intro hx
      exact Finset.mem_image.mpr ⟨⟨x, hSΓ x hx⟩, Finset.mem_preimage.mpr hx, rfl⟩
  have hcard : F.card = S.card := by
    have hc := Finset.card_image_of_injective F (show Function.Injective Γ.subtype from Subtype.val_injective)
    exact hc.symm.trans (congrArg Finset.card himage)
  have hFm : GroupMidpointClosed F := by
    intro x hx y hy z hz
    apply Finset.mem_preimage.mpr
    exact hmid x.val (Finset.mem_preimage.mp hx) y.val (Finset.mem_preimage.mp hy) z
      (congrArg Subtype.val hz)
  have h := midpoint_fan_bound Γ.subtype Subtype.val_injective hF hFm hd
  rwa [himage, hcard] at h

/-- Exact convex-lattice conclusion. Rank d suffices; discreteness is unnecessary
for a finite intersection, so this also covers every rank-d lattice. -/
theorem convex_lattice_fan_bound [Fintype ι]
    (Γ : Submodule ℤ (ι → ℝ)) [Module.Free ℤ Γ] [Module.Finite ℤ Γ]
    (hrank : Module.finrank ℤ Γ = Fintype.card ι)
    {C : Set (ι → ℝ)} (hC : Convex ℝ C) {S : Finset (ι → ℝ)}
    (hS : S.Nonempty) (hinter : (S : Set (ι → ℝ)) = C ∩ Γ)
    (hd : 0 < Fintype.card ι) :
    (S.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) /
      (16 : ℝ) ^ Fintype.card ι ≤ maxFan S := by
  have hSΓ : ∀ x ∈ S, x ∈ Γ := by
    intro x hx
    have hh : x ∈ (S : Set (ι → ℝ)) := hx
    rw [hinter] at hh
    exact hh.2
  have hmid : ∀ x ∈ S, ∀ y ∈ S, ∀ z : Γ, x + y = (2 : ℤ) • z.val → z.val ∈ S := by
    intro x hx y hy z hz
    have hxC : x ∈ C := by
      have hh : x ∈ (S : Set (ι → ℝ)) := hx
      rw [hinter] at hh
      exact hh.1
    have hyC : y ∈ C := by
      have hh : y ∈ (S : Set (ι → ℝ)) := hy
      rw [hinter] at hh
      exact hh.1
    have hm := hC.midpoint_mem hxC hyC
    have heq : midpoint ℝ x y = z.val := by
      have hh := midpoint_add_self ℝ x y
      rw [hz, two_zsmul] at hh
      funext i
      have hi := congrFun hh i
      change midpoint ℝ x y i + midpoint ℝ x y i = z.val i + z.val i at hi
      linarith
    rw [heq] at hm
    show z.val ∈ (S : Set (ι → ℝ))
    rw [hinter]
    exact ⟨hm, z.property⟩
  have h := subgroup_midpoint_fan_bound Γ hS hSΓ hmid hd
  rw [hrank] at h
  have he : Fintype.card ι + 3 * Fintype.card ι = 4 * Fintype.card ι := by omega
  rw [he, pow_mul] at h
  norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num] at h
  exact h

end
end Erdos539Geometry
