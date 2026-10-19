/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProductEnergy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical

/-- Literal finite pushforward of a weight along a map. When the map is
injective on the support, every nonzero fiber has its unique original value. -/
def pushWeight {G H : Type*} [DecidableEq H] (S : Finset G) (φ : G → H) (w : G → ℝ) (y : H) : ℝ :=
  ∑ x ∈ S, if φ x = y then w x else 0

theorem pushWeight_at_image {G H : Type*} [DecidableEq H] {S : Finset G} {φ : G → H}
    (hinj : Set.InjOn φ S) (w : G → ℝ) {x : G} (hx : x ∈ S) :
    pushWeight S φ w (φ x) = w x := by
  unfold pushWeight
  rw [Finset.sum_eq_single x]
  · simp
  · intro y hy hyx
    have hne : φ y ≠ φ x := fun h ↦ hyx (hinj hy hx h)
    simp only [if_neg hne]
  · exact fun h ↦ (h hx).elim

theorem pushWeight_zero {G H : Type*} [DecidableEq H] {S : Finset G} {φ : G → H}
    (w : G → ℝ) {y : H} (hy : y ∉ S.image φ) : pushWeight S φ w y = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  exact if_neg (fun h ↦ hy (Finset.mem_image.mpr ⟨x, hx, h⟩))

theorem pushWeight_nonneg {G H : Type*} [DecidableEq H] {S : Finset G} {φ : G → H}
    {w : G → ℝ} (hw : ∀ x ∈ S, 0 ≤ w x) (y : H) : 0 ≤ pushWeight S φ w y := by
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact hw x hx
  · rfl

theorem pushWeight_mono {G H : Type*} [DecidableEq H] {A S : Finset G} (hAS : A ⊆ S)
    (φ : G → H) {w : G → ℝ} (hw : ∀ x ∈ S, 0 ≤ w x) (y : H) :
    pushWeight A φ w y ≤ pushWeight S φ w y := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hAS
  intro x hx _
  split_ifs
  · exact hw x hx
  · rfl

variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

/-- Injective additive transport preserves the entire weighted energy.
This is an equality of actual finite sums, not only a norm inequality. -/
theorem weightedEnergy_pushWeight (S : Finset G) (φ : G →+ H) (hinj : Function.Injective φ)
    (w : G → ℝ) : weightedEnergy (S.image φ) (pushWeight S φ w) = weightedEnergy S w := by
  have hsum (g : H → ℝ) : (∑ y ∈ S.image φ, g y) = ∑ x ∈ S, g (φ x) :=
    Finset.sum_image (fun a _ b _ hab ↦ hinj hab)
  rw [weightedEnergy_eq_four_sum, weightedEnergy_eq_four_sum]
  simp_rw [hsum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  have he : φ a + φ b = φ c + φ d ↔ a + b = c + d := by
    rw [← map_add, ← map_add, hinj.eq_iff]
  simp only [he, pushWeight_at_image hinj.injOn w ha, pushWeight_at_image hinj.injOn w hb,
    pushWeight_at_image hinj.injOn w hc, pushWeight_at_image hinj.injOn w hd]

end
end Erdos539Geometry
