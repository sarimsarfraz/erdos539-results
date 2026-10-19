/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ExceptionalSumEnergy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The literal reflected intersection S intersect (w-S). -/
def reflectedSupport (S : Finset G) (w : G) : Finset G := S.filter (fun x ↦ w - x ∈ S)

theorem reflectedSupport_eq_inter (S : Finset G) (w : G) :
    reflectedSupport S w = S ∩ S.image (fun x ↦ w - x) := by
  ext x
  simp only [reflectedSupport, Finset.mem_filter, Finset.mem_inter, Finset.mem_image]
  constructor
  · rintro ⟨hx, hreflect⟩
    exact ⟨hx, w - x, hreflect, by abel⟩
  · rintro ⟨hx, y, hy, he⟩
    refine ⟨hx, ?_⟩
    have hxy : w - x = y := by rw [← he]; abel
    rwa [hxy]

/-- Ordered sum representations can equivalently be counted by their
first endpoint, exactly as in the research certificate. -/
theorem sumFiber_card_eq_representation_card (S : Finset G) (z : G) :
    (fiber (S ×ˢ S) (fun p ↦ p.1 + p.2) z).card = (S.filter (fun x ↦ z - x ∈ S)).card := by
  apply Finset.card_bij (fun p _ ↦ p.1)
  · intro p hp
    obtain ⟨hpS, hpz⟩ := mem_fiber.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hpS
    apply Finset.mem_filter.mpr
    refine ⟨ha, ?_⟩
    have he : z - p.1 = p.2 := by rw [← hpz]; abel
    rwa [he]
  · intro p hp q hq he
    have hsum := (mem_fiber.mp hp).2.trans (mem_fiber.mp hq).2.symm
    rw [he] at hsum
    exact Prod.ext he (add_left_cancel hsum)
  · intro x hx
    obtain ⟨hxS, hother⟩ := Finset.mem_filter.mp hx
    refine ⟨(x, z - x), mem_fiber.mpr ⟨Finset.mem_product.mpr ⟨hxS, hother⟩, ?_⟩, rfl⟩
    dsimp only
    abel

/-- The deterministic reflected-support certificate, with exactly the
noncentral representation hypothesis in the note. It includes the empty
support and holds in any additive commutative group. -/
theorem reflectedSupport_energyNorm_le (S : Finset G) (w : G) {R : ℝ} (hR : 0 ≤ R)
    (hrepr : ∀ z : G, z ≠ w →
      (((reflectedSupport S w).filter (fun x ↦ z - x ∈ reflectedSupport S w)).card : ℝ) ≤ R) :
    energyNorm (reflectedSupport S w) ≤ R + 1 := by
  apply energyNorm_le_exceptional_sum_bound (reflectedSupport S w) w hR
  intro z hz
  rw [sumFiber_card_eq_representation_card]
  exact hrepr z hz

/-- Deleting points and independently reoptimizing their weights cannot
evade the deterministic reflected-support bound. -/
theorem reflectedSupport_subset_energyNorm_le (S : Finset G) (w : G) {R : ℝ} (hR : 0 ≤ R)
    (hrepr : ∀ z : G, z ≠ w →
      (((reflectedSupport S w).filter (fun x ↦ z - x ∈ reflectedSupport S w)).card : ℝ) ≤ R)
    {A : Finset G} (hA : A ⊆ reflectedSupport S w) : energyNorm A ≤ R + 1 :=
  (energyNorm_mono hA).trans (reflectedSupport_energyNorm_le S w hR hrepr)

end
end Erdos539Geometry
