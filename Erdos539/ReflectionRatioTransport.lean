/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyImageEquality
import Erdos539.ReflectedCountingTransport
import Erdos539.ReflectedNormRetention
import Erdos539.EnergyFiniteCover

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

theorem reflected_norm_bound_product {S : Finset G} {T : Finset H} {r : ℝ}
    (hr : 0 ≤ r) (hR : ∀ w, energyNorm (reflectedSupport S w) ≤ energyNorm S * r)
    (w : G × H) :
    energyNorm (reflectedSupport (S ×ˢ T) w) ≤ energyNorm (S ×ˢ T) * r := by
  rw [reflectedSupport_product, energyNorm_product, energyNorm_product]
  have h := mul_le_mul (hR w.1)
    (energyNorm_mono (Finset.filter_subset (fun x ↦ w.2 - x ∈ T) T))
    (energyNorm_nonneg _) (mul_nonneg (energyNorm_nonneg S) hr)
  change energyNorm (reflectedSupport S w.1) * energyNorm (reflectedSupport T w.2) ≤ _ at h
  nlinarith only [h]

theorem reflected_norm_bound_image {S : Finset G} (φ : G →+ H) (hi : Function.Injective φ)
    {r : ℝ} (hr : 0 ≤ r) (hR : ∀ w, energyNorm (reflectedSupport S w) ≤ energyNorm S * r)
    (w : H) :
    energyNorm (reflectedSupport (S.image φ) w) ≤ energyNorm (S.image φ) * r := by
  by_cases hw : w ∈ S.image φ + S.image φ
  · rw [← Finset.image_add φ] at hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    rw [reflectedSupport_image_of_sum_injective S φ hi.injOn hz,
      energyNorm_image_of_injective _ φ hi, energyNorm_image_of_injective _ φ hi]
    exact hR z
  · rw [reflectedSupport_eq_empty_of_notMem_add hw, energyNorm_empty]
    exact mul_nonneg (energyNorm_nonneg _) hr

/-- Any subset of a union of k reflected supports obeys the same k^2 bound.
The supports may be formed after preliminary deletion. -/
theorem reflected_cover_norm_bound {ι : Type*} [Fintype ι] {S A E : Finset G}
    (hAS : A ⊆ S) (w : ι → G) (hcover : ∀ x ∈ E, ∃ i, x ∈ reflectedSupport A (w i))
    {r : ℝ} (hr : 0 ≤ r) (hR : ∀ z, energyNorm (reflectedSupport S z) ≤ energyNorm S * r) :
    energyNorm E ≤ (Fintype.card ι : ℝ) ^ 2 * (energyNorm S * r) := by
  apply energyNorm_le_card_sq_mul_of_cover (fun i ↦ reflectedSupport A (w i)) hcover
    (mul_nonneg (energyNorm_nonneg S) hr)
  intro i
  apply (energyNorm_mono ?_).trans (hR (w i))
  intro x hx
  obtain ⟨hx, hw⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hAS hx, hAS hw⟩

end
end Erdos539Geometry
