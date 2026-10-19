/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectedCountingProducts

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

theorem reflectedSupport_image_of_sum_injective (S : Finset G) (φ : G →+ H)
    (hinj : Set.InjOn φ (↑(S + S) : Set G)) {w : G} (hw : w ∈ S + S) :
    reflectedSupport (S.image φ) (φ w) = (reflectedSupport S w).image φ := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hb⟩ := Finset.mem_filter.mp hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hb
    have hs : a + b = w := by
      apply hinj (Finset.mem_add.mpr ⟨a, ha, b, hb, rfl⟩) hw
      rw [map_add, he]
      abel
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩, rfl⟩
    have heq : w - a = b := by rw [← hs]; abel
    rwa [heq]
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hb⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      Finset.mem_image.mpr ⟨w - a, hb, map_sub φ w a⟩⟩

theorem reflectedSupport_card_image (S : Finset G) (φ : G →+ H)
    (hinj : Set.InjOn φ S) (w : G) :
    ((reflectedSupport S w).image φ).card = (reflectedSupport S w).card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 he

/-- A map injective on the actual support and its sumset preserves its
counting energy exactly; global injectivity is unnecessary. -/
theorem countingEnergy_image_of_sum_injective (S : Finset G) (φ : G →+ H)
    (hinj : Set.InjOn φ S) (hsum : Set.InjOn φ (↑(S + S) : Set G)) :
    countingEnergy (S.image φ) = countingEnergy S := by
  rw [countingEnergy_eq_reflected_square_sum, ← Finset.image_add φ,
    Finset.sum_image]
  · rw [countingEnergy_eq_reflected_square_sum]
    apply Finset.sum_congr rfl
    intro w hw
    rw [reflectedSupport_image_of_sum_injective S φ hsum hw,
      reflectedSupport_card_image S φ hinj]
  · exact hsum

theorem countingDefect_image_of_sum_injective (S : Finset G) (φ : G →+ H)
    (hinj : Set.InjOn φ S) (hsum : Set.InjOn φ (↑(S + S) : Set G)) :
    countingDefect (S.image φ) = countingDefect S := by
  simp only [countingDefect, Finset.card_image_of_injOn hinj,
    countingEnergy_image_of_sum_injective S φ hinj hsum]

/-- The entire reflected-parent experiment is preserved by an additive
encoding with no collisions on the actual sumset. -/
theorem reflectedMeanCountingDefect_image_of_sum_injective (S : Finset G) (φ : G →+ H)
    (hinj : Set.InjOn φ S) (hsum : Set.InjOn φ (↑(S + S) : Set G)) :
    reflectedMeanCountingDefect (S.image φ) = reflectedMeanCountingDefect S := by
  unfold reflectedMeanCountingDefect
  rw [← Finset.image_add φ, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w hw
    have hT : reflectedSupport S w ⊆ S := Finset.filter_subset _ _
    have hTi : Set.InjOn φ (reflectedSupport S w) := hinj.mono hT
    have hTs : Set.InjOn φ (↑(reflectedSupport S w + reflectedSupport S w) : Set G) :=
      hsum.mono (Finset.add_subset_add hT hT)
    simp only [countingReflectionWeight, reflectedSupport_image_of_sum_injective S φ hsum hw,
      reflectedSupport_card_image S φ hinj, countingEnergy_image_of_sum_injective S φ hinj hsum,
      countingEnergy_image_of_sum_injective (reflectedSupport S w) φ hTi hTs]
  · exact hsum

end
end Erdos539Geometry
