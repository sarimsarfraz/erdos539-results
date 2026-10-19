/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StripEncoding
import Erdos539.UniformProductConditional

namespace Erdos539Geometry
noncomputable section
open scoped Classical Pointwise

theorem separatedPair_interval_injOn {T : ℕ} {H : ℤ} (hH : (T : ℤ) < H) :
    Set.InjOn (separatedPair H) (↑(scalarInterval T ×ˢ scalarInterval T) : Set (ℤ × ℤ)) := by
  intro a ha b hb he
  have hax := Finset.mem_Ico.mp (Finset.mem_product.mp ha).2
  have hbx := Finset.mem_Ico.mp (Finset.mem_product.mp hb).2
  exact separatedPair_injective (lt_of_le_of_lt (Int.natCast_nonneg T) hH)
    ⟨hax.1, hax.2.trans hH⟩ ⟨hbx.1, hbx.2.trans hH⟩ he

theorem intervalPair_add_subset (T : ℕ) :
    (scalarInterval T ×ˢ scalarInterval T) + (scalarInterval T ×ˢ scalarInterval T) ⊆
      scalarInterval (2 * T) ×ˢ scalarInterval (2 * T) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
  simp only [Finset.mem_product, scalarInterval, Finset.mem_Ico] at ha hb ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  omega

theorem gibbsStrip_projection {T : ℕ} (hT : 0 < T) (H : ℤ) :
    (gibbsStrip T H).image stripProjection = stripProjected T H := by
  ext z
  constructor
  · intro hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨a.1, (Finset.mem_product.mp ha).1, rfl⟩
  · intro hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    have h0 : (0 : ℤ) ∈ scalarInterval T := by simp [scalarInterval, hT]
    exact Finset.mem_image.mpr ⟨stripEncode H (p, 0),
      Finset.mem_image.mpr ⟨(p, 0), Finset.mem_product.mpr ⟨hp, h0⟩, rfl⟩, rfl⟩

theorem stripProjected_card {T : ℕ} {H : ℤ} (hH : (T : ℤ) < H) :
    (stripProjected T H).card = T ^ 2 := by
  rw [stripProjected, Finset.card_image_of_injOn (separatedPair_interval_injOn hH),
    Finset.card_product, scalarInterval_card]
  ring

theorem stripProjected_countingEnergy {T : ℕ} {H : ℤ} (hH : 2 * (T : ℤ) < H) :
    countingEnergy (stripProjected T H) = countingEnergy (scalarInterval T) ^ 2 := by
  rw [stripProjected, countingEnergy_image_of_sum_injective _ _
    (separatedPair_interval_injOn (by omega))
    ((separatedPair_interval_injOn (T := 2 * T) (by simpa using hH)).mono (intervalPair_add_subset T)),
    countingEnergy_product]
  ring

theorem stripFiberDigits_subset {T : ℕ} {p : ℤ × ℤ}
    (hp : p ∈ scalarInterval T ×ˢ scalarInterval T) :
    {p} ×ˢ scalarInterval T ⊆ stripDigits T := by
  intro a ha
  obtain ⟨hap, haT⟩ := Finset.mem_product.mp ha
  exact Finset.mem_product.mpr ⟨(Finset.mem_singleton.mp hap) ▸ hp, haT⟩

theorem gibbsStrip_fiber {T : ℕ} {H : ℤ} (hH : (T : ℤ) < H) {p : ℤ × ℤ}
    (hp : p ∈ scalarInterval T ×ˢ scalarInterval T) :
    fiber (gibbsStrip T H) stripProjection (separatedPair H p) =
      ({p} ×ˢ scalarInterval T).image (stripEncode H) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, he⟩ := mem_fiber.mp hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have hap := separatedPair_interval_injOn hH (Finset.mem_product.mp ha).1 hp he
    exact Finset.mem_image.mpr ⟨a,
      Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hap, (Finset.mem_product.mp ha).2⟩, rfl⟩
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have hap := Finset.mem_singleton.mp (Finset.mem_product.mp ha).1
    exact mem_fiber.mpr ⟨Finset.mem_image.mpr ⟨a, stripFiberDigits_subset hp ha, rfl⟩,
      congrArg (separatedPair H) hap⟩

theorem gibbsStrip_fiber_card {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : (T : ℤ) < H)
    (y : (gibbsStrip T H).image stripProjection) :
    (fiber (gibbsStrip T H) stripProjection y.val).card = T := by
  have hy : y.val ∈ stripProjected T H := by
    simpa only [gibbsStrip_projection hT H] using y.property
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hy
  rw [← he, gibbsStrip_fiber hH hp,
    Finset.card_image_of_injOn ((stripEncode_injOn hH).mono (stripFiberDigits_subset hp)),
    Finset.card_product, Finset.card_singleton, scalarInterval_card, one_mul]

theorem gibbsStrip_fiber_countingEnergy {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H)
    (y : (gibbsStrip T H).image stripProjection) :
    countingEnergy (fiber (gibbsStrip T H) stripProjection y.val) = countingEnergy (scalarInterval T) := by
  have hy : y.val ∈ stripProjected T H := by
    simpa only [gibbsStrip_projection hT H] using y.property
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hy
  have hs := stripFiberDigits_subset hp
  have hss : ({p} ×ˢ scalarInterval T) + ({p} ×ˢ scalarInterval T) ⊆ stripDigits (2 * T) :=
    (Finset.add_subset_add hs hs).trans (stripDigits_add_subset T)
  rw [← he, gibbsStrip_fiber (by omega) hp,
    countingEnergy_image_of_sum_injective _ _ ((stripEncode_injOn (by omega)).mono hs)
      ((stripEncode_injOn (T := 2 * T) (by simpa using hH)).mono hss),
    countingEnergy_product, countingEnergy_singleton, one_mul]

end
end Erdos539Geometry
