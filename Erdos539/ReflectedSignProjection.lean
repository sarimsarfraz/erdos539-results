/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PopularReflectedSupport
import Erdos539.CornerProjections

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

/-- Signs about the actual reflection center w/2, only on the physical
block B. Ties are assigned to the nonnegative side. -/
def reflectionSignMask (B : Finset ι) (w x : ι → ℝ) : Finset ι := B.filter (fun i ↦ w i ≤ 2 * x i)

theorem reflectionSignMask_subset (B : Finset ι) (w x : ι → ℝ) : reflectionSignMask B w x ⊆ B :=
  Finset.filter_subset _ _

/-- The two projection witnesses are actual reflected anchors in the
original fiber. No translated parent or new palette is substituted. -/
theorem reflected_sign_projection_fans {A F : Finset (ι → ℝ)} {w : ι → ℝ}
    (hA : A.Nonempty) (hAF : A ⊆ reflectedSupport F w) (B P : Finset ι)
    (hmask : ∀ x ∈ A, reflectionSignMask B w x = P) :
    ∃ a ∈ A, w - a ∈ F ∧
      (projection A P).card ≤ (fan F (w - a)).card ∧
      (projection A (B \ P)).card ≤ (fan F a).card := by
  obtain ⟨a, ha⟩ := hA
  have hsub : A ⊆ F := fun x hx ↦ (Finset.mem_filter.mp (hAF hx)).1
  have href (x : ι → ℝ) (hx : x ∈ A) : w - x ∈ F := (Finset.mem_filter.mp (hAF hx)).2
  refine ⟨a, ha, href a ha, ?_, ?_⟩
  · apply (projection_card_le_fan_of_minimum A P (w - a) ?_).trans
      (Finset.card_le_card (fan_mono hsub (w - a)))
    intro x hx i hi
    have hxi : w i ≤ 2 * x i := (Finset.mem_filter.mp (show i ∈ reflectionSignMask B w x by rw [hmask x hx]; exact hi)).2
    have hai : w i ≤ 2 * a i := (Finset.mem_filter.mp (show i ∈ reflectionSignMask B w a by rw [hmask a ha]; exact hi)).2
    change w i - a i ≤ x i
    linarith
  · let recover : (ι → ℝ) → (↥(B \ P) → ℝ) := fun z i ↦ w i - a i - z i
    have hs : projection A (B \ P) ⊆ (fan F a).image recover := by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_image.mpr ⟨pdiff (w - x) a, mem_fan.mpr ⟨w - x, href x hx, rfl⟩, ?_⟩
      funext i
      have hi := Finset.mem_sdiff.mp i.property
      have hneg (z : ι → ℝ) (hz : z ∈ A) : 2 * z i.val < w i.val := by
        apply lt_of_not_ge
        intro he
        have hm : i.val ∈ reflectionSignMask B w z := Finset.mem_filter.mpr ⟨hi.1, he⟩
        rw [hmask z hz] at hm
        exact hi.2 hm
      have hx' := hneg x hx
      have ha' := hneg a ha
      change w i.val - a i.val - max (w i.val - x i.val - a i.val) 0 = x i.val
      rw [max_eq_left (by linarith)]
      ring
    exact (Finset.card_le_card hs).trans Finset.card_image_le

end
end Erdos539Geometry
