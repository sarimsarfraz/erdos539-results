/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PairCounting

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*} [Fintype ι]

/-- The projection retaining every coordinate except one. -/
def offCoordinate (i : ι) : Finset ι := Finset.univ.erase i

def lineProjection (i : ι) (x : ι → ℝ) : offCoordinate i → ℝ := project (offCoordinate i) x

/-- The weak upper tail on a single coordinate line. -/
def coordinateUpperTail (F : Finset (ι → ℝ)) (i : ι) (a : ι → ℝ) : Finset (ι → ℝ) :=
  F.filter (fun x ↦ lineProjection i x = lineProjection i a ∧ a i ≤ x i)

@[simp] theorem mem_coordinateUpperTail {F : Finset (ι → ℝ)} {i : ι} {a x : ι → ℝ} :
    x ∈ coordinateUpperTail F i a ↔ x ∈ F ∧ lineProjection i x = lineProjection i a ∧ a i ≤ x i := by
  simp only [coordinateUpperTail, Finset.mem_filter]

/-- Remove at most k highest points on each coordinate line. -/
def trimCoordinate (F : Finset (ι → ℝ)) (i : ι) (k : ℕ) : Finset (ι → ℝ) :=
  F.filter (fun a ↦ k < (coordinateUpperTail F i a).card)

@[simp] theorem mem_trimCoordinate {F : Finset (ι → ℝ)} {i : ι} {k : ℕ} {a : ι → ℝ} :
    a ∈ trimCoordinate F i k ↔ a ∈ F ∧ k < (coordinateUpperTail F i a).card := Finset.mem_filter

theorem trimCoordinate_subset (F : Finset (ι → ℝ)) (i : ι) (k : ℕ) : trimCoordinate F i k ⊆ F :=
  fun _ hx ↦ (mem_trimCoordinate.mp hx).1

/-- Each discarded coordinate fiber has size at most k, using its minimum
coordinate as a common witness. Ties cause no loss. -/
theorem discarded_fiber_card_le (F : Finset (ι → ℝ)) (i : ι) (k : ℕ)
    (b : offCoordinate i → ℝ) :
    (fiber (F \ trimCoordinate F i k) (lineProjection i) b).card ≤ k := by
  classical
  let B := fiber (F \ trimCoordinate F i k) (lineProjection i) b
  by_cases hB : B.Nonempty
  · obtain ⟨a, ha, hmin⟩ := B.exists_min_image (fun x ↦ x i) hB
    obtain ⟨haF, hant⟩ := Finset.mem_sdiff.mp (mem_fiber.mp ha).1
    have htail : (coordinateUpperTail F i a).card ≤ k := by
      by_contra hn
      exact hant (mem_trimCoordinate.mpr ⟨haF, by omega⟩)
    have hsub : B ⊆ coordinateUpperTail F i a := by
      intro x hx
      apply mem_coordinateUpperTail.mpr
      exact ⟨(Finset.mem_sdiff.mp (mem_fiber.mp hx).1).1,
        (mem_fiber.mp hx).2.trans (mem_fiber.mp ha).2.symm, hmin x hx⟩
    exact (Finset.card_le_card hsub).trans htail
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    change B.card ≤ k
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

/-- Trimming a subset charges only the number of coordinate lines in the
original parent. -/
theorem trimCoordinate_removal_bound {S F : Finset (ι → ℝ)} (hSF : S ⊆ F) (i : ι) (k : ℕ) :
    S.card ≤ (trimCoordinate S i k).card + k * (F.image (lineProjection i)).card := by
  classical
  let B := S \ trimCoordinate S i k
  have hBF : B ⊆ F := fun _ hx ↦ hSF (Finset.mem_sdiff.mp hx).1
  have hc := card_le_image_mul_of_fiber_le B (lineProjection i) k
    (fun b _ ↦ discarded_fiber_card_le S i k b)
  have hp := Finset.card_le_card (Finset.image_subset_image (f := lineProjection i) hBF)
  have hsum := Finset.card_sdiff_add_card_eq_card (trimCoordinate_subset S i k)
  have hbound := hc.trans (Nat.mul_le_mul_right k hp)
  dsimp only [B] at hbound
  nlinarith

/-- On a coordinate line, the moving coordinate determines the whole point. -/
theorem coordinate_line_injective {i : ι} {a x y : ι → ℝ}
    (hx : lineProjection i x = lineProjection i a) (hy : lineProjection i y = lineProjection i a)
    (hi : x i = y i) : x = y := by
  funext j
  by_cases hj : j = i
  · simpa only [hj] using hi
  · exact congrFun (hx.trans hy.symm) ⟨j, by simp [offCoordinate, hj]⟩

theorem coordinateUpperTail_above {F : Finset (ι → ℝ)} {i : ι} {a x : ι → ℝ}
    (hx : x ∈ coordinateUpperTail F i a) : ∀ j, a j ≤ x j := by
  intro j
  by_cases hj : j = i
  · simpa only [hj] using (mem_coordinateUpperTail.mp hx).2.2
  · have h := congrFun (mem_coordinateUpperTail.mp hx).2.1 ⟨j, by simp [offCoordinate, hj]⟩
    change x j = a j at h
    exact h.symm.le

end
end Erdos539Geometry
