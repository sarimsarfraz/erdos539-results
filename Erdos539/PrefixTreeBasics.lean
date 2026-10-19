/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PairCounting
import Mathlib.Data.Fin.Tuple.Basic

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical

/-- The actual labels of the first coordinate of an original finite set. -/
def prefixLabels {d : ℕ} (S : Finset (Fin (d + 1) → ℝ)) : Finset ℝ :=
  S.image (fun x ↦ x 0)

/-- Actual suffixes below a prescribed original first-coordinate label. -/
def prefixChild {d : ℕ} (S : Finset (Fin (d + 1) → ℝ)) (t : ℝ) : Finset (Fin d → ℝ) :=
  (S.filter (fun x ↦ x 0 = t)).image Fin.tail

@[simp] theorem mem_prefixLabels {d : ℕ} {S : Finset (Fin (d + 1) → ℝ)} {t : ℝ} :
    t ∈ prefixLabels S ↔ ∃ x ∈ S, x 0 = t := Finset.mem_image

@[simp] theorem mem_prefixChild {d : ℕ} {S : Finset (Fin (d + 1) → ℝ)} {t : ℝ} {x : Fin d → ℝ} :
    x ∈ prefixChild S t ↔ Fin.cons t x ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hy, he⟩ := Finset.mem_filter.mp hy
    simpa only [← he, Fin.cons_self_tail] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨Fin.cons t x, Finset.mem_filter.mpr ⟨hx, by simp⟩, by simp⟩

theorem prefixChild_nonempty_iff {d : ℕ} {S : Finset (Fin (d + 1) → ℝ)} {t : ℝ} :
    (prefixChild S t).Nonempty ↔ t ∈ prefixLabels S := by
  constructor
  · rintro ⟨x, hx⟩
    exact mem_prefixLabels.mpr ⟨Fin.cons t x, mem_prefixChild.mp hx, by simp⟩
  · intro ht
    obtain ⟨x, hx, he⟩ := mem_prefixLabels.mp ht
    refine ⟨Fin.tail x, mem_prefixChild.mpr ?_⟩
    simpa only [← he, Fin.cons_self_tail] using hx

theorem prefixChild_mono {d : ℕ} {A S : Finset (Fin (d + 1) → ℝ)} (hAS : A ⊆ S) (t : ℝ) :
    prefixChild A t ⊆ prefixChild S t := by
  intro x hx
  exact mem_prefixChild.mpr (hAS (mem_prefixChild.mp hx))

theorem prefixLabels_mono {d : ℕ} {A S : Finset (Fin (d + 1) → ℝ)} (hAS : A ⊆ S) :
    prefixLabels A ⊆ prefixLabels S := Finset.image_subset_image hAS

theorem prefixChild_card {d : ℕ} (S : Finset (Fin (d + 1) → ℝ)) (t : ℝ) :
    (prefixChild S t).card = (S.filter (fun x ↦ x 0 = t)).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy he
  have hx0 := (Finset.mem_filter.mp hx).2
  have hy0 := (Finset.mem_filter.mp hy).2
  rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, hx0, hy0, he]

theorem sum_prefixChild_card {d : ℕ} (S : Finset (Fin (d + 1) → ℝ)) :
    ∑ t ∈ prefixLabels S, (prefixChild S t).card = S.card := by
  simp_rw [prefixChild_card]
  exact (Finset.card_eq_sum_card_image (fun x ↦ x 0) S).symm

/-- Assemble selected actual child sets using their unchanged real labels. -/
def prefixAssemble {d : ℕ} (L : Finset ℝ) (T : ℝ → Finset (Fin d → ℝ)) : Finset (Fin (d + 1) → ℝ) :=
  L.biUnion (fun t ↦ (T t).image (Fin.cons t))

@[simp] theorem mem_prefixAssemble {d : ℕ} {L : Finset ℝ} {T : ℝ → Finset (Fin d → ℝ)}
    {x : Fin (d + 1) → ℝ} :
    x ∈ prefixAssemble L T ↔ x 0 ∈ L ∧ Fin.tail x ∈ T (x 0) := by
  constructor
  · intro hx
    obtain ⟨t, ht, hy⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hy
    have h0 := congrFun he 0
    have htail := congrArg Fin.tail he
    simp only [Fin.cons_zero] at h0
    simp only [Fin.tail_cons] at htail
    exact ⟨h0 ▸ ht, by simpa only [← h0, ← htail] using hy⟩
  · rintro ⟨h0, ht⟩
    exact Finset.mem_biUnion.mpr ⟨x 0, h0, Finset.mem_image.mpr ⟨Fin.tail x, ht, Fin.cons_self_tail x⟩⟩

theorem prefixAssemble_subset {d : ℕ} {S : Finset (Fin (d + 1) → ℝ)}
    (L : Finset ℝ) (T : ℝ → Finset (Fin d → ℝ))
    (hT : ∀ t ∈ L, T t ⊆ prefixChild S t) : prefixAssemble L T ⊆ S := by
  intro x hx
  obtain ⟨h0, ht⟩ := mem_prefixAssemble.mp hx
  have h := mem_prefixChild.mp (hT (x 0) h0 ht)
  simpa only [Fin.cons_self_tail] using h

theorem prefixChild_assemble {d : ℕ} {L : Finset ℝ} {T : ℝ → Finset (Fin d → ℝ)}
    {t : ℝ} (ht : t ∈ L) : prefixChild (prefixAssemble L T) t = T t := by
  ext x
  simp only [mem_prefixChild, mem_prefixAssemble, Fin.cons_zero, Fin.tail_cons, ht, true_and]

theorem prefixLabels_assemble {d : ℕ} {L : Finset ℝ} {T : ℝ → Finset (Fin d → ℝ)}
    (hT : ∀ t ∈ L, (T t).Nonempty) : prefixLabels (prefixAssemble L T) = L := by
  ext t
  constructor
  · intro ht
    obtain ⟨x, hx, he⟩ := mem_prefixLabels.mp ht
    exact he ▸ (mem_prefixAssemble.mp hx).1
  · intro ht
    obtain ⟨x, hx⟩ := hT t ht
    exact mem_prefixLabels.mpr ⟨Fin.cons t x,
      mem_prefixAssemble.mpr (by simpa using And.intro ht hx), by simp⟩

end
end Erdos539Geometry
