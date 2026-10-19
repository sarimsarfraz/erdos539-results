/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic

namespace Erdos539Geometry
open scoped Classical

/-- Finite minimization with two literal successive tie rules. -/
theorem exists_three_stage_minimum {α : Type*} (C : Finset α) (hC : C.Nonempty)
    (score : α → ℝ) (size dimension : α → ℕ) :
    ∃ t ∈ C, (∀ x ∈ C, score t ≤ score x) ∧
      (∀ x ∈ C, score x = score t → size t ≤ size x) ∧
      (∀ x ∈ C, score x = score t → size x = size t → dimension t ≤ dimension x) := by
  obtain ⟨a, ha, hamin⟩ := Finset.exists_min_image C score hC
  let C₁ := C.filter (fun x ↦ score x = score a)
  have ha₁ : a ∈ C₁ := Finset.mem_filter.mpr ⟨ha, rfl⟩
  obtain ⟨b, hb, hbmin⟩ := Finset.exists_min_image C₁ size ⟨a, ha₁⟩
  let C₂ := C₁.filter (fun x ↦ size x = size b)
  have hb₂ : b ∈ C₂ := Finset.mem_filter.mpr ⟨hb, rfl⟩
  obtain ⟨t, ht, htmin⟩ := Finset.exists_min_image C₂ dimension ⟨b, hb₂⟩
  have ht₁ := (Finset.mem_filter.mp ht).1
  have htsize := (Finset.mem_filter.mp ht).2
  have htC := (Finset.mem_filter.mp ht₁).1
  have htscore := (Finset.mem_filter.mp ht₁).2
  refine ⟨t, htC, ?_, ?_, ?_⟩
  · intro x hx
    rw [htscore]
    exact hamin x hx
  · intro x hx hscore
    rw [htsize]
    exact hbmin x (Finset.mem_filter.mpr ⟨hx, hscore.trans htscore⟩)
  · intro x hx hscore hsize
    apply htmin x
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hx, hscore.trans htscore⟩,
      hsize.trans htsize⟩

end Erdos539Geometry
