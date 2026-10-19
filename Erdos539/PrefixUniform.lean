/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FeasibleProfiles
import Mathlib.Algebra.BigOperators.Fin

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical

/-- Every retained parent at a given depth has exactly a_i+1 actual children.
The profile stores branching numbers minus one, matching the compressed downset. -/
def PrefixUniform : (d : ℕ) → Finset (Fin d → ℝ) → (Fin d → ℕ) → Prop
  | 0, S, _ => S.Nonempty
  | d + 1, S, a => (prefixLabels S).card = a 0 + 1 ∧
      ∀ t ∈ prefixLabels S, PrefixUniform d (prefixChild S t) (Fin.tail a)

theorem PrefixUniform.nonempty {d : ℕ} {S : Finset (Fin d → ℝ)} {a : Fin d → ℕ}
    (h : PrefixUniform d S a) : S.Nonempty := by
  cases d with
  | zero => exact h
  | succ d =>
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (show 0 < (prefixLabels S).card by rw [h.1]; omega)
    obtain ⟨x, hx, _he⟩ := mem_prefixLabels.mp ht
    exact ⟨x, hx⟩

theorem PrefixUniform.card {d : ℕ} {S : Finset (Fin d → ℝ)} {a : Fin d → ℕ}
    (h : PrefixUniform d S a) : S.card = ∏ i, (a i + 1) := by
  induction d with
  | zero =>
    obtain ⟨x, hx⟩ := h.nonempty
    have he : S = {x} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hx, fun _ _ ↦ Subsingleton.elim _ _⟩
    simp [he]
  | succ d ih =>
    rw [← sum_prefixChild_card S, Fin.prod_univ_succ]
    calc
      _ = ∑ _t ∈ prefixLabels S, ∏ i, (Fin.tail a i + 1) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact ih (h.2 t ht)
      _ = _ := by simp [h.1, Fin.tail]

/-- Every compressed profile lifts to a genuine selected original tree. -/
theorem exists_prefixUniform_subset (d : ℕ) (S : Finset (Fin d → ℝ))
    {a : Fin d → ℕ} (ha : a ∈ feasibleProfiles d S) :
    ∃ T ⊆ S, PrefixUniform d T a := by
  induction d with
  | zero =>
    refine ⟨S, Finset.Subset.refl S, ?_⟩
    exact feasibleProfiles_nonempty_iff.mp ⟨a, ha⟩
  | succ d ih =>
    have ha' := mem_profileStack.mp ha
    let K := (prefixLabels S).filter (fun t ↦ Fin.tail a ∈ feasibleProfiles d (prefixChild S t))
    have hK : a 0 + 1 ≤ K.card := Nat.succ_le_iff.mpr ha'
    obtain ⟨L, hLK, hLc⟩ := Finset.exists_subset_card_eq hK
    have hex : ∀ t : ℝ, ∃ U : Finset (Fin d → ℝ),
        t ∈ L → U ⊆ prefixChild S t ∧ PrefixUniform d U (Fin.tail a) := by
      intro t
      by_cases ht : t ∈ L
      · have hprof := (Finset.mem_filter.mp (hLK ht)).2
        obtain ⟨U, hU, hu⟩ := ih (prefixChild S t) hprof
        exact ⟨U, fun _ ↦ ⟨hU, hu⟩⟩
      · exact ⟨∅, fun h ↦ False.elim (ht h)⟩
    choose T hT using hex
    have hTne : ∀ t ∈ L, (T t).Nonempty := fun t ht ↦ (hT t ht).2.nonempty
    have hlabels := prefixLabels_assemble hTne
    refine ⟨prefixAssemble L T, prefixAssemble_subset L T (fun t ht ↦ (hT t ht).1), ?_⟩
    change (prefixLabels (prefixAssemble L T)).card = a 0 + 1 ∧ _
    rw [hlabels]
    refine ⟨hLc, ?_⟩
    intro t ht
    rw [prefixChild_assemble ht]
    exact (hT t ht).2

/-- Retained leaves are determined by their actual coordinates at branching
levels. Nonbranching coordinates may depend on earlier original labels. -/
theorem PrefixUniform.eq_of_active_eq {d : ℕ} {S : Finset (Fin d → ℝ)} {a : Fin d → ℕ}
    (h : PrefixUniform d S a) {x y : Fin d → ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hactive : ∀ i, 0 < a i → x i = y i) : x = y := by
  induction d with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    have hxL : x 0 ∈ prefixLabels S := mem_prefixLabels.mpr ⟨x, hx, rfl⟩
    have hyL : y 0 ∈ prefixLabels S := mem_prefixLabels.mpr ⟨y, hy, rfl⟩
    have hhead : x 0 = y 0 := by
      by_cases ha : 0 < a 0
      · exact hactive 0 ha
      · have hc : (prefixLabels S).card ≤ 1 := by rw [h.1]; omega
        exact Finset.card_le_one.mp hc _ hxL _ hyL
    have hxchild : Fin.tail x ∈ prefixChild S (x 0) := mem_prefixChild.mpr (by simpa using hx)
    have hychild : Fin.tail y ∈ prefixChild S (x 0) := mem_prefixChild.mpr (by simpa only [hhead, Fin.cons_self_tail] using hy)
    have htail : Fin.tail x = Fin.tail y := ih (h.2 (x 0) hxL) hxchild hychild (fun i hi ↦ hactive i.succ hi)
    rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, hhead, htail]

/-- Actual original-coordinate projection, with no relabeling assumption. -/
theorem PrefixUniform.project_injOn {d : ℕ} {S : Finset (Fin d → ℝ)} {a : Fin d → ℕ}
    (h : PrefixUniform d S a) :
    (S : Set (Fin d → ℝ)).InjOn (project (Finset.univ.filter (fun i ↦ 0 < a i))) := by
  intro x hx y hy he
  apply h.eq_of_active_eq hx hy
  intro i hi
  exact congrFun he ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

end
end Erdos539Geometry
