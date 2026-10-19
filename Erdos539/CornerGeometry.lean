/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignMasks

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

/-- Coordinatewise membership in the closed box with two prescribed corners. -/
def InCornerBox (a b x : ι → ℝ) : Prop :=
  ∀ i, min (a i) (b i) ≤ x i ∧ x i ≤ max (a i) (b i)

def cornerSlice (S : Finset (ι → ℝ)) (a b : ι → ℝ) : Finset (ι → ℝ) :=
  S.filter (InCornerBox a b)

@[simp] theorem mem_cornerSlice {S : Finset (ι → ℝ)} {a b x : ι → ℝ} :
    x ∈ cornerSlice S a b ↔ x ∈ S ∧ InCornerBox a b x := Finset.mem_filter

theorem inCornerBox_left (a b : ι → ℝ) : InCornerBox a b a :=
  fun _ ↦ ⟨min_le_left _ _, le_max_left _ _⟩

theorem inCornerBox_right (a b : ι → ℝ) : InCornerBox a b b :=
  fun _ ↦ ⟨min_le_right _ _, le_max_right _ _⟩

theorem cornerSlice_subset (S : Finset (ι → ℝ)) (a b : ι → ℝ) : cornerSlice S a b ⊆ S :=
  Finset.filter_subset _ _

/-- A coordinate order in which precisely the coordinates in J are reversed. -/
def orientedLE (J : Finset ι) (x y : ι → ℝ) : Prop :=
  ∀ i, if i ∈ J then y i ≤ x i else x i ≤ y i

theorem orientedLE_antisymm {J : Finset ι} {x y : ι → ℝ}
    (hxy : orientedLE J x y) (hyx : orientedLE J y x) : x = y := by
  funext i
  have h := hxy i
  have h' := hyx i
  split_ifs at h h' <;> exact le_antisymm (by assumption) (by assumption)

theorem orientedLE_between {J : Finset ι} {x y z : ι → ℝ}
    (hxy : orientedLE J x y) (hyz : orientedLE J y z) : InCornerBox x z y := by
  intro i
  have h := hxy i
  have h' := hyz i
  split_ifs at h h'
  · exact ⟨(min_le_right _ _).trans h', h.trans (le_max_left _ _)⟩
  · exact ⟨(min_le_left _ _).trans h, h'.trans (le_max_right _ _)⟩

variable [Fintype ι]

/-- With one coordinate's direction fixed, every pair is comparable in some
remaining sign order. Ties require no perturbation or relabeling. -/
theorem exists_orientedLE (i : ι) {x y : ι → ℝ} (h : x i ≤ y i) :
    ∃ J ∈ (Finset.univ.erase i).powerset, orientedLE J x y := by
  let J := Finset.univ.filter (fun j ↦ y j < x j)
  refine ⟨J, Finset.mem_powerset.mpr ?_, ?_⟩
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro he
    subst j
    exact (not_lt_of_ge h) hj'
  · intro j
    by_cases hj : j ∈ J
    · simpa only [if_pos hj] using (Finset.mem_filter.mp hj).2.le
    · have hn : ¬ y j < x j := fun hlt ↦ hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
      simpa only [if_neg hj] using le_of_not_gt hn

/-- The predecessor profile is a subset of the 2^(d-1) sign orders. -/
def cornerPredecessorProfile (S : Finset (ι → ℝ)) (i : ι) (x : ι → ℝ) : Finset (Finset ι) :=
  (Finset.univ.erase i).powerset.filter (fun J ↦ ∃ y ∈ S, y ≠ x ∧ orientedLE J y x)

/-- The multidimensional monotone-triple bound, by binary predecessor profiles.
It covers coordinate ties directly. -/
theorem card_le_corner_independence_bound (S : Finset (ι → ℝ)) (i : ι)
    (hfree : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c → ¬ InCornerBox a c b) :
    S.card ≤ 2 ^ (2 ^ (Fintype.card ι - 1)) := by
  have distinguish {x y : ι → ℝ} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y)
      (hxy : x i ≤ y i) : cornerPredecessorProfile S i x ≠ cornerPredecessorProfile S i y := by
    obtain ⟨J, hJ, hle⟩ := exists_orientedLE i hxy
    have hmem : J ∈ cornerPredecessorProfile S i y :=
      Finset.mem_filter.mpr ⟨hJ, x, hx, hne, hle⟩
    intro he
    rw [← he] at hmem
    obtain ⟨z, hz, hzx, hzle⟩ := (Finset.mem_filter.mp hmem).2
    have hzy : z ≠ y := by
      intro hzy
      subst z
      exact hne (orientedLE_antisymm hle hzle)
    exact hfree z hz x hx y hy hzx hne hzy (orientedLE_between hzle hle)
  have hinj : (S : Set (ι → ℝ)).InjOn (cornerPredecessorProfile S i) := by
    intro x hx y hy he
    by_contra hne
    rcases le_total (x i) (y i) with hxy | hyx
    · exact distinguish hx hy hne hxy he
    · exact distinguish hy hx (Ne.symm hne) hyx he.symm
  have hsub : S.image (cornerPredecessorProfile S i) ⊆ ((Finset.univ.erase i).powerset).powerset := by
    intro P hP
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hP
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hc
  simpa only [Finset.card_powerset, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] using hc

theorem exists_corner_triple_of_large (S : Finset (ι → ℝ)) (i : ι)
    (hlarge : 2 ^ (2 ^ (Fintype.card ι - 1)) < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ InCornerBox a c b := by
  by_contra h
  have hf : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c → ¬ InCornerBox a c b := by
    intro a ha b hb c hc hab hbc hac hbox
    exact h ⟨a, ha, b, hb, c, hc, hab, hbc, hac, hbox⟩
  exact (not_lt_of_ge (card_le_corner_independence_bound S i hf)) hlarge

end
end Erdos539Geometry
