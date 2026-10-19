/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.OrthantTrimming

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*} [Fintype ι]

/-- Trimming in reverse order allows surviving points to be expanded forward. -/
def trimCoordinates (F : Finset (ι → ℝ)) (k : ι → ℕ) : List ι → Finset (ι → ℝ)
  | [] => F
  | i :: is => trimCoordinate (trimCoordinates F k is) i (k i)

theorem trimCoordinates_subset (F : Finset (ι → ℝ)) (k : ι → ℕ) (is : List ι) :
    trimCoordinates F k is ⊆ F := by
  induction is with
  | nil => exact Finset.Subset.refl F
  | cons i is ih => exact (trimCoordinate_subset _ _ _).trans ih

/-- The total number removed is bounded by the sum of the parent fiber budgets. -/
theorem trimCoordinates_card_budget (F : Finset (ι → ℝ)) (k : ι → ℕ) (is : List ι) :
    F.card ≤ (trimCoordinates F k is).card +
      (is.map (fun i ↦ k i * (F.image (lineProjection i)).card)).sum := by
  induction is with
  | nil => simp only [trimCoordinates, List.map_nil, List.sum_nil, Nat.add_zero, le_refl]
  | cons i is ih =>
    have h := trimCoordinate_removal_bound (trimCoordinates_subset F k is) i (k i)
    simp only [trimCoordinates, List.map_cons, List.sum_cons]
    omega

/-- Every surviving point expands into a product-sized family above it. Each
coordinate is changed once, so the branches stay disjoint. -/
theorem trimCoordinates_expansion (F : Finset (ι → ℝ)) (k : ι → ℕ)
    (is : List ι) (his : is.Nodup) {a : ι → ℝ} (ha : a ∈ trimCoordinates F k is) :
    ∃ G ⊆ F, (∀ x ∈ G, ∀ j, a j ≤ x j) ∧
      (∀ x ∈ G, ∀ j, j ∉ is → x j = a j) ∧
      (is.map (fun i ↦ k i + 1)).prod ≤ G.card := by
  classical
  induction is generalizing a with
  | nil =>
    refine ⟨{a}, Finset.singleton_subset_iff.mpr ha, ?_, ?_, ?_⟩
    · intro x hx j
      rw [Finset.mem_singleton.mp hx]
    · intro x hx j _hj
      rw [Finset.mem_singleton.mp hx]
    · simp
  | cons i is ih =>
    have hnot : i ∉ is := (List.nodup_cons.mp his).1
    have htail : is.Nodup := (List.nodup_cons.mp his).2
    have ha' := mem_trimCoordinate.mp ha
    let E := coordinateUpperTail (trimCoordinates F k is) i a
    have hsize : k i + 1 ≤ E.card := ha'.2
    have he (b : {b // b ∈ E}) :
        ∃ G ⊆ F, (∀ x ∈ G, ∀ j, b.val j ≤ x j) ∧
          (∀ x ∈ G, ∀ j, j ∉ is → x j = b.val j) ∧
          (is.map (fun j ↦ k j + 1)).prod ≤ G.card :=
      ih htail (mem_coordinateUpperTail.mp b.property).1
    choose G hGF hGa hGoff hGc using he
    let U := E.attach.biUnion G
    have hUF : U ⊆ F := by
      intro x hx
      obtain ⟨b, _hb, hx⟩ := Finset.mem_biUnion.mp hx
      exact hGF b hx
    have hdis : ∀ b ∈ E.attach, ∀ c ∈ E.attach, b ≠ c → Disjoint (G b) (G c) := by
      intro b _hb c _hc hbc
      apply Finset.disjoint_left.mpr
      intro x hxb hxc
      have hi : b.val i = c.val i := (hGoff b x hxb i hnot).symm.trans (hGoff c x hxc i hnot)
      have heq := coordinate_line_injective (mem_coordinateUpperTail.mp b.property).2.1
        (mem_coordinateUpperTail.mp c.property).2.1 hi
      exact hbc (Subtype.ext heq)
    have hUcard : U.card = ∑ b ∈ E.attach, (G b).card :=
      Finset.card_biUnion hdis
    refine ⟨U, hUF, ?_, ?_, ?_⟩
    · intro x hx j
      obtain ⟨b, _hb, hx⟩ := Finset.mem_biUnion.mp hx
      exact (coordinateUpperTail_above b.property j).trans (hGa b x hx j)
    · intro x hx j hj
      obtain ⟨b, _hb, hx⟩ := Finset.mem_biUnion.mp hx
      have hji : j ≠ i := fun h ↦ hj (by simp only [List.mem_cons, h, true_or])
      have hjtail : j ∉ is := fun h ↦ hj (List.mem_cons_of_mem i h)
      have hb := congrFun (mem_coordinateUpperTail.mp b.property).2.1 ⟨j, by simp [offCoordinate, hji]⟩
      exact (hGoff b x hx j hjtail).trans hb
    · rw [hUcard]
      simp only [List.map_cons, List.prod_cons]
      calc
        (k i + 1) * (is.map (fun j ↦ k j + 1)).prod ≤ E.card * (is.map (fun j ↦ k j + 1)).prod :=
          Nat.mul_le_mul_right _ hsize
        _ = ∑ _b ∈ E.attach, (is.map (fun j ↦ k j + 1)).prod := by simp
        _ ≤ ∑ b ∈ E.attach, (G b).card := Finset.sum_le_sum (fun b _ ↦ hGc b)

end
end Erdos539Geometry
