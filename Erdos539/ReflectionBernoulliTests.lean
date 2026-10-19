/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteOverlapColoring
import Erdos539.ColoredBernoulliTail

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance reflectionBernoulliIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _
local instance reflectionBernoulliIndexDecidableEq (I : Finset ℤ) : DecidableEq I := Classical.decEq _
local instance reflectionBernoulliSampleDecidableEq (I : Finset ℤ) : DecidableEq (I → Bool) := Classical.decEq _

def goodReflectionTests (I : Finset ℤ) (w z : ℤ) : Finset ℤ :=
  I.filter (fun x ↦ (∀ i : Fin 4, reflectionTestSite w z x i ∈ I) ∧
    Function.Injective (reflectionTestSite w z x))

/-- The literal four-site block, now viewed inside the finite sampling domain. -/
def reflectionSiteBlock (I : Finset ℤ) (w z x : ℤ) : Finset I :=
  I.attach.filter (fun a ↦ a.val ∈ reflectionTestSites w z x)

theorem reflectionSiteBlock_card {I : Finset ℤ} {w z x : ℤ} (hx : x ∈ goodReflectionTests I w z) :
    (reflectionSiteBlock I w z x).card = 4 := by
  obtain ⟨_, hall, hinj⟩ := Finset.mem_filter.mp hx
  have he : (reflectionSiteBlock I w z x).card = (reflectionTestSites w z x).card := by
    apply Finset.card_bij (fun a _ ↦ a.val)
    · intro a ha
      exact (Finset.mem_filter.mp ha).2
    · intro a _ b _ he
      exact Subtype.ext he
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      refine ⟨⟨reflectionTestSite w z x i, hall i⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  rw [he, reflectionTestSites, Finset.card_image_of_injective _ hinj]
  decide

theorem reflectionSiteBlock_disjoint (I : Finset ℤ) {w z x y : ℤ}
    (h : Disjoint (reflectionTestSites w z x) (reflectionTestSites w z y)) :
    Disjoint (reflectionSiteBlock I w z x) (reflectionSiteBlock I w z y) := by
  apply Finset.disjoint_left.mpr
  intro a hax hay
  exact Finset.disjoint_left.mp h (Finset.mem_filter.mp hax).2 (Finset.mem_filter.mp hay).2

/-- Number of successful nonexceptional reflected-representation tests under
the actual independent Boolean sampling of the integer support. -/
def reflectionGoodCount (I : Finset ℤ) (w z : ℤ) (ω : I → Bool) : ℝ :=
  ∑ x : goodReflectionTests I w z, bernoulliAll (reflectionSiteBlock I w z x.val) ω

theorem reflectionGoodCount_tail (I : Finset ℤ) (w z : ℤ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    (∑ ω ∈ Finset.univ.filter (fun ω ↦ 2 * (α ^ 4 * I.card) ≤ reflectionGoodCount I w z ω),
      finiteBernoulliWeight α ω) ≤ Real.exp (-(α ^ 4 * I.card) / 48) := by
  let D := goodReflectionTests I w z
  obtain ⟨c, hc, hdisj⟩ := reflectionTest_sixteen_coloring D w z
  let col : D → Fin 16 := fun x ↦ ⟨c x.val, hc x.val x.property⟩
  have hn : ((Finset.univ : Finset D).card : ℝ) ≤ I.card := by
    simp only [Finset.card_univ, Fintype.card_coe]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _ : D ⊆ I)
  have hd : ∀ x ∈ (Finset.univ : Finset D), ∀ y ∈ (Finset.univ : Finset D), x ≠ y →
      col x = col y → Disjoint (reflectionSiteBlock I w z x.val) (reflectionSiteBlock I w z y.val) := by
    intro x _ y _ hxy he
    apply reflectionSiteBlock_disjoint I
    apply hdisj x.val x.property y.val y.property
    · exact fun h ↦ hxy (Subtype.ext h)
    · exact congrArg (fun j : Fin 16 ↦ j.val) he
  exact colored_bernoulli_four_site_tail hα hα1 (Nat.cast_nonneg _) Finset.univ
    (fun x : D ↦ reflectionSiteBlock I w z x.val) col
    (fun x _ ↦ reflectionSiteBlock_card x.property) hn hd

end
end Erdos539Geometry
