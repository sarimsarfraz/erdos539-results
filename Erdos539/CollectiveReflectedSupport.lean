/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CollectiveFiberBudgets
import Erdos539.PopularReflectedSupport

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
local instance collectiveReflectedImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

/-- Each original fiber has its own actual popular sum center. -/
def collectiveReflectedCenter (S : Finset G) (φ : G →+ H) (y : S.image φ) : G :=
  popularReflectedCenter (fiber S φ y.val) (imageFiber_nonempty S φ y)

def collectiveReflectedFiber (S : Finset G) (φ : G →+ H) (y : S.image φ) : Finset G :=
  reflectedSupport (fiber S φ y.val) (collectiveReflectedCenter S φ y)

theorem collectiveReflectedFiber_subset (S : Finset G) (φ : G →+ H) (y : S.image φ) :
    collectiveReflectedFiber S φ y ⊆ fiber S φ y.val := Finset.filter_subset _ _

/-- A subset of the original parent, with the original fiber labels.
No between-fiber translation or reflected replacement of the parent occurs. -/
def collectiveReflectedSubset (S : Finset G) (φ : G →+ H) : Finset G :=
  Finset.univ.biUnion (collectiveReflectedFiber S φ)

theorem collectiveReflectedSubset_subset (S : Finset G) (φ : G →+ H) :
    collectiveReflectedSubset S φ ⊆ S := by
  intro x hx
  obtain ⟨y, _, hy⟩ := Finset.mem_biUnion.mp hx
  exact (mem_fiber.mp (collectiveReflectedFiber_subset S φ y hy)).1

theorem collectiveReflectedSubset_fiber (S : Finset G) (φ : G →+ H) (y : S.image φ) :
    fiber (collectiveReflectedSubset S φ) φ y.val = collectiveReflectedFiber S φ y := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hxy⟩ := mem_fiber.mp hx
    obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.mp hx
    have hxz := (mem_fiber.mp (collectiveReflectedFiber_subset S φ z hz)).2
    have he : z = y := Subtype.ext (hxz.symm.trans hxy)
    simpa only [he] using hz
  · intro hx
    exact mem_fiber.mpr ⟨Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, hx⟩,
      (mem_fiber.mp (collectiveReflectedFiber_subset S φ y hx)).2⟩

theorem collectiveReflectedSubset_card (S : Finset G) (φ : G →+ H) :
    (collectiveReflectedSubset S φ).card = ∑ y : S.image φ, (collectiveReflectedFiber S φ y).card := by
  apply Finset.card_biUnion
  intro y _ z _ hyz
  apply Finset.disjoint_left.mpr
  intro x hy hz
  have hxy := (mem_fiber.mp (collectiveReflectedFiber_subset S φ y hy)).2
  have hxz := (mem_fiber.mp (collectiveReflectedFiber_subset S φ z hz)).2
  exact hyz (Subtype.ext (hxy.symm.trans hxz))

/-- The actual retained subset has size at least N/K before a common
sign cell is selected, improving the older N/K^2 loss. -/
theorem collectiveReflectedSubset_card_lower {S : Finset G} (hS : S.Nonempty) (φ : G →+ H) :
    (S.card : ℝ) ^ 2 / (S - S).card ≤ (collectiveReflectedSubset S φ).card := by
  have h := collective_fiber_inverse_energy hS φ
  rw [collectiveReflectedSubset_card, Nat.cast_sum]
  apply h.trans
  apply Finset.sum_le_sum
  intro y _
  exact popularReflectedCenter_bound (fiber S φ y.val) (imageFiber_nonempty S φ y)

end
end Erdos539Geometry
