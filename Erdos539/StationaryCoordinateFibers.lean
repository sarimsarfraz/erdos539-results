/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryReferenceState
import Erdos539.MaskedEnergy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*}
local instance fixedCoordinateDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace StationaryReferenceState

def FixedOutside (s : StationaryReferenceState (ι → ℝ)) (B : Finset ι) : Prop :=
  ∀ x ∈ s.support, ∀ y ∈ s.support, ∀ i ∉ B, x i = y i

/-- The entire original outside-coordinate fiber is present, with its
original point labels. This is stronger than having constant outside coordinates. -/
def FullOutsideFiber (root s : StationaryReferenceState (ι → ℝ)) (B : Finset ι) : Prop :=
  s.support ⊆ root.support ∧ ∀ a ∈ s.support, ∀ x,
    x ∈ s.support ↔ x ∈ root.support ∧ ∀ i ∉ B, x i = a i

theorem fullOutsideFiber_self (s : StationaryReferenceState (ι → ℝ)) (B : Finset ι)
    (h : s.FixedOutside B) : s.FullOutsideFiber s B := by
  refine ⟨Finset.Subset.refl _, ?_⟩
  intro a ha x
  exact ⟨fun hx ↦ ⟨hx, h x hx a ha⟩, fun hx ↦ hx.1⟩

theorem FullOutsideFiber.fixedOutside {root s : StationaryReferenceState (ι → ℝ)} {B : Finset ι}
    (h : root.FullOutsideFiber s B) : s.FixedOutside B := by
  intro x hx a ha
  exact ((h.2 a ha x).mp hx).2

theorem fiber_fullOutside {root s : StationaryReferenceState (ι → ℝ)} {B : Finset ι}
    (h : root.FullOutsideFiber s B) (I : Finset ι) (y : s.support.image (maskCoordinatesHom I)) :
    root.FullOutsideFiber (s.fiber (maskCoordinatesHom I) y) (B \ I) := by
  refine ⟨fun x hx ↦ h.1 (mem_fiber.mp hx).1, ?_⟩
  intro a ha x
  have ha' := mem_fiber.mp ha
  constructor
  · intro hx
    have hx' := mem_fiber.mp hx
    refine ⟨h.1 hx'.1, ?_⟩
    intro i hi
    by_cases hiI : i ∈ I
    · have he := congrFun (hx'.2.trans ha'.2.symm) i
      simpa only [maskCoordinatesHom, maskCoordinates, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_pos hiI] using he
    · exact h.fixedOutside x hx'.1 a ha'.1 i (fun hiB ↦ hi (Finset.mem_sdiff.mpr ⟨hiB, hiI⟩))
  · rintro ⟨hx, he⟩
    have hxs : x ∈ s.support := (h.2 a ha'.1 x).mpr ⟨hx, fun i hi ↦
      he i (fun hm ↦ hi (Finset.mem_sdiff.mp hm).1)⟩
    apply mem_fiber.mpr
    refine ⟨hxs, ?_⟩
    apply Eq.trans _ ha'.2
    ext i
    change maskCoordinates I x i = maskCoordinates I a i
    by_cases hiI : i ∈ I
    · simp only [maskCoordinates, if_pos hiI]
      exact he i (fun hm ↦ (Finset.mem_sdiff.mp hm).2 hiI)
    · simp only [maskCoordinates, if_neg hiI]

end StationaryReferenceState
end
end Erdos539Geometry
