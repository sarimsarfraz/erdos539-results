/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsRecursionBudget
import Erdos539.MaskedEnergy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*}
local instance coordinateReferenceDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace GibbsReference

/-- Coordinates outside the current physical mask are constant on the
support. Fiber constants are retained, not reset or identified. -/
def FixedOutside (s : GibbsReference (ι → ℝ)) (B : Finset ι) : Prop :=
  ∀ x ∈ s.support, ∀ y ∈ s.support, ∀ i ∉ B, x i = y i

theorem image_fixedOutside (s : GibbsReference (ι → ℝ)) (I : Finset ι) :
    (s.image (maskCoordinatesHom I)).FixedOutside I := by
  intro x hx y hy i hi
  change x ∈ maskedProjection s.support I at hx
  change y ∈ maskedProjection s.support I at hy
  rw [maskedProjection_zero_outside hx hi, maskedProjection_zero_outside hy hi]

theorem fiber_fixedOutside (s : GibbsReference (ι → ℝ)) (B I : Finset ι)
    (hfixed : s.FixedOutside B) (y : s.support.image (maskCoordinatesHom I)) :
    (s.fiber (maskCoordinatesHom I) y).FixedOutside (B \ I) := by
  intro x hx z hz i hi
  have hx' := mem_fiber.mp hx
  have hz' := mem_fiber.mp hz
  by_cases hiI : i ∈ I
  · have he := congrFun (hx'.2.trans hz'.2.symm) i
    change maskCoordinates I x i = maskCoordinates I z i at he
    simpa only [maskCoordinates, if_pos hiI] using he
  · exact hfixed x hx'.1 z hz'.1 i (fun hiB ↦ hi (Finset.mem_sdiff.mpr ⟨hiB, hiI⟩))

end GibbsReference

namespace GibbsRecursion

def leafCount {G : Type*} [AddCommGroup G] [DecidableEq G] :
    {s : GibbsReference G} → (t : GibbsRecursion s) → t.Outcome → ℕ
  | _, .leaf _, _ => 1
  | _, .cut _ _ p f, x => p.leafCount x.1 + (f x.2.1).leafCount x.2.2

def leafStates {G : Type*} [AddCommGroup G] [DecidableEq G] :
    {s : GibbsReference G} → (t : GibbsRecursion s) → t.Outcome → List (GibbsReference G)
  | _, .leaf s, _ => [s]
  | _, .cut _ _ p f, x => p.leafStates x.1 ++ (f x.2.1).leafStates x.2.2

/-- Every cut is a proper partition of the current physical mask, and
every terminal support has just one allowed free physical coordinate.
Different fibers may have different continued cuts. -/
inductive IsCoordinate : (B : Finset ι) → {s : GibbsReference (ι → ℝ)} → GibbsRecursion s → Prop
  | leaf (s : GibbsReference (ι → ℝ)) (B : Finset ι) (hcard : B.card = 1)
      (hfixed : s.FixedOutside B) : IsCoordinate B (.leaf s)
  | cut (s : GibbsReference (ι → ℝ)) (B I : Finset ι)
      (hI : I ⊆ B) (hi : I.Nonempty) (hj : (B \ I).Nonempty) (hfixed : s.FixedOutside B)
      (p : GibbsRecursion (s.image (maskCoordinatesHom I)))
      (f : (y : s.support.image (maskCoordinatesHom I)) → GibbsRecursion (s.fiber (maskCoordinatesHom I) y))
      (hp : IsCoordinate I p) (hf : ∀ y, IsCoordinate (B \ I) (f y)) :
        IsCoordinate B (.cut s (maskCoordinatesHom I) p f)

theorem IsCoordinate.leafCount_eq {s : GibbsReference (ι → ℝ)} {B : Finset ι}
    {t : GibbsRecursion s} (h : IsCoordinate B t) (x : t.Outcome) : t.leafCount x = B.card := by
  induction h with
  | leaf s B hcard _ => exact hcard.symm
  | cut s B I hI _ _ _ p f _ _ ihp ihf =>
    change p.leafCount x.1 + (f x.2.1).leafCount x.2.2 = B.card
    rw [ihp, ihf]
    simpa only [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hI

theorem IsCoordinate.leaf_scalar {s : GibbsReference (ι → ℝ)} {B : Finset ι}
    {t : GibbsRecursion s} (h : IsCoordinate B t) (x : t.Outcome) :
    ∀ r ∈ t.leafStates x, ∃ i ∈ B, r.FixedOutside {i} := by
  induction h with
  | leaf s B hcard hfixed =>
    intro r hr
    have he : r = s := List.mem_singleton.mp hr
    subst r
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    exact ⟨i, hi ▸ Finset.mem_singleton_self i, hi ▸ hfixed⟩
  | cut s B I hI _ _ _ p f _ _ ihp ihf =>
    intro r hr
    rcases List.mem_append.mp hr with hl | hr
    · obtain ⟨i, hi, hs⟩ := ihp x.1 r hl
      exact ⟨i, hI hi, hs⟩
    · obtain ⟨i, hi, hs⟩ := ihf x.2.1 x.2.2 r hr
      exact ⟨i, (Finset.mem_sdiff.mp hi).1, hs⟩

end GibbsRecursion
end
end Erdos539Geometry
