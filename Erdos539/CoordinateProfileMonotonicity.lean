/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryLawComposition

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*}
local instance coordinateProfileMonotonicityDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- Actual restriction between two nested coordinate images. -/
def restrictProjectedEndpoint (S : Finset (ι → ℝ)) {I J : Finset ι} (hJI : J ⊆ I)
    (v : projection S I) : projection S J :=
  ⟨fun j ↦ v.val ⟨j.val, hJI j.property⟩, by
    have hv := v.property
    simp only [projection, Finset.mem_image] at hv ⊢
    obtain ⟨x, hx, he⟩ := hv
    refine ⟨x, hx, ?_⟩
    funext j
    exact congrFun he ⟨j.val, hJI j.property⟩⟩

theorem restrictProjectedEndpoint_preserves_additive (S : Finset (ι → ℝ))
    {I J : Finset ι} (hJI : J ⊆ I) (a b c d : projection S I)
    (h : a.val + b.val = c.val + d.val) :
    (restrictProjectedEndpoint S hJI a).val + (restrictProjectedEndpoint S hJI b).val =
      (restrictProjectedEndpoint S hJI c).val + (restrictProjectedEndpoint S hJI d).val := by
  funext j
  exact congrFun h ⟨j.val, hJI j.property⟩

theorem restrictProjectedEndpoint_comp (S : Finset (ι → ℝ))
    {I J : Finset ι} (hJI : J ⊆ I) :
    restrictProjectedEndpoint S hJI ∘ projectEndpoint S I = projectEndpoint S J := rfl

namespace StationaryAdditiveLaw
variable {S : Finset (ι → ℝ)} {f : S → ℝ}

/-- The literal k(I) profile is monotone under inclusion of coordinate
masks, with every projected law still coming from the one root law. -/
theorem projectLaw_correlation_mono (Q : StationaryAdditiveLaw S (fun x ↦ f x ^ 2))
    {I J : Finset ι} (hJI : J ⊆ I) :
    (Q.projectLaw J).correlation ≤ (Q.projectLaw I).correlation := by
  have h := (Q.projectLaw I).correlation_map_le
    (finitePush_nonneg _ _ (fun x ↦ sq_nonneg (f x)))
    (restrictProjectedEndpoint S hJI) (restrictProjectedEndpoint_preserves_additive S hJI)
  have he := Q.correlation_map_comp (projectEndpoint S I) (restrictProjectedEndpoint S hJI)
    (projectEndpoint_preserves_additive S I) (restrictProjectedEndpoint_preserves_additive S hJI)
  change ((Q.projectLaw I).map (restrictProjectedEndpoint S hJI)
    (restrictProjectedEndpoint_preserves_additive S hJI)).correlation = (Q.projectLaw J).correlation at he
  rw [he] at h
  exact h

/-- Deleting coordinates loses at most the corresponding conditional
entropy, in the root-referenced energy profile. -/
theorem projectLaw_energyProfile_loss_le (Q : StationaryAdditiveLaw S (fun x ↦ f x ^ 2))
    {I J : Finset ι} (hJI : J ⊆ I) :
    (Q.projectLaw I).energyProfile - (Q.projectLaw J).energyProfile ≤
      finiteEntropy (finitePush (fun x ↦ f x ^ 2) (projectEndpoint S I)) -
        finiteEntropy (finitePush (fun x ↦ f x ^ 2) (projectEndpoint S J)) := by
  have h := Q.projectLaw_correlation_mono hJI
  rw [energyProfile_eq_entropy_sub_correlation, energyProfile_eq_entropy_sub_correlation]
  linarith

end StationaryAdditiveLaw
end
end Erdos539Geometry
