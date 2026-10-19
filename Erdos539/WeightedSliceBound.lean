/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinateFiberEnergy
import Erdos539.WeightRestriction
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*}
local instance weightedSliceBoundDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- A positive-energy parent has positive energy in each actual square-root
marginal. This follows from the finite fiber estimate, with no extra balance
assumption. -/
theorem coordinateMarginalEnergy_pos {A : Finset (ι → ℝ)} (w : (ι → ℝ) → ℝ)
    (hw : ∀ x ∈ A, 0 ≤ w x) (hE : 0 < weightedEnergy A w)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J) :
    0 < coordinateMarginalEnergy A w I J := by
  have hA := weightedEnergy_nonempty_of_pos hE
  have hprojA : (projection A I).Nonempty := by
    obtain ⟨x, hx⟩ := hA
    refine ⟨project I x, ?_⟩
    simp only [projection, Finset.mem_image]
    exact ⟨x, hx, rfl⟩
  obtain ⟨v, _hv, hmax⟩ := (projection A I).exists_max_image
    (fun v ↦ energyNorm (projection (fiber A (project I) v) J)) hprojA
  have hM := energyNorm_nonneg (projection (fiber A (project I) v) J)
  have h := coordinate_fiber_energy_bound (Finset.Subset.refl A) w hw I J hcover hM hmax
  by_contra hn
  have hnonpos : coordinateMarginalEnergy A w I J ≤ 0 := le_of_not_gt hn
  have hm := mul_nonpos_of_nonneg_of_nonpos hM hnonpos
  linarith

/-- A retained-energy subset has a large restricted fan whenever every
nonempty lower-dimensional support has the stated energy-norm fan bound. -/
theorem weighted_restricted_fan_lower_bound {A B : Finset (ι → ℝ)} (hBA : B ⊆ A)
    (w : (ι → ℝ) → ℝ) (hw : ∀ x ∈ A, 0 ≤ w x) (hE : 0 < weightedEnergy A w)
    (hBenergy : weightedEnergy A w / 16 ≤ weightedEnergy B w)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    {c a : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hfan : ∀ F : Finset (J → ℝ), F.Nonempty → c * energyNorm F ^ a ≤ (maxFan F : ℝ)) :
    c * (weightedEnergy A w / (16 * coordinateMarginalEnergy A w I J)) ^ a ≤
      (maxRestrictedFan B I : ℝ) := by
  have hA := weightedEnergy_nonempty_of_pos hE
  have hL := coordinateMarginalEnergy_pos w hw hE I J hcover
  have hprojA : (projection A I).Nonempty := by
    obtain ⟨x, hx⟩ := hA
    refine ⟨project I x, ?_⟩
    simp only [projection, Finset.mem_image]
    exact ⟨x, hx, rfl⟩
  obtain ⟨v, _hv, hmax⟩ := (projection A I).exists_max_image
    (fun v ↦ energyNorm (projection (fiber B (project I) v) J)) hprojA
  let F := projection (fiber B (project I) v) J
  have hM := energyNorm_nonneg F
  have hbound := coordinate_fiber_energy_bound hBA w hw I J hcover hM hmax
  have hratio : weightedEnergy A w / (16 * coordinateMarginalEnergy A w I J) ≤ energyNorm F := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * coordinateMarginalEnergy A w I J)).mpr
    nlinarith
  have hMpos : 0 < energyNorm F := (div_pos hE (by positivity)).trans_le hratio
  have hF : F.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, energyNorm_empty] at hMpos
    exact (lt_irrefl 0) hMpos
  have hfl := hfan F hF
  have hp := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hratio ha) hc
  have hmain := hp.trans hfl
  obtain ⟨u, hu⟩ := hF
  have hu' : ∃ x ∈ fiber B (project I) v, project J x = u := by
    simpa only [F, projection, Finset.mem_image] using hu
  obtain ⟨x, hx, _hxu⟩ := hu' 
  have he : fiber B (project I) v = slice B I x := by
    dsimp only [slice]
    rw [(mem_fiber.mp hx).2]
  have hgeom := maxFan_projection_slice_le B I J x
  rw [← he] at hgeom
  exact hmain.trans (by exact_mod_cast hgeom)

end
end Erdos539Geometry
