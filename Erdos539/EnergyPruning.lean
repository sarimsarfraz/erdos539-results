/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.AggregatePruning
import Erdos539.WeightRestriction

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*}
local instance energyPruningDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- Common-anchor pruning driven by actual energy retention. Both lower
bounds quantify over subsets of the same parent with their actual restricted
weights. No cardinality-density assumption is substituted for energy. -/
theorem energy_aggregate_pruning
    {A : Finset (ι → ℝ)} (w : (ι → ℝ) → ℝ) (hE : 0 < weightedEnergy A w)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    (K : Finset ι) (hKI : K ⊆ I) (hKJ : K ⊆ J)
    (ell mu : ℝ) (hell : 0 ≤ ell)
    (hfirst : ∀ B ⊆ A, weightedEnergy A w / 16 ≤ weightedEnergy B w → ell ≤ (maxRestrictedFan B J : ℝ))
    (hsecond : ∀ B ⊆ A, weightedEnergy A w / 16 ≤ weightedEnergy B w → mu ≤ (maxRestrictedFan B I : ℝ)) :
    ell * mu ≤ (maxRestrictedFan A K : ℝ) := by
  classical
  let bad := A.filter (fun a ↦ ((restrictedFan A J a).card : ℝ) < ell)
  have hbadsub : bad ⊆ A := Finset.filter_subset _ _
  have hbad : weightedEnergy bad w < weightedEnergy A w / 16 := by
    by_contra h
    have hh : weightedEnergy A w / 16 ≤ weightedEnergy bad w := le_of_not_gt h
    have hbne : bad.Nonempty := weightedEnergy_nonempty_of_pos ((by positivity : 0 < weightedEnergy A w / 16).trans_le hh)
    obtain ⟨a, ha, hmax⟩ := exists_max_restrictedFan hbne J
    have hlower := hfirst bad hbadsub hh
    rw [hmax] at hlower
    have hmono : (restrictedFan bad J a).card ≤ (restrictedFan A J a).card :=
      Finset.card_le_card (restrictedFan_mono hbadsub J a)
    have hbadpoint := (Finset.mem_filter.mp ha).2
    exact (not_lt_of_ge (hlower.trans (by exact_mod_cast hmono))) hbadpoint
  let G := A \ bad
  have hGsub : G ⊆ A := Finset.sdiff_subset
  have hGlarge : weightedEnergy A w / 16 ≤ weightedEnergy G w :=
    weightedEnergy_complement_retention hbadsub w hbad.le
  have hGne : G.Nonempty := weightedEnergy_nonempty_of_pos ((by positivity : 0 < weightedEnergy A w / 16).trans_le hGlarge)
  obtain ⟨a, ha, hmax⟩ := exists_max_restrictedFan hGne I
  let W := restrictedFan G I a
  have hW : mu ≤ (W.card : ℝ) := by
    have h := hsecond G hGsub hGlarge
    rwa [hmax] at h
  let r : (ι → ℝ) → (ι → ℝ) := fun w ↦
    if hw : w ∈ W then Classical.choose (mem_fan.mp hw) else a
  have hr (w : ι → ℝ) (hw : w ∈ W) : r w ∈ slice G I a ∧ pdiff (r w) a = w := by
    dsimp only [r]
    rw [dif_pos hw]
    exact Classical.choose_spec (mem_fan.mp hw)
  have hrA (w : ι → ℝ) (hw : w ∈ W) : r w ∈ slice A I a ∧ pdiff (r w) a = w :=
    ⟨slice_mono hGsub I a (hr w hw).1, (hr w hw).2⟩
  have hgood (w : ι → ℝ) (hw : w ∈ W) : ell ≤ ((restrictedFan A J (r w)).card : ℝ) := by
    have hg : r w ∈ G := (mem_slice.mp (hr w hw).1).1
    obtain ⟨hin, hnot⟩ := Finset.mem_sdiff.mp hg
    exact le_of_not_gt (fun h ↦ hnot (Finset.mem_filter.mpr ⟨hin, h⟩))
  have hlift := sum_card_restrictedFan_le_restrictedFan A I J hcover K hKI hKJ a W r hrA
  calc
    ell * mu ≤ ell * (W.card : ℝ) := mul_le_mul_of_nonneg_left hW hell
    _ = ∑ _w ∈ W, ell := by simp [mul_comm]
    _ ≤ ∑ w ∈ W, ((restrictedFan A J (r w)).card : ℝ) := Finset.sum_le_sum hgood
    _ ≤ ((restrictedFan A K a).card : ℝ) := by
      simpa only [Nat.cast_sum] using (Nat.cast_le (α := ℝ)).mpr hlift
    _ ≤ (maxRestrictedFan A K : ℝ) := by exact_mod_cast card_restrictedFan_le_max K (hGsub ha)


end
end Erdos539Geometry
