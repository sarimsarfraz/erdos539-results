/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.NestedProjectionEntropy
import Erdos539.StationarySweepLog

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*}
local instance projectionDeletionIndexDecidableEq {κ : Type*} (J : Finset κ) :
    DecidableEq J := Classical.decEq _
local instance projectionDeletionDecidableEq {κ : Type*} : DecidableEq (κ → ℝ) := Classical.decEq _
local instance projectionDeletionProjectionDecidableEq {κ : Type*}
    (S : Finset (κ → ℝ)) (I : Finset κ) : DecidableEq (projection S I) := Classical.decEq _

/-- One deletion from any original coordinate mask, still referenced to
one root law. The cost uses the root entropy and root maximum fan. -/
theorem exists_projection_profile_deletion {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    {f : S → ℝ} (hf : ∑ x, f x ^ 2 = 1)
    (Q : StationaryAdditiveLaw S (fun x ↦ f x ^ 2))
    (J : Finset ι) (hJ : J.Nonempty) :
    ∃ i ∈ J, (Q.projectLaw J).energyProfile - (Q.projectLaw (J.erase i)).energyProfile ≤
      Real.log (maxFan S) / J.card +
        2 * Real.log (finiteEntropy (fun x ↦ f x ^ 2) / J.card + 2) + 3 := by
  let ν := fun x ↦ f x ^ 2
  let η := finitePush ν (projectEndpoint S J)
  have hν : ∀ x, 0 ≤ ν x := fun x ↦ sq_nonneg (f x)
  have hη : ∀ x, 0 ≤ η x := finitePush_nonneg ν _ hν
  have hηsum : ∑ x, η x = 1 := by rw [finitePush_sum]; exact hf
  have hm : (0 : ℝ) < J.card := by exact_mod_cast hJ.card_pos
  have hPJ : (projection S J).Nonempty := by
    obtain ⟨a, ha⟩ := hS
    exact ⟨(projectEndpoint S J ⟨a, ha⟩).val, (projectEndpoint S J ⟨a, ha⟩).property⟩
  have hfan : maxFan (projection S J) ≤ maxFan S := by
    have h := maxFan_projection_slice_le S ∅ J 0
    simpa only [slice_empty, maxRestrictedFan_empty] using h
  have hfanpos : (0 : ℝ) < maxFan (projection S J) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_maxFan hPJ))
  have hcap := stationaryFanCapacity_le_log_maxFan (projection S J) η hη hηsum
  have hlogfan := Real.log_le_log hfanpos (show (maxFan (projection S J) : ℝ) ≤ maxFan S by exact_mod_cast hfan)
  have hentropy := finiteEntropy_push_le ν (projectEndpoint S J) hν
  have hηH : 0 ≤ finiteEntropy η := finiteEntropy_nonneg η hη hηsum
  have harg : finiteEntropy η / (J.card : ℝ) + 2 ≤ finiteEntropy ν / J.card + 2 := by
    linarith [div_le_div_of_nonneg_right hentropy hm.le]
  have hlog := Real.log_le_log (show 0 < finiteEntropy η / (J.card : ℝ) + 2 by positivity) harg
  have hlogmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * (J.card : ℝ) by positivity)
  have hsweep := stationary_sweep_log_bound (projection S J) η hη hηsum
  simp only [Fintype.card_coe] at hsweep
  let C := Real.log (maxFan S) / J.card + 2 * Real.log (finiteEntropy ν / J.card + 2) + 3
  have halg : (J.card : ℝ) * C = Real.log (maxFan S) +
      2 * (J.card : ℝ) * Real.log (finiteEntropy ν / J.card + 2) + 3 * J.card := by
    dsimp [C]
    field_simp
  have hsum : (∑ i : J, coordinateConditionalEntropy (projection S J) η i) ≤ ∑ _i : J, C := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, halg]
    linarith
  obtain ⟨j, hj⟩ := hJ
  have hne : (Finset.univ : Finset J).Nonempty := ⟨⟨j, hj⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le hne hsum
  refine ⟨i.val, i.property, ?_⟩
  have hloss := Q.projectLaw_energyProfile_loss_le (Finset.erase_subset i.val J)
  have hid := projected_coordinateConditionalEntropy S ν hν J i
  change coordinateConditionalEntropy (projection S J) η i = _ at hid
  change (Q.projectLaw J).energyProfile - (Q.projectLaw (J.erase i.val)).energyProfile ≤
    coordinateProjectionEntropy S ν J - coordinateProjectionEntropy S ν (J.erase i.val) at hloss
  rw [← hid] at hloss
  exact hloss.trans hi

end
end Erdos539Geometry
