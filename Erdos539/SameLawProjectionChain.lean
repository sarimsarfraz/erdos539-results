/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProjectionDeletion
import Erdos539.FiniteDeletionChain
import Erdos539.CoordinateProfileExact

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*}
local instance sameLawProjectionChainDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The complete deletion chain within any starting mask, with its
quadruple and endpoint laws still projected from the same root. -/
theorem same_law_projection_chain_from_mask {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    {f : S → ℝ} (hf : ∑ x, f x ^ 2 = 1)
    (Q : StationaryAdditiveLaw S (fun x ↦ f x ^ 2))
    (J : Finset ι) {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J.card) :
    ∃ I ⊆ J, I.card = k ∧
      (Q.projectLaw J).energyProfile - Real.log (maxFan S) * Real.log ((J.card : ℝ) / k) -
        ((J.card : ℝ) - k) * (2 * Real.log (finiteEntropy (fun x ↦ f x ^ 2) / (k + 1 : ℕ) + 2) + 3) ≤
        (Q.projectLaw I).energyProfile := by
  let H := finiteEntropy (fun x ↦ f x ^ 2)
  let M := Real.log (maxFan S)
  let E := 2 * Real.log (H / (k + 1 : ℕ) + 2) + 3
  have hH : 0 ≤ H := finiteEntropy_nonneg _ (fun x ↦ sq_nonneg (f x)) hf
  have hM : 0 ≤ M := Real.log_nonneg (by exact_mod_cast one_le_maxFan hS)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hJpos : (0 : ℝ) < J.card := by exact_mod_cast (show 0 < J.card by omega)
  have hstep (K : Finset ι) (_hK : K ⊆ J) (hkc : k < K.card) :
      ∃ i ∈ K, (Q.projectLaw K).energyProfile - (Q.projectLaw (K.erase i)).energyProfile ≤
        M * (Real.log K.card - Real.log (K.erase i).card) + E := by
    have hKne : K.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hi, hdel⟩ := exists_projection_profile_deletion hS hf Q K hKne
    refine ⟨i, hi, ?_⟩
    have hcard := Finset.card_erase_of_mem hi
    have hlogdrop := inverse_le_log_card_drop (show 2 ≤ K.card by omega)
    rw [← hcard] at hlogdrop
    have hfirst := mul_le_mul_of_nonneg_left hlogdrop hM
    have hKpos : (0 : ℝ) < K.card := by exact_mod_cast hKne.card_pos
    have hkone : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hden : ((k + 1 : ℕ) : ℝ) ≤ K.card := by exact_mod_cast (show k + 1 ≤ K.card by omega)
    have harg : H / (K.card : ℝ) + 2 ≤ H / (k + 1 : ℕ) + 2 := by
      linarith [div_le_div_of_nonneg_left hH hkone hden]
    have hlog := Real.log_le_log (show 0 < H / (K.card : ℝ) + 2 by positivity) harg
    change (Q.projectLaw K).energyProfile - (Q.projectLaw (K.erase i)).energyProfile ≤
      M / K.card + 2 * Real.log (H / K.card + 2) + 3 at hdel
    dsimp [E]
    simp only [div_eq_mul_inv, one_mul] at hfirst hdel hlog ⊢
    linarith
  obtain ⟨I, hIJ, hI, hret⟩ := finite_deletion_chain (fun I ↦ (Q.projectLaw I).energyProfile)
    M E J k hkJ hstep
  refine ⟨I, hIJ, hI, ?_⟩
  rw [Real.log_div hJpos.ne' hkpos.ne']
  exact hret

/-- The manuscript's full same-reference-law projection chain, including
the actual square-root marginal energy upper endpoint. -/
theorem optimizer_same_law_projection_chain [Fintype ι]
    {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    {k : ℕ} (hk : 1 ≤ k) (hkd : k ≤ Fintype.card ι) :
    let Q := optimizerStationaryAdditiveLaw hS hf hE
    ∃ I : Finset ι, I.card = k ∧
      Real.log (energyNorm S) - Real.log (maxFan S) * Real.log ((Fintype.card ι : ℝ) / k) -
        ((Fintype.card ι : ℝ) - k) *
          (2 * Real.log (finiteEntropy (fun x ↦ f x ^ 2) / (k + 1 : ℕ) + 2) + 3) ≤
        (Q.projectLaw I).energyProfile ∧
      (Q.projectLaw I).energyProfile ≤ Real.log (actualMarginalEnergy S (extendWeight S f) I) := by
  let Q := optimizerStationaryAdditiveLaw hS hf hE
  obtain ⟨I, _, hI, hret⟩ := same_law_projection_chain_from_mask hS hf.2 Q Finset.univ hk
    (by simpa only [Finset.card_univ] using hkd)
  refine ⟨I, hI, ?_, Q.projected_entropy_le_log_actual hf.2 I⟩
  rw [Q.projectLaw_univ_energyProfile, optimizerStationaryAdditiveLaw_energyProfile hS hf hE,
    Finset.card_univ] at hret
  exact hret

end
end Erdos539Geometry
