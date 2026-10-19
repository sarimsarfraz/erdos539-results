/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsPureComponents
import Erdos539.UniformEnergyWeight
import Erdos539.SharpSeparatedExponents

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators Pointwise
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]
local instance pureRetentionFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance pureRetentionImageDecidableEq (s : GibbsReference G) (n : ℕ) (label : G → Fin n) :
    DecidableEq (s.support.image label) := Classical.decEq _

theorem log_energyNorm_ge_uniform_reference {S : Finset G} (hS : S.Nonempty) :
    Real.log (S.card : ℝ) - referenceDeficit S (uniformReference S) ≤ Real.log (energyNorm S) := by
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hE := countingEnergy_pos hS
  have h := energyNorm_ge_admissible (uniformEnergyWeight_admissible hS)
  rw [uniformEnergyWeight_energy] at h
  have hl := Real.log_le_log (div_pos hE (pow_pos hN 2)) h
  rw [Real.log_div hE.ne' (pow_pos hN 2).ne', Real.log_pow] at hl
  rw [referenceDeficit_uniform hS, Real.log_div (pow_pos hN 3).ne' hE.ne', Real.log_pow]
  norm_num only [Nat.cast_ofNat] at hl ⊢
  linarith

namespace GibbsReference

theorem componentCharge_ge_log_mass (s : GibbsReference G) (n : ℕ) (label : G → Fin n)
    (i : s.support.image label) :
    (3 - sharpSidonExponent) * (-Real.log (finitePush s.weight (imageEndpoint s.support label) i)) ≤
      s.componentCharge label i := by
  have hγ : 0 ≤ sharpSidonExponent := le_trans (by norm_num) sharpSidonExponent_bounds.1
  have hη := imageFiberReference_pos s.support label (referenceEndpoint s.support s.weight)
    (referenceEndpoint_pos s.nonempty s.positive) i
  have hν := referenceEndpoint_pos (imageFiber_nonempty s.support label i)
    (imageFiberReference_pos s.support label s.weight s.positive i)
  have hd : 0 ≤ fiberEndpointDrift s.support label s.weight i :=
    finiteRelEntropy_nonneg _ _ (fun x ↦ (hη x).le) (fun x ↦ (hν x).le)
      (imageFiberReference_sum s.support label (referenceEndpoint s.support s.weight)
        (referenceEndpoint_pos s.nonempty s.positive) i)
      (referenceEndpoint_sum (imageFiber_nonempty s.support label i)
        (imageFiberReference_pos s.support label s.weight s.positive i)) (fun x _ ↦ hν x)
  have hv := mul_nonneg hγ (labelReferenceDivergence_nonneg s.nonempty label s.weight s.positive s.normalized)
  unfold componentCharge
  linarith

end GibbsReference

namespace GibbsInterleavedRecursion

theorem pure_cost_lower_bound
    (charge : (s : GibbsReference G) → (φ : G →+ G) → s.support.image φ → ℝ)
    {s : GibbsReference G} (t : GibbsInterleavedRecursion s) (hp : t.IsPure) (x : t.Outcome) :
    (3 - sharpSidonExponent) * t.logMassCost hp x + (t.selectedLeaf hp x).deficit ≤ t.cost charge x := by
  induction t with
  | leaf s => simp only [logMassCost, selectedLeaf, cost, mul_zero, zero_add, le_refl]
  | cut s φ p f ihp ihf => exact hp.elim
  | select s n label hsep f ih =>
    have hchild := ih x.1 (hp x.1) x.2
    have hlocal := s.componentCharge_ge_log_mass n label x.1
    change (3 - sharpSidonExponent) * (-Real.log (finitePush s.weight (imageEndpoint s.support label) x.1) +
      (f x.1).logMassCost (hp x.1) x.2) + ((f x.1).selectedLeaf (hp x.1) x.2).deficit ≤
        s.componentCharge label x.1 + (f x.1).cost charge x.2
    linarith

/-- The selected leaf uses its actual uniform carried reference, with the
whole path cost paid by the initial reference deficit. -/
theorem exists_pure_uniform_leaf_log_norm {s : GibbsReference G} (t : GibbsInterleavedRecursion s)
    (hp : t.IsPure) (hs : s.weight = uniformReference s.support) :
    ∃ x : t.Outcome, Real.log (s.support.card : ℝ) - sharpRetentionTau * s.deficit ≤
      Real.log (energyNorm (t.selectedLeaf hp x).support) := by
  obtain ⟨x, hx⟩ := t.exists_realization_cut_budget
  refine ⟨x, ?_⟩
  have hcost := (t.pure_cost_lower_bound (fun s φ _ ↦ s.cutCharge φ) hp x).trans hx
  rw [t.logMassCost_eq hp hs x] at hcost
  have hleaf := log_energyNorm_ge_uniform_reference (t.selectedLeaf hp x).nonempty
  have he : referenceDeficit (t.selectedLeaf hp x).support (uniformReference (t.selectedLeaf hp x).support) =
      (t.selectedLeaf hp x).deficit := by
    rw [← t.selectedLeaf_uniform hp hs x]
    rfl
  rw [he] at hleaf
  have hδ := (t.selectedLeaf hp x).deficit_nonneg
  have hγ := sharpSidonExponent_strict_bounds
  have hc : 0 < 3 - sharpSidonExponent := by linarith
  have hbound : Real.log (s.support.card : ℝ) - Real.log (energyNorm (t.selectedLeaf hp x).support) ≤
      s.deficit / (3 - sharpSidonExponent) := by
    apply (le_div_iff₀ hc).mpr
    have hm := mul_le_mul_of_nonneg_left hleaf hc.le
    have hn := mul_nonneg (show 0 ≤ sharpSidonExponent - 2 by linarith) hδ
    nlinarith
  unfold sharpRetentionTau
  simp only [div_eq_mul_inv, one_mul] at hbound ⊢
  linarith

theorem exists_pure_uniform_leaf_norm {S : Finset G} (hS : S.Nonempty)
    (t : GibbsInterleavedRecursion (GibbsReference.uniform S hS)) (hp : t.IsPure)
    {K : ℝ} (hK : 0 < K) (hD : ((S - S).card : ℝ) ≤ K * S.card) :
    ∃ x : t.Outcome, (S.card : ℝ) / K ^ (Real.log 2 / Real.log (4 / 3 : ℝ)) ≤
      energyNorm (t.selectedLeaf hp x).support := by
  obtain ⟨x, hx⟩ := t.exists_pure_uniform_leaf_log_norm hp rfl
  refine ⟨x, ?_⟩
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hW : (0 : ℝ) < (S - S).card := by
    obtain ⟨a, ha⟩ := hS
    exact_mod_cast (Finset.card_pos.mpr ⟨0, Finset.mem_sub.mpr ⟨a, ha, a, ha, sub_self a⟩⟩)
  have hratio : ((S - S).card : ℝ) / S.card ≤ K := (div_le_iff₀ hN).mpr hD
  have hδ := (GibbsReference.uniform_deficit_le S hS).trans (Real.log_le_log (div_pos hW hN) hratio)
  have hτ : 0 ≤ sharpRetentionTau := by
    unfold sharpRetentionTau
    exact div_nonneg zero_le_one (sub_nonneg.mpr sharpSidonExponent_bounds.2)
  have hm := mul_le_mul_of_nonneg_left hδ hτ
  change Real.log (S.card : ℝ) - sharpRetentionTau * (GibbsReference.uniform S hS).deficit ≤ _ at hx
  have hlog : Real.log (S.card : ℝ) - sharpRetentionTau * Real.log K ≤
      Real.log (energyNorm (t.selectedLeaf hp x).support) := by linarith
  apply (Real.log_le_log_iff (div_pos hN (Real.rpow_pos_of_pos hK _))
    (energyNorm_pos (t.selectedLeaf hp x).nonempty)).mp
  rw [Real.log_div hN.ne' (Real.rpow_pos_of_pos hK _).ne', Real.log_rpow hK,
    ← sharpRetentionTau_eq_log_ratio]
  exact hlog

end GibbsInterleavedRecursion
end
end Erdos539Geometry
