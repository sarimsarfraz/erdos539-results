/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectedMassEntropy
import Erdos539.EnergyHereditary

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators Pointwise
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem reflectedLawMass_square_weight (S : Finset G) (f : S → ℝ) (w : G) :
    reflectedLawMass S (fun x ↦ f x ^ 2) w = weightSquareSum (reflectedSupport S w) (extendWeight S f) := by
  rw [weightSquareSum, reflectedSupport, Finset.sum_filter, ← Finset.sum_attach S]
  simp only [reflectedLawMass, extendWeight_mem]
  rfl

theorem energyMaximizer_reflected_mass_le {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    {r : ℝ} (hr : 0 ≤ r) (hR : ∀ w : G, energyNorm (reflectedSupport S w) ≤ energyNorm S * r ^ 2)
    (w : G) : reflectedLawMass S (fun x ↦ f x ^ 2) w ≤ r := by
  have h := energyNorm_hereditary (A := reflectedSupport S w) (Finset.filter_subset _ _) hS hf hE
  rw [← reflectedLawMass_square_weight] at h
  have hm := reflectedLawMass_nonneg S (fun x ↦ f x ^ 2) (fun x ↦ sq_nonneg (f x)) w
  have hs : reflectedLawMass S (fun x ↦ f x ^ 2) w ^ 2 ≤ r ^ 2 :=
    (mul_le_mul_iff_right₀ (energyNorm_pos hS)).mp (h.trans (hR w))
  nlinarith

/-- Uniform reflected norm bounds force a defect cost at every exact
optimizer, including those with zero endpoint atoms. -/
theorem energyMaximizer_reflected_norm_cost {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    {r : ℝ} (hr : 0 ≤ r) (hR : ∀ w : G, energyNorm (reflectedSupport S w) ≤ energyNorm S * r ^ 2) :
    -Real.log r ≤ finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm S) := by
  have h := (optimizerStationaryAdditiveLaw hS hf hE).correlation_ge_reflected_mass_cost
    (fun x ↦ sq_nonneg (f x)) hf.2 (energyMaximizer_reflected_mass_le hS hf hE hr hR)
  rwa [optimizerStationaryAdditiveLaw_correlation hS hf hE] at h

theorem reflectedSupport_eq_empty_of_notMem_add {S : Finset G} {w : G} (hw : w ∉ S + S) :
    reflectedSupport S w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hx, hother⟩ := Finset.mem_filter.mp hx
  apply hw
  exact Finset.mem_add.mpr ⟨x, hx, w - x, hother, by abel⟩

/-- Actual reflected-support retention at every exact optimizer. The proof
combines hereditary retention with the support cost of the triple law. -/
theorem exists_reflected_energyNorm_retention {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    ∃ w ∈ S + S, energyNorm S *
      Real.exp (-2 * (finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm S))) ≤
        energyNorm (reflectedSupport S w) := by
  obtain ⟨w, hw, hmax⟩ := (S + S).exists_max_image (fun v ↦ energyNorm (reflectedSupport S v)) (hS.add hS)
  have hMpos : 0 < energyNorm (reflectedSupport S w) := by
    obtain ⟨a, ha⟩ := hS
    have haC : (reflectedSupport S (a + a)).Nonempty :=
      ⟨a, Finset.mem_filter.mpr ⟨ha, by simpa using ha⟩⟩
    exact (energyNorm_pos haC).trans_le (hmax (a + a) (Finset.mem_add.mpr ⟨a, ha, a, ha, rfl⟩))
  have hR : ∀ v : G, energyNorm (reflectedSupport S v) ≤ energyNorm (reflectedSupport S w) := by
    intro v
    by_cases hv : v ∈ S + S
    · exact hmax v hv
    · rw [reflectedSupport_eq_empty_of_notMem_add hv, energyNorm_empty]
      exact hMpos.le
  let r := Real.sqrt (energyNorm (reflectedSupport S w) / energyNorm S)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hsq : energyNorm S * r ^ 2 = energyNorm (reflectedSupport S w) := by
    rw [Real.sq_sqrt (div_pos hMpos (energyNorm_pos hS)).le]
    field_simp [(energyNorm_pos hS).ne']
  have hc := energyMaximizer_reflected_norm_cost hS hf hE hr (fun v ↦ by rw [hsq]; exact hR v)
  have hlog : Real.log r = (Real.log (energyNorm (reflectedSupport S w)) - Real.log (energyNorm S)) / 2 := by
    rw [Real.log_sqrt (div_pos hMpos (energyNorm_pos hS)).le,
      Real.log_div hMpos.ne' (energyNorm_pos hS).ne']
  rw [hlog] at hc
  have hl : Real.log (energyNorm S) + (-2 * (finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm S))) ≤
      Real.log (energyNorm (reflectedSupport S w)) := by linarith
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_add, Real.exp_log (energyNorm_pos hS), Real.exp_log hMpos] at he
  exact ⟨w, hw, he⟩

/-- The support-only cubic retention scale, obtained from an attained
optimizer and its entropy upper bound. -/
theorem exists_reflected_energyNorm_cubic {S : Finset G} (hS : S.Nonempty) :
    ∃ w ∈ S + S, energyNorm S ^ 3 / (S.card : ℝ) ^ 2 ≤ energyNorm (reflectedSupport S w) := by
  obtain ⟨f, hf, hs, hE⟩ := energyNorm_attained hS
  obtain ⟨w, hw, hret⟩ := exists_reflected_energyNorm_retention hS ⟨hf, hs⟩ hE
  have he := (energyMaximizer_entropy_bounds hS ⟨hf, hs⟩ hE).2
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hl : Real.log (energyNorm S ^ 2 / (S.card : ℝ) ^ 2) =
      -2 * (Real.log (S.card : ℝ) - Real.log (energyNorm S)) := by
    rw [Real.log_div (pow_pos (energyNorm_pos hS) 2).ne' (pow_pos hn 2).ne', Real.log_pow, Real.log_pow]
    norm_num
    ring
  have hpow := Real.exp_le_exp.mpr (show -2 * (Real.log (S.card : ℝ) - Real.log (energyNorm S)) ≤
      -2 * (finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm S)) by linarith)
  rw [← hl, Real.exp_log (div_pos (pow_pos (energyNorm_pos hS) 2) (pow_pos hn 2))] at hpow
  have hmul := mul_le_mul_of_nonneg_left hpow (energyNorm_nonneg S)
  have hid : energyNorm S * (energyNorm S ^ 2 / (S.card : ℝ) ^ 2) = energyNorm S ^ 3 / (S.card : ℝ) ^ 2 := by ring
  rw [hid] at hmul
  exact ⟨w, hw, hmul.trans hret⟩

end
end Erdos539Geometry
