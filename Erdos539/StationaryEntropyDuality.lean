/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.AdditiveProbabilityPolytope
import Erdos539.FiniteConcaveDuality
import Erdos539.WeightedGibbsEntropy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The common-endpoint log-partition dual, using an unrestricted real
potential so its exponential weights are always strictly positive. -/
def stationaryEntropyDualValue (S : Finset G) (ν t : S → ℝ) : ℝ :=
  Real.log (weightedGibbsPartition S (fun x ↦ Real.exp (t x))) - 4 * ∑ x, ν x * t x

theorem stationaryAdditiveEntropy_le_partition {S : Finset G} (hS : S.Nonempty)
    {ν f : S → ℝ} (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (hf : ∀ x, 0 < f x) :
    stationaryAdditiveEntropy S ν ≤
      Real.log (weightedGibbsPartition S f) - 4 * ∑ x, ν x * Real.log (f x) := by
  obtain ⟨Q, hQ⟩ := stationaryAdditiveEntropy_attained S ν hν hs
  have h := Q.relativeEntropy_weightedGibbs_nonneg hs hf (weightedGibbsPartition_pos hS hf)
  rw [Q.relativeEntropy_weightedGibbs hs hf (weightedGibbsPartition_pos hS hf), hQ] at h
  linarith

theorem stationaryAdditiveEntropy_le_dualValue {S : Finset G} (hS : S.Nonempty)
    {ν : S → ℝ} (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (t : S → ℝ) :
    stationaryAdditiveEntropy S ν ≤ stationaryEntropyDualValue S ν t := by
  simpa only [stationaryEntropyDualValue, Real.log_exp] using
    stationaryAdditiveEntropy_le_partition hS hν hs (fun x ↦ Real.exp_pos (t x))

/-- Common endpoint potentials approach the actual entropy maximum,
even when the prescribed endpoint law has zero atoms. The proof first
separates all four marginal constraints, then tests the resulting bound
on the genuine Gibbs law of the averaged potential. -/
theorem stationaryEntropyDualValue_approximate {S : Finset G} (hS : S.Nonempty)
    {ν : S → ℝ} (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : S → ℝ, stationaryEntropyDualValue S ν t < stationaryAdditiveEntropy S ν + ε := by
  obtain ⟨P, hP⟩ := stationaryAdditiveEntropy_attained S ν hν hs
  have hmax : ∀ p ∈ additiveProbabilities S, quadrupleMarginals S p = repeatedMarginal S ν →
      finiteEntropy p ≤ stationaryAdditiveEntropy S ν := by
    intro p hp hm
    let Q := StationaryAdditiveLaw.ofFlat (stationaryAdditiveWeights_of_marginals hp hm)
    simpa only [Q, StationaryAdditiveLaw.ofFlat_entropy] using Q.entropy_le_stationaryAdditiveEntropy hν hs
  have heP : finiteEntropy P.flat = stationaryAdditiveEntropy S ν := by
    simpa only [finiteEntropy, StationaryAdditiveLaw.flat, StationaryAdditiveLaw.entropy,
      Fintype.sum_prod_type] using hP
  obtain ⟨l, hl⟩ := finite_concave_approximate_dual (additiveProbabilities S)
    (additiveProbabilities_isCompact S) (quadrupleMarginals S) finiteEntropy
    continuous_finiteEntropy (additiveProbabilities_entropy_concave S)
    (repeatedMarginal S ν) (stationaryAdditiveEntropy S ν) P.flat
    (P.flat_mem_additiveProbabilities hs) P.quadrupleMarginals_flat heP hmax hε
  let ψ : S → ℝ := fun x ↦ l (repeatedMarginal S (Pi.single x 1))
  have hexp (v : S → ℝ) : l (repeatedMarginal S v) = ∑ x, v x * ψ x := by
    let k := l.comp (repeatedMarginal S)
    change k v = ∑ x, v x * ψ x
    conv_lhs => rw [pi_eq_sum_univ' v]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, k, ψ, LinearMap.comp_apply]
  let t : S → ℝ := fun x ↦ -ψ x / 4
  let f : S → ℝ := fun x ↦ Real.exp (t x)
  have hf : ∀ x, 0 < f x := fun x ↦ Real.exp_pos _
  have hZ := weightedGibbsPartition_pos hS hf
  let Q := weightedGibbsLaw S f (fun x ↦ (hf x).le)
  have h := hl Q.flat (Q.flat_mem_additiveProbabilities (weightedGibbsEndpoint_sum hZ.ne'))
  rw [Q.quadrupleMarginals_flat, hexp, hexp] at h
  have heflat : finiteEntropy Q.flat = Q.entropy := by
    simp only [finiteEntropy, StationaryAdditiveLaw.flat, StationaryAdditiveLaw.entropy,
      Fintype.sum_prod_type]
  rw [heflat] at h
  have hcross (v : S → ℝ) : 4 * ∑ x, v x * Real.log (f x) = -(∑ x, v x * ψ x) := by
    simp only [f, Real.log_exp, t, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hent := weightedGibbs_entropy hf hZ
  change Q.entropy = _ at hent
  rw [hcross] at hent
  refine ⟨t, ?_⟩
  have ht : stationaryEntropyDualValue S ν t =
      Real.log (weightedGibbsPartition S f) - 4 * ∑ x, ν x * Real.log (f x) := by
    simp only [stationaryEntropyDualValue, f, Real.log_exp]
  rw [ht, hcross]
  linarith

/-- Exact duality is an infimum; it does not assert an attained finite
potential at a boundary endpoint law. -/
theorem stationaryAdditiveEntropy_eq_inf_dualValue {S : Finset G} (hS : S.Nonempty)
    {ν : S → ℝ} (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    stationaryAdditiveEntropy S ν = sInf (Set.range (stationaryEntropyDualValue S ν)) := by
  have hne : (Set.range (stationaryEntropyDualValue S ν)).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hb : BddBelow (Set.range (stationaryEntropyDualValue S ν)) := by
    refine ⟨stationaryAdditiveEntropy S ν, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact stationaryAdditiveEntropy_le_dualValue hS hν hs t
  apply le_antisymm
  · apply le_csInf hne
    rintro _ ⟨t, rfl⟩
    exact stationaryAdditiveEntropy_le_dualValue hS hν hs t
  · by_contra hn
    have hgap : 0 < sInf (Set.range (stationaryEntropyDualValue S ν)) - stationaryAdditiveEntropy S ν :=
      sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨t, ht⟩ := stationaryEntropyDualValue_approximate hS hν hs (half_pos hgap)
    have hle := csInf_le hb (Set.mem_range_self t)
    linarith

end
end Erdos539Geometry
