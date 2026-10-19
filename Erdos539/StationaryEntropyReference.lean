/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryEntropyMaximum
import Erdos539.ReferenceGibbs

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The entropy maximum for the recomputed endpoint law is the actual
reference Gibbs law's entropy. -/
theorem stationaryAdditiveEntropy_referenceEndpoint {S : Finset G} (hS : S.Nonempty)
    {u : S → ℝ} (hu : ∀ x, 0 < u x) :
    stationaryAdditiveEntropy S (referenceEndpoint S u) = (referenceGibbsLaw S u hu).entropy :=
  stationaryAdditiveEntropy_eq_of_maximal _ (referenceGibbs_entropy_maximal hS hu)

/-- The manuscript's exact gap identity for any actual entropy maximizer,
including a competing endpoint law with zero atoms. -/
theorem stationaryEntropyMax_reference_identity {S : Finset G} (hS : S.Nonempty)
    {η u : S → ℝ} (hηs : ∑ x, η x = 1) (hu : ∀ x, 0 < u x)
    (Q : StationaryAdditiveLaw S η) (hQ : Q.entropy = stationaryAdditiveEntropy S η) :
    finiteRelEntropy Q.flat (referenceGibbsLaw S u hu).flat =
      stationaryEntropyDefect S η + 3 * finiteRelEntropy η u - referenceDeficit S u := by
  rw [Q.referenceGibbs_variational_identity hηs hS hu]
  simp only [StationaryAdditiveLaw.correlation, stationaryEntropyDefect, hQ]

theorem referenceDeficit_le_stationaryEntropyDefect {S : Finset G} (hS : S.Nonempty)
    {η u : S → ℝ} (hη : ∀ x, 0 ≤ η x) (hηs : ∑ x, η x = 1) (hu : ∀ x, 0 < u x) :
    referenceDeficit S u ≤ stationaryEntropyDefect S η + 3 * finiteRelEntropy η u := by
  obtain ⟨Q, hQ⟩ := stationaryAdditiveEntropy_attained S η hη hηs
  have h := Q.referenceGibbs_variational_bound hηs hS hu
  simpa only [StationaryAdditiveLaw.correlation, stationaryEntropyDefect, hQ] using h

theorem referenceDeficit_eq_stationaryEntropyDefect {S : Finset G} (hS : S.Nonempty)
    {u : S → ℝ} (hu : ∀ x, 0 < u x) :
    referenceDeficit S u = stationaryEntropyDefect S (referenceEndpoint S u) +
      3 * finiteRelEntropy (referenceEndpoint S u) u := by
  rw [stationaryEntropyDefect, stationaryAdditiveEntropy_referenceEndpoint hS hu]
  exact referenceGibbs_deficit_identity hS hu

/-- The reference deficit is the attained minimum over all endpoint
probability laws, with the minimizing law explicitly recomputed from u. -/
theorem referenceDeficit_isLeast {S : Finset G} (hS : S.Nonempty)
    {u : S → ℝ} (hu : ∀ x, 0 < u x) :
    IsLeast {v : ℝ | ∃ η : S → ℝ, (∀ x, 0 ≤ η x) ∧ (∑ x, η x = 1) ∧
      v = stationaryEntropyDefect S η + 3 * finiteRelEntropy η u} (referenceDeficit S u) := by
  refine ⟨⟨referenceEndpoint S u, fun x ↦ (referenceEndpoint_pos hS hu x).le,
    referenceEndpoint_sum hS hu, referenceDeficit_eq_stationaryEntropyDefect hS hu⟩, ?_⟩
  rintro v ⟨η, hη, hηs, rfl⟩
  exact referenceDeficit_le_stationaryEntropyDefect hS hη hηs hu

end
end Erdos539Geometry
