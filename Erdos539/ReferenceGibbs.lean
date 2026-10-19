/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedGibbsEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def referencePowerWeight {S : Finset G} (u : S → ℝ) (x : S) : ℝ := u x ^ (3 / 4 : ℝ)

def referencePartition (S : Finset G) (u : S → ℝ) : ℝ :=
  weightedGibbsPartition S (referencePowerWeight u)

def referenceDeficit (S : Finset G) (u : S → ℝ) : ℝ := -Real.log (referencePartition S u)

def referenceEndpoint (S : Finset G) (u : S → ℝ) : S → ℝ :=
  weightedGibbsEndpoint S (referencePowerWeight u)

omit [AddCommGroup G] [DecidableEq G] in
theorem referencePowerWeight_pos {S : Finset G} {u : S → ℝ} (hu : ∀ x, 0 < u x) (x : S) :
    0 < referencePowerWeight u x := Real.rpow_pos_of_pos (hu x) _

theorem referencePartition_pos {S : Finset G} (hS : S.Nonempty) {u : S → ℝ}
    (hu : ∀ x, 0 < u x) : 0 < referencePartition S u :=
  weightedGibbsPartition_pos hS (referencePowerWeight_pos hu)

/-- Recompute the canonical additive law from the carried reference,
using exponent 3/4 rather than an ordinary norm optimizer. -/
def referenceGibbsLaw (S : Finset G) (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    StationaryAdditiveLaw S (referenceEndpoint S u) :=
  weightedGibbsLaw S (referencePowerWeight u) (fun x ↦ (referencePowerWeight_pos hu x).le)

theorem referenceEndpoint_pos {S : Finset G} (hS : S.Nonempty) {u : S → ℝ}
    (hu : ∀ x, 0 < u x) (x : S) : 0 < referenceEndpoint S u x :=
  weightedGibbsEndpoint_pos (referencePowerWeight_pos hu) (referencePartition_pos hS hu) x

theorem referenceEndpoint_sum {S : Finset G} (hS : S.Nonempty) {u : S → ℝ}
    (hu : ∀ x, 0 < u x) : ∑ x, referenceEndpoint S u x = 1 :=
  weightedGibbsEndpoint_sum (referencePartition_pos hS hu).ne'

namespace StationaryAdditiveLaw
variable {S : Finset G} {η : S → ℝ}

/-- Exact coefficient-three variational identity for every stationary
competitor, with the relative-entropy directions fixed by literal laws. -/
theorem referenceGibbs_variational_identity (Q : StationaryAdditiveLaw S η)
    (hη : ∑ x, η x = 1) (hS : S.Nonempty) {u : S → ℝ} (hu : ∀ x, 0 < u x) :
    finiteRelEntropy Q.flat (referenceGibbsLaw S u hu).flat =
      Q.correlation + 3 * finiteRelEntropy η u - referenceDeficit S u := by
  have h := Q.relativeEntropy_weightedGibbs hη (referencePowerWeight_pos hu)
    (referencePartition_pos hS hu)
  have hsum : (∑ x, η x * Real.log (referencePowerWeight u x)) =
      (3 / 4 : ℝ) * ∑ x, η x * Real.log (u x) := by
    simp only [referencePowerWeight, Real.log_rpow (hu _), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum] at h
  change finiteRelEntropy Q.flat (referenceGibbsLaw S u hu).flat = _ at h
  rw [h, finiteRelEntropy_eq_entropy_cross]
  unfold correlation referenceDeficit referencePartition
  ring

theorem referenceGibbs_variational_bound (Q : StationaryAdditiveLaw S η)
    (hη : ∑ x, η x = 1) (hS : S.Nonempty) {u : S → ℝ} (hu : ∀ x, 0 < u x) :
    referenceDeficit S u ≤ Q.correlation + 3 * finiteRelEntropy η u := by
  have h := Q.relativeEntropy_weightedGibbs_nonneg hη (referencePowerWeight_pos hu)
    (referencePartition_pos hS hu)
  change 0 ≤ finiteRelEntropy Q.flat (referenceGibbsLaw S u hu).flat at h
  rw [Q.referenceGibbs_variational_identity hη hS hu] at h
  linarith

end StationaryAdditiveLaw

/-- The variational bound is attained by the newly computed Gibbs law. -/
theorem referenceGibbs_deficit_identity {S : Finset G} (hS : S.Nonempty)
    {u : S → ℝ} (hu : ∀ x, 0 < u x) :
    referenceDeficit S u = (referenceGibbsLaw S u hu).correlation +
      3 * finiteRelEntropy (referenceEndpoint S u) u := by
  have h := (referenceGibbsLaw S u hu).referenceGibbs_variational_identity
    (referenceEndpoint_sum hS hu) hS hu
  have hself : finiteRelEntropy (referenceGibbsLaw S u hu).flat
      (referenceGibbsLaw S u hu).flat = 0 := by simp [finiteRelEntropy]
  rw [hself] at h
  linarith

theorem referenceDeficit_nonneg {S : Finset G} (hS : S.Nonempty) {u : S → ℝ}
    (hu : ∀ x, 0 < u x) (hus : ∑ x, u x = 1) : 0 ≤ referenceDeficit S u := by
  rw [referenceGibbs_deficit_identity hS hu]
  have hcorr := (referenceGibbsLaw S u hu).correlation_nonneg
    (fun x ↦ (referenceEndpoint_pos hS hu x).le) (referenceEndpoint_sum hS hu)
  have hkl := finiteRelEntropy_nonneg (referenceEndpoint S u) u
    (fun x ↦ (referenceEndpoint_pos hS hu x).le) (fun x ↦ (hu x).le)
    (referenceEndpoint_sum hS hu) hus (fun x _ ↦ hu x)
  linarith

/-- Young's bound at exponent 4/3 follows from the exact entropy identity,
with no analytic convolution theorem assumed. -/
theorem referencePartition_le_one {S : Finset G} (hS : S.Nonempty) {u : S → ℝ}
    (hu : ∀ x, 0 < u x) (hus : ∑ x, u x = 1) : referencePartition S u ≤ 1 := by
  apply (Real.log_le_log_iff (referencePartition_pos hS hu) (by norm_num : (0 : ℝ) < 1)).mp
  have h := referenceDeficit_nonneg hS hu hus
  unfold referenceDeficit at h
  rw [Real.log_one]
  linarith

/-- The reference Gibbs law is the entropy maximum for its own recomputed
endpoint law, even when it is not an ordinary energy optimizer. -/
theorem referenceGibbs_entropy_maximal {S : Finset G} (hS : S.Nonempty)
    {u : S → ℝ} (hu : ∀ x, 0 < u x)
    (Q : StationaryAdditiveLaw S (referenceEndpoint S u)) :
    Q.entropy ≤ (referenceGibbsLaw S u hu).entropy :=
  weightedGibbs_entropy_maximal (referencePowerWeight_pos hu) (referencePartition_pos hS hu) Q

end
end Erdos539Geometry
