/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsAutocorrelationStability
import Erdos539.GibbsFiberDrift

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators Pointwise
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
local instance zeroAlignmentImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

theorem projectedReferenceLaw_diagonal_pos {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) (a b : S.image φ) :
    0 < (projectedReferenceLaw S φ u hu).mass a b a b := by
  obtain ⟨x, rfl⟩ := imageEndpoint_surjective S φ a
  obtain ⟨y, rfl⟩ := imageEndpoint_surjective S φ b
  let Q := referenceGibbsLaw S u hu
  have hp : 0 < Q.mass x y x y := by
    change 0 < weightedGibbsMass S (referencePowerWeight u) x y x y
    rw [weightedGibbsMass, additiveQuadrupleWeight, if_pos rfl]
    exact div_pos (mul_pos (mul_pos (referencePowerWeight_pos hu x) (referencePowerWeight_pos hu y))
      (mul_pos (referencePowerWeight_pos hu x) (referencePowerWeight_pos hu y))) (referencePartition_pos hS hu)
  have hl := le_finitePush Q.flat (StationaryAdditiveLaw.mapFour (imageEndpoint S φ))
    (fun z ↦ Q.nonneg z.1.1 z.1.2 z.2.1 z.2.2) ((x, y), (x, y))
  exact hp.trans_le hl

/-- Zero average alignment cost forces equality of every pair of fiber
correlation vectors: all diagonal projected quadruples have positive mass. -/
theorem imageAutocorrelationDistance_zero_of_mean_zero {S : Finset G} (hS : S.Nonempty)
    (φ : G →+ H) (u : S → ℝ) (hu : ∀ x, 0 < u x)
    (hzero : meanImageAutocorrelationDistance S φ u hu = 0) (a b : S.image φ) :
    autocorrelationDistanceSq S (imageAutocorrelationWeight S φ u a) (imageAutocorrelationWeight S φ u b) = 0 := by
  let q := fun a b c d ↦ (projectedReferenceLaw S φ u hu).mass a b c d *
    imageSixAutocorrelationDistances S φ u a b c d
  have hn a b c d : 0 ≤ q a b c d := mul_nonneg
    ((projectedReferenceLaw S φ u hu).nonneg a b c d) (imageSixAutocorrelationDistances_nonneg S φ u a b c d)
  change (∑ a, ∑ b, ∑ c, ∑ d, q a b c d) = 0 at hzero
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦
    Finset.sum_nonneg (fun c _ ↦ Finset.sum_nonneg (fun d _ ↦ hn a b c d))))).mp hzero a (Finset.mem_univ a)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ ↦ Finset.sum_nonneg (fun c _ ↦
    Finset.sum_nonneg (fun d _ ↦ hn a b c d)))).mp h1 b (Finset.mem_univ b)
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ ↦ Finset.sum_nonneg (fun d _ ↦ hn a b c d))).mp
    h2 a (Finset.mem_univ a)
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun d _ ↦ hn a b a d)).mp h3 b (Finset.mem_univ b)
  have hz := (mul_eq_zero.mp h4).resolve_left (projectedReferenceLaw_diagonal_pos hS φ u hu a b).ne'
  unfold imageSixAutocorrelationDistances at hz
  have haa := autocorrelationDistanceSq_nonneg S (imageAutocorrelationWeight S φ u a) (imageAutocorrelationWeight S φ u a)
  have hab := autocorrelationDistanceSq_nonneg S (imageAutocorrelationWeight S φ u a) (imageAutocorrelationWeight S φ u b)
  have hba := autocorrelationDistanceSq_nonneg S (imageAutocorrelationWeight S φ u b) (imageAutocorrelationWeight S φ u a)
  have hbb := autocorrelationDistanceSq_nonneg S (imageAutocorrelationWeight S φ u b) (imageAutocorrelationWeight S φ u b)
  linarith

theorem normalizedAutocorrelation_eq_of_distance_zero (S : Finset G) (f g : G → ℝ)
    (he : autocorrelationDistanceSq S f g = 0) {z : G} (hz : z ∈ S - S) :
    normalizedAutocorrelation S f z = normalizedAutocorrelation S g z := by
  have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ ↦ sq_nonneg
    (normalizedAutocorrelation S f z - normalizedAutocorrelation S g z))).mp he z hz
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)

theorem fiberEndpointDrift_zero_of_mean_zero {S : Finset G} (hS : S.Nonempty)
    (φ : G →+ H) (u : S → ℝ) (hu : ∀ x, 0 < u x)
    (he : meanFiberEndpointDrift S φ u = 0) (y : S.image φ) : fiberEndpointDrift S φ u y = 0 := by
  have hp := finitePush_imageEndpoint_pos S φ (referenceEndpoint S u) (referenceEndpoint_pos hS hu) y
  have hn z : 0 ≤ finitePush (referenceEndpoint S u) (imageEndpoint S φ) z * fiberEndpointDrift S φ u z :=
    mul_nonneg (finitePush_nonneg _ _ (fun x ↦ (referenceEndpoint_pos hS hu x).le) z)
      (fiberEndpointDrift_nonneg hS φ u hu z)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ ↦ hn z)).mp he y (Finset.mem_univ y)
  exact (mul_eq_zero.mp hz).resolve_left hp.ne'

end
end Erdos539Geometry
