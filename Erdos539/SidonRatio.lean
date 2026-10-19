/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SidonCriticalConcavity

namespace Erdos539Geometry
noncomputable section

/-- The two-weight energy ratio, in a multiplication form convenient
for differentiation. On [0,1] it is the usual quotient by (1+x)^p. -/
def sidonRatio (p x : ℝ) : ℝ := (x ^ p + 4 * x ^ (p / 2) + 1) * (1 + x) ^ (-p)

theorem hasDerivAt_sidonRatio (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (sidonRatio p)
      (p * (1 + x) ^ (-p - 1) * (sidonCritical p x - 1)) x := by
  have h1 := Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')
  have h2 := (Real.hasDerivAt_rpow_const (p := p / 2) (Or.inl hx.ne')).const_mul 4
  have h3 := ((hasDerivAt_id x).const_add 1).rpow_const (p := -p)
    (Or.inl (show (1 : ℝ) + x ≠ 0 by positivity))
  convert ((h1.add h2).add_const 1).mul h3 using 1
  have hp : 0 < 1 + x := by positivity
  have hbase : (1 + x) ^ (-p) = (1 + x) ^ (-p - 1) * (1 + x) := by
    conv_rhs => arg 2; rw [← Real.rpow_one (1 + x)]
    rw [← Real.rpow_add hp]
    congr 1
    ring
  have hfull : x ^ p = x ^ (p - 1) * x := by
    conv_rhs => arg 2; rw [← Real.rpow_one x]
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hhalf : x ^ (p / 2) = x ^ ((p - 2) / 2) * x := by
    conv_rhs => arg 2; rw [← Real.rpow_one x]
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have he : p / 2 - 1 = (p - 2) / 2 := by ring
  unfold sidonCritical
  dsimp only [id, Pi.add_apply]
  rw [hbase, hfull, hhalf, he]
  ring

theorem sidonRatio_continuousOn {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (sidonRatio p) (Set.Icc 0 1) := by
  have hnum := ((Real.continuous_rpow_const hp).add
    ((Real.continuous_rpow_const (show 0 ≤ p / 2 by positivity)).const_mul 4)).add_const 1
  exact hnum.continuousOn.mul ((continuousOn_const.add continuousOn_id).rpow_const
    (fun x hx ↦ Or.inl (show (1 : ℝ) + x ≠ 0 by linarith [hx.1])))

/-- The two-weight ratio never exceeds its endpoint values. No numerical
critical-point or decimal logarithm estimate occurs in the proof. -/
theorem sidonRatio_le_max_endpoints {p x : ℝ} (hp2 : 2 ≤ p) (hp3 : p ≤ 3)
    (hx : x ∈ Set.Icc 0 1) : sidonRatio p x ≤ max (sidonRatio p 0) (sidonRatio p 1) := by
  apply le_max_endpoints_of_concave_derivative_sign (sidonRatio_continuousOn (by linarith))
    (sidonCritical_concave hp2 hp3) (g := sidonCritical p)
    (w := fun y ↦ p * (1 + y) ^ (-p - 1))
  · simp [sidonCritical]
  · intro y hy
    exact hasDerivAt_sidonRatio p hy.1
  · intro y hy
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith [hy.1]) _)
  · exact hx

/-- Normalized sharp Sidon inequality for any admissible exponent.
The sharp logarithmic exponent will be substituted using exact identities. -/
theorem sidon_scalar_unit {p x : ℝ} (hp2 : 2 ≤ p) (hp3 : p ≤ 3)
    (hendpoint : (6 : ℝ) ≤ 2 ^ p) (hx : x ∈ Set.Icc 0 1) :
    x ^ p + 4 * x ^ (p / 2) + 1 ≤ (1 + x) ^ p := by
  have hp : 0 < p := by linarith
  have h0 : sidonRatio p 0 = 1 := by
    simp [sidonRatio, Real.zero_rpow hp.ne', Real.zero_rpow (show p / 2 ≠ 0 by positivity)]
  have h1 : sidonRatio p 1 ≤ 1 := by
    simp only [sidonRatio, Real.one_rpow, mul_one, one_add_one_eq_two]
    norm_num only [show (1 : ℝ) + 4 + 1 = 6 by norm_num]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact (mul_inv_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) p)).mpr (by simpa using hendpoint)
  have h := (sidonRatio_le_max_endpoints hp2 hp3 hx).trans (max_le (by rw [h0]) h1)
  have hb : 0 < 1 + x := by linarith [hx.1]
  change (x ^ p + 4 * x ^ (p / 2) + 1) * (1 + x) ^ (-p) ≤ 1 at h
  rw [Real.rpow_neg hb.le] at h
  exact (mul_inv_le_iff₀ (Real.rpow_pos_of_pos hb p)).mp h |>.trans_eq (one_mul _)

end
end Erdos539Geometry
