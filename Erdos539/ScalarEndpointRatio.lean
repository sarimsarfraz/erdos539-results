/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarMaxClass
import Erdos539.ScalarRealInterval
import Erdos539.ScalarGeometricTail

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance scalarEndpointRatioDecidableEq : DecidableEq ℝ := Classical.decEq _

def scalarEndpointReference (N : ℕ) (a : scalarRealInterval N) : ℝ :=
  Real.exp (-(Real.log N / N) * a.val)

theorem scalarEndpointReference_pos (N : ℕ) (a : scalarRealInterval N) :
    0 < scalarEndpointReference N a := Real.exp_pos _

/-- A bound for the actual Tg/g ratio, obtained from its literal scalar
maximum classes and a finite geometric tail. -/
theorem scalarEndpointRatio_bound {N : ℕ} (hN : 2 ≤ N) (c : scalarRealInterval N) :
    channelWeightRatio (scalarPositiveDifferenceChannel (scalarRealInterval N))
      (scalarEndpointReference N) c ≤
        Real.exp (Real.log N * c.val / N) + 1 / (Real.exp (Real.log N / N) - 1) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let t := Real.log N / N
  have ht : 0 < t := div_pos (Real.log_pos hNr) hNp
  let m : scalarRealInterval N := ⟨0, mem_scalarRealInterval.mpr ⟨0, by omega, by norm_num⟩⟩
  have hm : m.val ≤ c.val := scalarRealInterval_nonneg c
  have hmax : ∀ a : scalarRealInterval N, a.val ≤ c.val → scalarEndpointReference N a ≤ scalarEndpointReference N m := by
    intro a _
    change Real.exp (-t * a.val) ≤ Real.exp (-t * 0)
    apply Real.exp_le_exp.mpr
    have ha := scalarRealInterval_nonneg a
    nlinarith
  have hrow := scalarChannel_weightSum (scalarEndpointReference N) (scalarEndpointReference_pos N) c m hm hmax
  have hmone : scalarEndpointReference N m = 1 := by simp [scalarEndpointReference, m]
  rw [hmone] at hrow
  have hdiv : (∑ a ∈ Finset.univ.filter (fun a : scalarRealInterval N ↦ c.val < a.val), scalarEndpointReference N a) /
      scalarEndpointReference N c =
      ∑ a ∈ Finset.univ.filter (fun a : scalarRealInterval N ↦ c.val < a.val), Real.exp (-t * (a.val - c.val)) := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    change Real.exp (-t * a.val) / Real.exp (-t * c.val) = _
    rw [← Real.exp_sub]
    congr 1
    ring
  have hfirst : 1 / scalarEndpointReference N c = Real.exp (Real.log N * c.val / N) := by
    change 1 / Real.exp (-t * c.val) = _
    rw [one_div, ← Real.exp_neg]
    congr 1
    dsimp [t]
    ring
  obtain ⟨k, _hk, hkc⟩ := mem_scalarRealInterval.mp c.property
  have hsum : (∑ a ∈ Finset.univ.filter (fun a : scalarRealInterval N ↦ c.val < a.val),
      Real.exp (-t * (a.val - c.val))) =
        ∑ j ∈ Finset.range N, if k < j then Real.exp (-t * ((j : ℝ) - k)) else 0 := by
    rw [Finset.sum_filter]
    change (∑ a : scalarRealInterval N, (fun x : ℝ ↦ if c.val < x then Real.exp (-t * (x - c.val)) else 0) a.val) = _
    rw [scalarRealInterval_sum N (fun x : ℝ ↦ if c.val < x then Real.exp (-t * (x - c.val)) else 0)]
    simp only [← hkc, Nat.cast_lt]
  unfold channelWeightRatio
  rw [hrow, add_div, hdiv, hfirst, hsum]
  exact add_le_add le_rfl (exponential_tail_index_bound ht N k)

/-- The actual reference ratio is at most 2N/log N on the first half. -/
theorem scalarEndpointRatio_prefix {N : ℕ} (hN : 2 ≤ N) (c : scalarRealInterval N)
    (hc : c.val ≤ (N : ℝ) / 2) :
    channelWeightRatio (scalarPositiveDifferenceChannel (scalarRealInterval N))
      (scalarEndpointReference N) c ≤ 2 * (N : ℝ) / Real.log N := by
  exact (scalarEndpointRatio_bound hN c).trans
    (endpoint_prefix_ratio_bound (by exact_mod_cast (show 1 < N by omega)) hc)

end
end Erdos539Geometry
