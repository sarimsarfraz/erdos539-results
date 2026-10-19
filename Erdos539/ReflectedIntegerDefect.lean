/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectedDefectComparison
import Erdos539.IntegerCountingCertificate

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical

def reflectedCountingCharge (S : Finset ℤ) (w : ℤ) : ℝ :=
  ((reflectedSupport S w).card : ℝ) ^ 2 *
    Real.log (((reflectedSupport S w).card : ℝ) ^ 3 / countingEnergy (reflectedSupport S w))

theorem reflectedCountingCharge_eq_of_stats {S : Finset ℤ} {w : ℤ} {r E : ℕ}
    (hr : (reflectedSupport S w).card = r) (he : countingEnergy (reflectedSupport S w) = E) :
    reflectedCountingCharge S w = (r : ℝ) ^ 2 * Real.log ((r : ℝ) ^ 3 / E) := by
  simp only [reflectedCountingCharge, hr, he]

theorem reflectedMeanCountingDefect_eq_interval (S : Finset ℤ) (B : ℕ)
    (hS : ∀ a ∈ S, 0 ≤ a ∧ 2 * a < B) :
    reflectedMeanCountingDefect S =
      (∑ w ∈ Finset.range B, reflectedCountingCharge S w) / countingEnergy S := by
  let W : Finset ℤ := (Finset.range B).image (fun n : ℕ ↦ (n : ℤ))
  have hsub : S + S ⊆ W := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hw
    have ha' := hS a ha
    have hb' := hS b hb
    have hn : 0 ≤ a + b := by omega
    apply Finset.mem_image.mpr
    refine ⟨(a + b).toNat, Finset.mem_range.mpr ?_, Int.toNat_of_nonneg hn⟩
    omega
  have he : (∑ w ∈ S + S, reflectedCountingCharge S w) =
      ∑ w ∈ Finset.range B, reflectedCountingCharge S w := by
    calc
      _ = ∑ w ∈ W, reflectedCountingCharge S w := by
        apply Finset.sum_subset hsub
        intro w _ hw
        have hz : reflectedSupport S w = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro a ha
          obtain ⟨ha, hb⟩ := Finset.mem_filter.mp ha
          exact hw (Finset.mem_add.mpr ⟨a, ha, w - a, hb, by omega⟩)
        simp [reflectedCountingCharge, hz]
      _ = _ := by
        rw [Finset.sum_image]
        intro a _ b _ hh
        exact Int.ofNat.inj hh
  unfold reflectedMeanCountingDefect countingReflectionWeight
  simp_rw [div_mul_eq_mul_div]
  change (∑ w ∈ S + S, reflectedCountingCharge S w / countingEnergy S) = _
  simp only [div_eq_mul_inv, ← Finset.sum_mul, he]

end
end Erdos539Geometry
