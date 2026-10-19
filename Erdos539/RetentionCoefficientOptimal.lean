/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntervalFiberSharpness

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical

/-- No coefficient below one, even with a fixed additive error, controls
the log-norm loss of all actual coordinate fibers of exact optimizers.
The witnesses are literal two-dimensional integer interval products. -/
theorem retention_entropy_coefficient_optimal {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) (C : ℝ) :
    ∃ (n : ℕ), 0 < n ∧ ∃ f : (scalarInterval n ×ˢ ({0, 1} : Finset ℤ)) → ℝ,
      f ∈ admissibleWeights (scalarInterval n ×ˢ ({0, 1} : Finset ℤ)) ∧
      weightedEnergy (scalarInterval n ×ˢ ({0, 1} : Finset ℤ))
        (extendWeight (scalarInterval n ×ˢ ({0, 1} : Finset ℤ)) f) =
          energyNorm (scalarInterval n ×ˢ ({0, 1} : Finset ℤ)) ∧
      c * finiteEntropy (finitePush (fun x ↦ f x ^ 2) (imageEndpoint _ Prod.fst)) + C <
        Real.log (energyNorm (scalarInterval n ×ˢ ({0, 1} : Finset ℤ))) -
          (∑ y, finitePush (fun x ↦ f x ^ 2) (imageEndpoint _ Prod.fst) y *
            Real.log (energyNorm (fiber (scalarInterval n ×ˢ ({0, 1} : Finset ℤ)) Prod.fst y.val))) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (Real.exp ((C + Real.log (3 / 2 : ℝ)) / (1 - c))))
  have hn' : (0 : ℝ) < n := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hn)
  have hn0 : 0 < n := by exact_mod_cast hn'
  have hlog : (C + Real.log (3 / 2 : ℝ)) / (1 - c) < Real.log (n : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) ((le_max_right _ _).trans_lt hn)
    simpa only [Real.log_exp] using h
  have hgap : C < (1 - c) * Real.log (n : ℝ) - Real.log (3 / 2 : ℝ) := by
    have h := (div_lt_iff₀ (sub_pos.mpr hc1)).mp hlog
    nlinarith
  obtain ⟨f, hf, hs, hE⟩ := energyNorm_attained
    ((scalarInterval_nonempty hn0).product (by simp : ({0, 1} : Finset ℤ).Nonempty))
  refine ⟨n, hn0, f, ⟨hf, hs⟩, hE, ?_⟩
  have h := interval_fiber_coefficient_gap hn0 hc (fun x ↦ f x ^ 2) (fun x ↦ sq_nonneg _) hs
  linarith

end
end Erdos539Geometry
