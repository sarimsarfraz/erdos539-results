/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntervalEnergyBounds
import Erdos539.SidonFiberSharpness

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical

variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

theorem product_fiber_log_norm_loss {S : Finset G} {T : Finset H}
    (hS : S.Nonempty) (hT : T.Nonempty) (ν : (S ×ˢ T) → ℝ) (hs : ∑ x, ν x = 1) :
    Real.log (energyNorm (S ×ˢ T)) -
      (∑ y, finitePush ν (imageEndpoint (S ×ˢ T) Prod.fst) y *
        Real.log (energyNorm (fiber (S ×ˢ T) Prod.fst y.val))) = Real.log (energyNorm S) := by
  rw [mean_log_norm_first_product_fibers S T ν hs, energyNorm_product,
    Real.log_mul (energyNorm_pos hS).ne' (energyNorm_pos hT).ne']
  ring

omit [AddCommGroup G] [AddCommGroup H] [DecidableEq H] in
theorem product_first_entropy_upper {S : Finset G} {T : Finset H}
    (hS : S.Nonempty) (hT : T.Nonempty) (ν : (S ×ˢ T) → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    finiteEntropy (finitePush ν (imageEndpoint (S ×ˢ T) Prod.fst)) ≤ Real.log (S.card : ℝ) := by
  haveI : Nonempty ((S ×ˢ T).image Prod.fst) :=
    ((hS.product hT).image Prod.fst).coe_sort
  have h := finiteEntropy_le_log_card (finitePush ν (imageEndpoint (S ×ˢ T) Prod.fst))
    (finitePush_nonneg ν _ hν) (by rw [finitePush_sum, hs])
  simpa only [Fintype.card_coe, Finset.product_image_fst hT] using h

omit [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H] in
theorem interval_fiber_log_norm_loss {n : ℕ} (hn : 0 < n)
    (ν : (scalarInterval n ×ˢ ({0, 1} : Finset ℤ)) → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    finiteEntropy (finitePush ν (imageEndpoint _ Prod.fst)) - Real.log (3 / 2 : ℝ) <
      Real.log (energyNorm (scalarInterval n ×ˢ ({0, 1} : Finset ℤ))) -
        (∑ y, finitePush ν (imageEndpoint _ Prod.fst) y *
          Real.log (energyNorm (fiber (scalarInterval n ×ˢ ({0, 1} : Finset ℤ)) Prod.fst y.val))) := by
  rw [product_fiber_log_norm_loss (scalarInterval_nonempty hn) (by simp) ν hs]
  have hu := product_first_entropy_upper (scalarInterval_nonempty hn) (by simp) ν hν hs
  rw [scalarInterval_card] at hu
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := Real.log_lt_log (by positivity : (0 : ℝ) < 2 * n / 3)
    (energyNorm_scalarInterval_bounds hn).1
  rw [show 2 * (n : ℝ) / 3 = n / (3 / 2) by ring,
    Real.log_div hn'.ne' (by norm_num : (3 / 2 : ℝ) ≠ 0)] at hl
  linarith

omit [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H] in
theorem interval_fiber_coefficient_gap {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 0 ≤ c)
    (ν : (scalarInterval n ×ˢ ({0, 1} : Finset ℤ)) → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    (1 - c) * Real.log (n : ℝ) - Real.log (3 / 2 : ℝ) <
      Real.log (energyNorm (scalarInterval n ×ˢ ({0, 1} : Finset ℤ))) -
        (∑ y, finitePush ν (imageEndpoint _ Prod.fst) y *
          Real.log (energyNorm (fiber (scalarInterval n ×ˢ ({0, 1} : Finset ℤ)) Prod.fst y.val))) -
        c * finiteEntropy (finitePush ν (imageEndpoint _ Prod.fst)) := by
  rw [product_fiber_log_norm_loss (scalarInterval_nonempty hn) (by simp) ν hs]
  have hu := product_first_entropy_upper (scalarInterval_nonempty hn) (by simp) ν hν hs
  rw [scalarInterval_card] at hu
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := Real.log_lt_log (by positivity : (0 : ℝ) < 2 * n / 3)
    (energyNorm_scalarInterval_bounds hn).1
  rw [show 2 * (n : ℝ) / 3 = n / (3 / 2) by ring,
    Real.log_div hn'.ne' (by norm_num : (3 / 2 : ℝ) ≠ 0)] at hl
  nlinarith [mul_le_mul_of_nonneg_left hu hc]

end
end Erdos539Geometry
