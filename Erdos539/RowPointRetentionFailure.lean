/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RowPointUniformEnergy
import Erdos539.SidonFiberSharpness

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem rowPointReference_marginal_uniform (S : Finset G) (h0 : (0 : G) ∈ S) :
    finitePush (rowPointReference S) (imageEndpoint (rowPointSupport S) Prod.snd) =
      uniformReference ((rowPointSupport S).image Prod.snd) := by
  funext y
  rw [rowPointReference_marginal S h0]
  simp only [uniformReference, rowPointSupport_image S h0]
  norm_num

theorem rowPointReference_marginal_energy (S : Finset G) (h0 : (0 : G) ∈ S) :
    weightedEnergy ((rowPointSupport S).image Prod.snd)
      (extendWeight ((rowPointSupport S).image Prod.snd)
        (fun y ↦ Real.sqrt (finitePush (rowPointReference S) (imageEndpoint (rowPointSupport S) Prod.snd) y))) = 3 / 2 := by
  have hs : HasSidonSums ({0, 1} : Finset ℤ) := by
    simpa only [HasSidonSums, Finset.mem_insert, Finset.mem_singleton] using hasSidonSums_binary
  rw [rowPointReference_marginal_uniform S h0, sqrt_uniformReference,
    uniformEnergyWeight_energy, rowPointSupport_image S h0,
    countingEnergy_sidon hs]
  norm_num

theorem rowPointReference_geometric_mean (S : Finset G) (h0 : (0 : G) ∈ S) :
    (∏ y, imageConditionalEnergy (rowPointSupport S) Prod.snd (rowPointReference S) y ^
      finitePush (rowPointReference S) (imageEndpoint (rowPointSupport S) Prod.snd) y) =
      Real.sqrt (countingEnergy S / (S.card : ℝ) ^ 2) := by
  simp only [rowPointReference_conditional_energy S h0, rowPointReference_marginal S h0]
  calc
    _ = ∏ y ∈ (rowPointSupport S).image Prod.snd,
        (if y = 0 then countingEnergy S / (S.card : ℝ) ^ 2 else 1) ^ (1 / 2 : ℝ) := by
      exact Finset.prod_attach ((rowPointSupport S).image Prod.snd)
        (fun y : ℤ ↦ (if y = 0 then countingEnergy S / (S.card : ℝ) ^ 2 else 1) ^ (1 / 2 : ℝ))
    _ = _ := by
      rw [rowPointSupport_image S h0]
      norm_num [← Real.sqrt_eq_rpow]

omit [AddCommGroup G] [DecidableEq G] in
theorem row_point_numeric_failure {ℓ : ℝ} (hℓ : 25 < ℓ) :
    (3 / 2 : ℝ) * Real.sqrt ℓ < (ℓ + 5) / 4 := by
  have hpos : 0 ≤ ℓ := by linarith
  have hs := Real.sq_sqrt hpos
  have hroot : 5 < Real.sqrt ℓ := by
    nlinarith [Real.sqrt_nonneg ℓ]
  have hm : 0 < (Real.sqrt ℓ - 1) * (Real.sqrt ℓ - 5) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

/-- The literal raw parent energy exceeds projected marginal energy times
the geometric mean of actual conditional energies. Thus the optimizing
parent hypothesis cannot be removed from the retention statement. -/
theorem rowPointReference_retention_failure (S : Finset G) (h0 : (0 : G) ∈ S)
    (hE : 25 < countingEnergy S / (S.card : ℝ) ^ 2) :
    weightedEnergy ((rowPointSupport S).image Prod.snd)
      (extendWeight ((rowPointSupport S).image Prod.snd)
        (fun y ↦ Real.sqrt (finitePush (rowPointReference S) (imageEndpoint (rowPointSupport S) Prod.snd) y))) *
      (∏ y, imageConditionalEnergy (rowPointSupport S) Prod.snd (rowPointReference S) y ^
        finitePush (rowPointReference S) (imageEndpoint (rowPointSupport S) Prod.snd) y) <
      weightedEnergy (rowPointSupport S)
        (extendWeight (rowPointSupport S) (fun x ↦ Real.sqrt (rowPointReference S x))) := by
  rw [rowPointReference_marginal_energy S h0, rowPointReference_geometric_mean S h0,
    rowPointReference_energy S h0]
  exact row_point_numeric_failure hE

end
end Erdos539Geometry
