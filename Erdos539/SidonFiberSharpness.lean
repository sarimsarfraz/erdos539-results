/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.UniformProductConditional
import Erdos539.BinaryCubeNorm

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
local instance sidonFiberIntDecidableEq : DecidableEq ℤ := Classical.decEq _

theorem hasSidonSums_binary : HasSidonSums ({0, 1} : Finset ℤ) := by
  intro a ha b hb c hc d hd he
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> omega

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem sidon_binary_uniform_maximizes {S : Finset G} (hS : S.Nonempty)
    (hSidon : HasSidonSums S) :
    weightedEnergy (S ×ˢ ({0, 1} : Finset ℤ))
      (extendWeight (S ×ˢ ({0, 1} : Finset ℤ)) (uniformEnergyWeight (S ×ˢ ({0, 1} : Finset ℤ)))) =
      energyNorm (S ×ˢ ({0, 1} : Finset ℤ)) := by
  exact uniformEnergyWeight_product_maximizes
    (uniformEnergyWeight_maximizes_sidon hS hSidon)
    (uniformEnergyWeight_maximizes_sidon (by simp) hasSidonSums_binary)

theorem sidon_binary_first_profile {S : Finset G} (hS : S.Nonempty)
    (hSidon : HasSidonSums S) :
    stationaryEnergyProfile ((S ×ˢ ({0, 1} : Finset ℤ)).image Prod.fst)
      (finitePush (uniformReference (S ×ˢ ({0, 1} : Finset ℤ)))
        (imageEndpoint _ Prod.fst)) = Real.log (2 - 1 / (S.card : ℝ)) := by
  rw [uniform_product_first_marginal hS (by simp), Finset.product_image_fst (by simp)]
  exact stationaryEnergyProfile_sidon_uniform hS hSidon

/-- Equality in the actual conditional-energy retention estimate for a
Sidon factor times a binary factor. Its loss is bounded by log 2 although
the actual label entropy is log |S|. -/
theorem sidon_binary_retention_equality {S : Finset G} (hS : S.Nonempty)
    (hSidon : HasSidonSums S) :
    Real.log (energyNorm (S ×ˢ ({0, 1} : Finset ℤ))) -
      stationaryEnergyProfile ((S ×ˢ ({0, 1} : Finset ℤ)).image Prod.fst)
        (finitePush (uniformReference (S ×ˢ ({0, 1} : Finset ℤ))) (imageEndpoint _ Prod.fst)) =
      ∑ y, finitePush (uniformReference (S ×ˢ ({0, 1} : Finset ℤ))) (imageEndpoint _ Prod.fst) y *
        Real.log (imageConditionalEnergy _ Prod.fst (uniformReference (S ×ˢ ({0, 1} : Finset ℤ))) y) := by
  rw [uniform_product_mean_log_conditional_energy hS (by simp),
    uniformEnergyWeight_maximizes_sidon (by simp) hasSidonSums_binary,
    sidon_binary_first_profile hS hSidon, energyNorm_product,
    Real.log_mul (energyNorm_pos hS).ne' (energyNorm_pos (by simp : ({0, 1} : Finset ℤ).Nonempty)).ne',
    energyNorm_sidon hS hSidon]
  ring

theorem sidon_binary_retention_loss_lt_log_two {S : Finset G} (hS : S.Nonempty)
    (hSidon : HasSidonSums S) :
    Real.log (energyNorm (S ×ˢ ({0, 1} : Finset ℤ))) -
      (∑ y, finitePush (uniformReference (S ×ˢ ({0, 1} : Finset ℤ))) (imageEndpoint _ Prod.fst) y *
        Real.log (imageConditionalEnergy _ Prod.fst (uniformReference (S ×ˢ ({0, 1} : Finset ℤ))) y)) < Real.log 2 := by
  have he := sidon_binary_retention_equality hS hSidon
  have hl := stationaryEnergyProfile_sidon_uniform_lt_log_two hS hSidon
  rw [stationaryEnergyProfile_sidon_uniform hS hSidon] at hl
  rw [sidon_binary_first_profile hS hSidon] at he
  linarith

end
end Erdos539Geometry
