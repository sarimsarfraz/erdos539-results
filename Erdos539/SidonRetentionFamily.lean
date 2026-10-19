/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarSidonFamily

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
local instance sidonRetentionIntDecidableEq : DecidableEq ℤ := Classical.decEq _

theorem scalarSidonSet_nonempty {n : ℕ} (hn : 0 < n) : (scalarSidonSet n).Nonempty := by
  rw [← Finset.card_pos, scalarSidonSet_card]
  exact hn

theorem scalarSidon_binary_entropy {n : ℕ} (hn : 0 < n) :
    finiteEntropy (finitePush (uniformReference (scalarSidonSet n ×ˢ ({0, 1} : Finset ℤ)))
      (imageEndpoint _ Prod.fst)) = Real.log (n : ℝ) := by
  rw [uniform_product_first_entropy (scalarSidonSet_nonempty hn) (by simp), scalarSidonSet_card]

theorem scalarSidon_binary_profile {n : ℕ} (hn : 0 < n) :
    stationaryEnergyProfile ((scalarSidonSet n ×ˢ ({0, 1} : Finset ℤ)).image Prod.fst)
      (finitePush (uniformReference (scalarSidonSet n ×ˢ ({0, 1} : Finset ℤ)))
        (imageEndpoint _ Prod.fst)) = Real.log (2 - 1 / (n : ℝ)) := by
  rw [sidon_binary_first_profile (scalarSidonSet_nonempty hn) (scalarSidonSet_sidon n), scalarSidonSet_card]

/-- Arbitrarily large label entropy with a uniformly bounded optimized
projection cost, on explicit scalar Sidon products whose uniform weights
are exact energy maximizers. -/
theorem sidon_retention_entropy_separation (R : ℝ) :
    ∃ n : ℕ, 0 < n ∧
      R < finiteEntropy (finitePush (uniformReference (scalarSidonSet n ×ˢ ({0, 1} : Finset ℤ)))
        (imageEndpoint _ Prod.fst)) ∧
      stationaryEnergyProfile ((scalarSidonSet n ×ˢ ({0, 1} : Finset ℤ)).image Prod.fst)
        (finitePush (uniformReference (scalarSidonSet n ×ˢ ({0, 1} : Finset ℤ)))
          (imageEndpoint _ Prod.fst)) < Real.log 2 ∧
      weightedEnergy (scalarSidonSet n ×ˢ ({0, 1} : Finset ℤ))
        (extendWeight (scalarSidonSet n ×ˢ ({0, 1} : Finset ℤ))
          (uniformEnergyWeight (scalarSidonSet n ×ˢ ({0, 1} : Finset ℤ)))) =
        energyNorm (scalarSidonSet n ×ˢ ({0, 1} : Finset ℤ)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp R)
  have hn' : (0 : ℝ) < n := (Real.exp_pos R).trans hn
  have hn0 : 0 < n := by exact_mod_cast hn'
  refine ⟨n, hn0, ?_, ?_, sidon_binary_uniform_maximizes
    (scalarSidonSet_nonempty hn0) (scalarSidonSet_sidon n)⟩
  · rw [scalarSidon_binary_entropy hn0]
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos R) hn
  · rw [sidon_binary_first_profile (scalarSidonSet_nonempty hn0) (scalarSidonSet_sidon n)]
    rw [← stationaryEnergyProfile_sidon_uniform (scalarSidonSet_nonempty hn0) (scalarSidonSet_sidon n)]
    exact stationaryEnergyProfile_sidon_uniform_lt_log_two
      (scalarSidonSet_nonempty hn0) (scalarSidonSet_sidon n)

end
end Erdos539Geometry
