/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteObservationEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- Exact chain decomposition of the mutual information between two pairs. -/
theorem four_block_information_identity {κ : Type*} (H : Finset κ → ℝ) (h0 : H ∅ = 0)
    (C Z D W : Finset κ) :
    maskCMI H (C ∪ Z) (D ∪ W) ∅ =
      maskCMI H C D ∅ + maskCMI H Z D C + maskCMI H W C D + maskCMI H Z W (C ∪ D) := by
  simp only [maskCMI, Finset.union_empty, h0, Finset.union_left_comm, Finset.union_comm]
  ring

/-- Four nonnegative terms for literal observations of one probability law. -/
theorem observation_four_information_terms {α β κ : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (O : κ → α → β) (C Z D W : Finset κ) :
    0 ≤ maskCMI (observationEntropy p O) C D ∅ ∧
    0 ≤ maskCMI (observationEntropy p O) Z D C ∧
    0 ≤ maskCMI (observationEntropy p O) W C D ∧
    0 ≤ maskCMI (observationEntropy p O) Z W (C ∪ D) :=
  ⟨observation_maskCMI_nonneg p hp O _ _ _, observation_maskCMI_nonneg p hp O _ _ _,
    observation_maskCMI_nonneg p hp O _ _ _, observation_maskCMI_nonneg p hp O _ _ _⟩

theorem observation_four_information_identity {α β κ : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    (O : κ → α → β) (C Z D W : Finset κ) :
    maskCMI (observationEntropy p O) (C ∪ Z) (D ∪ W) ∅ =
      maskCMI (observationEntropy p O) C D ∅ + maskCMI (observationEntropy p O) Z D C +
      maskCMI (observationEntropy p O) W C D + maskCMI (observationEntropy p O) Z W (C ∪ D) :=
  four_block_information_identity _ (observationEntropy_empty p hp hs O) C Z D W

end
end Erdos539Geometry
