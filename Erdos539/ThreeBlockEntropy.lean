/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteBlockEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Classical
variable {ι : Type*}

/-- The seven-term certificate is an exact identity, not a numerical check. -/
theorem three_block_seven_CMI_identity (H : Finset ι → ℝ) (h0 : H ∅ = 0)
    (U₁ U₂ U₃ V₁ V₂ V₃ : Finset ι) :
    H (U₁ ∪ V₂ ∪ V₃) + H (U₂ ∪ V₁ ∪ V₃) + H (U₃ ∪ V₁ ∪ V₂) -
      H (U₁ ∪ U₂ ∪ U₃ ∪ V₁ ∪ V₂ ∪ V₃) - H (V₁ ∪ V₂ ∪ V₃) =
    maskCMI H V₁ V₂ V₃ + maskCMI H (V₁ ∪ V₂) V₃ ∅ +
    maskCMI H U₁ V₁ (V₂ ∪ V₃) + maskCMI H U₂ V₂ (V₁ ∪ V₃) +
    maskCMI H U₃ V₃ (V₁ ∪ V₂) + maskCMI H U₁ U₂ (V₁ ∪ V₂ ∪ V₃) +
    maskCMI H (U₁ ∪ U₂) U₃ (V₁ ∪ V₂ ∪ V₃) := by
  simp only [maskCMI, Finset.union_empty, h0, Finset.union_left_comm, Finset.union_comm]
  ring

theorem three_block_entropy_inequality (H : Finset ι → ℝ) (h0 : H ∅ = 0)
    (hCMI : ∀ A B C, 0 ≤ maskCMI H A B C) (U₁ U₂ U₃ V₁ V₂ V₃ : Finset ι) :
    H (U₁ ∪ U₂ ∪ U₃ ∪ V₁ ∪ V₂ ∪ V₃) + H (V₁ ∪ V₂ ∪ V₃) ≤
      H (U₁ ∪ V₂ ∪ V₃) + H (U₂ ∪ V₁ ∪ V₃) + H (U₃ ∪ V₁ ∪ V₂) := by
  have he := three_block_seven_CMI_identity H h0 U₁ U₂ U₃ V₁ V₂ V₃
  linarith [hCMI V₁ V₂ V₃, hCMI (V₁ ∪ V₂) V₃ ∅, hCMI U₁ V₁ (V₂ ∪ V₃),
    hCMI U₂ V₂ (V₁ ∪ V₃), hCMI U₃ V₃ (V₁ ∪ V₂), hCMI U₁ U₂ (V₁ ∪ V₂ ∪ V₃),
    hCMI (U₁ ∪ U₂) U₃ (V₁ ∪ V₂ ∪ V₃)]

end
end Erdos539Geometry
