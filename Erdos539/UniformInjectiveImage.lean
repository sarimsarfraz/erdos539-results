/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteUniformImage
import Erdos539.EnergyTransport
import Erdos539.GibbsImageFibers

namespace Erdos539Geometry
noncomputable section
open scoped Classical

theorem finiteUniformWeight_finset {α : Type*} (S : Finset α) :
    finiteUniformWeight S = uniformReference S := by
  funext x
  simp [finiteUniformWeight, uniformReference]

theorem uniformReference_image_injective {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (hf : Set.InjOn f S) :
    finitePush (uniformReference S) (imageEndpoint S f) = uniformReference (S.image f) := by
  have h := finiteUniformWeight_equiv (supportImageEquiv S f hf)
  change finitePush (finiteUniformWeight S) (imageEndpoint S f) = finiteUniformWeight (S.image f) at h
  simpa only [finiteUniformWeight_finset] using h

end
end Erdos539Geometry
