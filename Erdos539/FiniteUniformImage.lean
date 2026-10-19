/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteUniformFunctions

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

def finiteImageEndpoint {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) (a : α) :
    Finset.univ.image f := ⟨f a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩

theorem finiteImageEndpoint_bijective {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) : Function.Bijective (finiteImageEndpoint f) := by
  constructor
  · intro a b he
    exact hf (congrArg Subtype.val he)
  · intro y
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp y.property
    exact ⟨a, Subtype.ext ha⟩

theorem finiteUniformWeight_image {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) :
    finitePush (finiteUniformWeight α) (finiteImageEndpoint f) = uniformReference (Finset.univ.image f) := by
  let e := Equiv.ofBijective (finiteImageEndpoint f) (finiteImageEndpoint_bijective f hf)
  have h := finiteUniformWeight_equiv e
  change finitePush (finiteUniformWeight α) (finiteImageEndpoint f) =
    finiteUniformWeight (Finset.univ.image f) at h
  rw [h]
  funext y
  simp only [finiteUniformWeight, uniformReference, Fintype.card_coe]

end
end Erdos539Geometry
