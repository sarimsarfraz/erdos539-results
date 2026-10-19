/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13Branches
import Erdos539.FourLeafDefect

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

def pg13UnionEndpoint (T : ℕ) (z : Fin 13 × fourLeafBranch T) : pg13Union T :=
  ⟨pg13BranchEmbed T z.1 z.2.val,
    Finset.mem_biUnion.mpr ⟨z.1, Finset.mem_univ _, Finset.mem_image_of_mem _ z.2.property⟩⟩

theorem pg13UnionEndpoint_bijective {T : ℕ} (hT : 0 < T) :
    Function.Bijective (pg13UnionEndpoint T) := by
  constructor
  · intro a b he
    have hv := congrArg Subtype.val he
    have hl : a.1 = b.1 := by
      by_contra hn
      have ha : pg13BranchEmbed T a.1 a.2.val ∈ pg13Branch T a.1 :=
        Finset.mem_image_of_mem _ a.2.property
      have hb : pg13BranchEmbed T a.1 a.2.val ∈ pg13Branch T b.1 := by
        change pg13BranchEmbed T a.1 a.2.val = pg13BranchEmbed T b.1 b.2.val at hv
        rw [hv]
        exact Finset.mem_image_of_mem _ b.2.property
      exact Finset.disjoint_left.mp (pg13Branches_disjoint hT hn) ha hb
    obtain ⟨l, a⟩ := a
    obtain ⟨m, b⟩ := b
    dsimp only at hl
    subst m
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact pg13BranchEmbed_injective T l hv
  · intro x
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp x.property
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hl
    exact ⟨(l, ⟨a, ha⟩), Subtype.ext he⟩

/-- The actual uniform union law is obtained by choosing a uniform line
and an independent uniform branch point. -/
theorem pg13Union_uniform_law {T : ℕ} (hT : 0 < T) :
    finitePush (fun z : Fin 13 × fourLeafBranch T ↦
      finiteUniformWeight (Fin 13) z.1 * uniformReference (fourLeafBranch T) z.2)
        (pg13UnionEndpoint T) = uniformReference (pg13Union T) := by
  have h := finiteUniformWeight_equiv (Equiv.ofBijective (pg13UnionEndpoint T) (pg13UnionEndpoint_bijective hT))
  change finitePush (finiteUniformWeight (Fin 13 × fourLeafBranch T)) (pg13UnionEndpoint T) =
    finiteUniformWeight (pg13Union T) at h
  rw [finiteUniformWeight_product] at h
  have hp : finiteUniformWeight (fourLeafBranch T) = uniformReference (fourLeafBranch T) := by
    funext x
    simp [finiteUniformWeight, uniformReference]
  have hu : finiteUniformWeight (pg13Union T) = uniformReference (pg13Union T) := by
    funext x
    simp [finiteUniformWeight, uniformReference]
  change finitePush (fun z : Fin 13 × fourLeafBranch T ↦
    finiteUniformWeight (Fin 13) z.1 * finiteUniformWeight (fourLeafBranch T) z.2)
      (pg13UnionEndpoint T) = finiteUniformWeight (pg13Union T) at h
  rwa [hp, hu] at h

theorem pg13Union_nonempty {T : ℕ} (hT : 0 < T) : (pg13Union T).Nonempty := by
  apply Finset.card_pos.mp
  rw [pg13Union_card hT]
  positivity

end
end Erdos539Geometry
