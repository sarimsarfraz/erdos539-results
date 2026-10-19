/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13CutEntropy
import Erdos539.UniformInjectiveImage

namespace Erdos539Geometry
noncomputable section
open scoped Classical

theorem pg13Branch_uniform_law (T : ℕ) (l : Fin 13) :
    finitePush (uniformReference (fourLeafBranch T)) (imageEndpoint (fourLeafBranch T) (pg13BranchEmbed T l)) =
      uniformReference (pg13Branch T l) :=
  uniformReference_image_injective _ _ (pg13BranchEmbed_injective T l).injOn

/-- Projection entropy after actually retaining one branch and
renormalizing its uniform law. -/
theorem pg13Branch_projection_entropy {T : ℕ} (hT : 0 < T) (l : Fin 13) (I : Finset (Fin 13)) :
    finiteEntropy (finitePush (uniformReference (pg13Branch T l))
      (imageEndpoint (pg13Branch T l) (fun x (j : I) ↦ x j.val))) =
        ((fourLeafActiveDigits (pg13LocalCoordinates l I)).card : ℝ) * Real.log (T : ℝ) := by
  let g := (imageEndpoint (pg13Branch T l) (fun x (j : I) ↦ x j.val)) ∘
    (imageEndpoint (fourLeafBranch T) (pg13BranchEmbed T l))
  have hg (a b : fourLeafBranch T) :
      pg13UnionObservation T I (l, a) = pg13UnionObservation T I (l, b) ↔ g a = g b := by
    constructor
    · intro h
      have hv := congrArg Subtype.val h
      exact Subtype.ext hv
    · intro h
      have hv := congrArg Subtype.val h
      exact Subtype.ext hv
  have h := finiteEntropy_push_eq_of_same_fibers (uniformReference (fourLeafBranch T))
    (fun a ↦ pg13UnionObservation T I (l, a)) g hg
  have hc := finitePush_comp (uniformReference (fourLeafBranch T))
    (imageEndpoint (fourLeafBranch T) (pg13BranchEmbed T l))
    (imageEndpoint (pg13Branch T l) (fun x (j : I) ↦ x j.val))
  rw [pg13Branch_uniform_law] at hc
  change finitePush (uniformReference (pg13Branch T l))
    (imageEndpoint (pg13Branch T l) (fun x (j : I) ↦ x j.val)) =
      finitePush (uniformReference (fourLeafBranch T)) g at hc
  rw [hc, ← h, pg13_branch_observation_entropy hT]

def pg13SiblingCut (l : Fin 13) : Finset (Fin 13) :=
  ({0, 1} : Finset (Fin 4)).image (pg13LineEmbedding l)

theorem pg13SiblingCut_digits : ∀ l : Fin 13,
    (fourLeafActiveDigits (pg13LocalCoordinates l (pg13SiblingCut l))).card = 4 ∧
    (fourLeafActiveDigits (pg13LocalCoordinates l (pg13SiblingCut l)ᶜ)).card = 4 := by
  decide +kernel

theorem pg13Branch_subset_union (T : ℕ) (l : Fin 13) : pg13Branch T l ⊆ pg13Union T := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, hx⟩

theorem pg13Union_maxFan_ge {T : ℕ} (hT : 0 < T) :
    T ^ 4 ≤ maxFan (integerRealSet (pg13Union T)) := by
  have hs : integerRealSet (pg13Branch T 0) ⊆ integerRealSet (pg13Union T) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_integerRealSet.mp hx
    exact mem_integerRealSet.mpr ⟨a, pg13Branch_subset_union T 0 ha, rfl⟩
  have h := maxFan_mono hs
  rw [pg13Branch_maxFan] at h
  exact (fourLeafBranch_maxFan_bounds hT).1.trans h

/-- Every retained branch has density exactly 1/13 and a sibling cut
whose two actual projection entropies are bounded by log M of the union. -/
theorem pg13_retained_branch_repair {T : ℕ} (hT : 0 < T) (l : Fin 13) :
    pg13Branch T l ⊆ pg13Union T ∧ (pg13Branch T l).card * 13 = (pg13Union T).card ∧
    (finiteEntropy (finitePush (uniformReference (pg13Branch T l))
      (imageEndpoint (pg13Branch T l) (fun x (j : pg13SiblingCut l) ↦ x j.val))) ≤
        Real.log (maxFan (integerRealSet (pg13Union T)) : ℝ)) ∧
    (finiteEntropy (finitePush (uniformReference (pg13Branch T l))
      (imageEndpoint (pg13Branch T l) (fun x (j : ↥((pg13SiblingCut l)ᶜ)) ↦ x j.val))) ≤
        Real.log (maxFan (integerRealSet (pg13Union T)) : ℝ)) := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hm : (T : ℝ) ^ 4 ≤ maxFan (integerRealSet (pg13Union T)) := by exact_mod_cast pg13Union_maxFan_ge hT
  have hl := Real.log_le_log (pow_pos ht 4) hm
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  refine ⟨pg13Branch_subset_union T l, ?_, ?_, ?_⟩
  · rw [pg13Branch_card, pg13Union_card hT]
    omega
  · rw [pg13Branch_projection_entropy hT, (pg13SiblingCut_digits l).1]
    exact hl
  · rw [pg13Branch_projection_entropy hT, (pg13SiblingCut_digits l).2]
    exact hl

end
end Erdos539Geometry
