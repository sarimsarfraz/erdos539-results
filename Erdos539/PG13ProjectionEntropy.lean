/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13UnionLaw
import Erdos539.FiniteMixtureEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

def pg13LocalCoordinates (l : Fin 13) (I : Finset (Fin 13)) : Finset (Fin 4) :=
  Finset.univ.filter (fun i ↦ pg13LineEmbedding l i ∈ I)

def pg13VisibleWeight (I : Finset (Fin 13)) : ℕ :=
  ∑ l : Fin 13, (fourLeafActiveDigits (pg13LocalCoordinates l I)).card

def pg13UnionObservation (T : ℕ) (I : Finset (Fin 13)) (z : Fin 13 × fourLeafBranch T) :
    (pg13Union T).image (fun x (j : I) ↦ x j.val) :=
  imageEndpoint (pg13Union T) (fun x (j : I) ↦ x j.val) (pg13UnionEndpoint T z)

theorem pg13_branch_observation_fibers (T : ℕ) (l : Fin 13) (I : Finset (Fin 13))
    (a b : fourLeafBranch T) :
    pg13UnionObservation T I (l, a) = pg13UnionObservation T I (l, b) ↔
      imageEndpoint (fourLeafBranch T) (fun x (i : pg13LocalCoordinates l I) ↦ x i.val) a =
      imageEndpoint (fourLeafBranch T) (fun x (i : pg13LocalCoordinates l I) ↦ x i.val) b := by
  constructor
  · intro h
    apply Subtype.ext
    funext i
    have hi : pg13LineEmbedding l i.val ∈ I := (Finset.mem_filter.mp i.property).2
    have he := congrFun (congrArg Subtype.val h) ⟨pg13LineEmbedding l i.val, hi⟩
    change pg13BranchEmbed T l a.val (pg13LineEmbedding l i.val) =
      pg13BranchEmbed T l b.val (pg13LineEmbedding l i.val) at he
    simpa only [pg13BranchEmbed_at, add_left_inj] using he
  · intro h
    apply Subtype.ext
    funext j
    change pg13BranchEmbed T l a.val j.val = pg13BranchEmbed T l b.val j.val
    by_cases hj : j.val ∈ pg13LineSet l
    · obtain ⟨i, hi⟩ := (pg13_mem_line_iff l j.val).mp hj
      have him : i ∈ pg13LocalCoordinates l I := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by rw [hi]; exact j.property⟩
      have he := congrFun (congrArg Subtype.val h) ⟨i, him⟩
      rw [← hi, pg13BranchEmbed_at, pg13BranchEmbed_at]
      exact congrArg (fun t : ℤ ↦ t + fourLeafShift T) he
    · rw [pg13BranchEmbed_off T l a.val j.val hj, pg13BranchEmbed_off T l b.val j.val hj]

theorem pg13_branch_observation_entropy {T : ℕ} (hT : 0 < T) (l : Fin 13)
    (I : Finset (Fin 13)) :
    finiteEntropy (finitePush (uniformReference (fourLeafBranch T))
      (fun a ↦ pg13UnionObservation T I (l, a))) =
        ((fourLeafActiveDigits (pg13LocalCoordinates l I)).card : ℝ) * Real.log (T : ℝ) := by
  have h := finiteEntropy_push_eq_of_same_fibers (uniformReference (fourLeafBranch T))
    (fun a ↦ pg13UnionObservation T I (l, a))
    (imageEndpoint (fourLeafBranch T) (fun x (i : pg13LocalCoordinates l I) ↦ x i.val))
    (pg13_branch_observation_fibers T l I)
  exact h.trans (fourLeafBranch_projection_entropy hT (pg13LocalCoordinates l I))

/-- Entropy lower bound for the actual uniform union law, with no
assumption that projected branch supports are disjoint. -/
theorem pg13Union_projection_entropy {T : ℕ} (hT : 0 < T) (I : Finset (Fin 13)) :
    (pg13VisibleWeight I : ℝ) / 13 * Real.log (T : ℝ) ≤
      finiteEntropy (finitePush (uniformReference (pg13Union T))
        (imageEndpoint (pg13Union T) (fun x (j : I) ↦ x j.val))) := by
  have h := finiteEntropy_mixture_observation (finiteUniformWeight (Fin 13))
    (uniformReference (fourLeafBranch T)) (finiteUniformWeight_nonneg _)
    (finiteUniformWeight_sum _) (fun x ↦ (uniformReference_pos (fourLeafBranch_nonempty hT) x).le)
    (uniformReference_sum (fourLeafBranch_nonempty hT))
    (fun l a ↦ pg13UnionObservation T I (l, a))
  have he : finitePush (fun z : Fin 13 × fourLeafBranch T ↦
      finiteUniformWeight (Fin 13) z.1 * uniformReference (fourLeafBranch T) z.2)
        (fun z ↦ pg13UnionObservation T I z) =
      finitePush (uniformReference (pg13Union T))
        (imageEndpoint (pg13Union T) (fun x (j : I) ↦ x j.val)) := by
    rw [← pg13Union_uniform_law hT]
    exact (finitePush_comp _ (pg13UnionEndpoint T)
      (imageEndpoint (pg13Union T) (fun x (j : I) ↦ x j.val))).symm
  rw [he] at h
  simp_rw [pg13_branch_observation_entropy hT, finiteUniformWeight, Fintype.card_fin] at h
  have hs : (∑ l : Fin 13, (1 / (13 : ℝ)) *
      (((fourLeafActiveDigits (pg13LocalCoordinates l I)).card : ℝ) * Real.log (T : ℝ))) =
      (pg13VisibleWeight I : ℝ) / 13 * Real.log (T : ℝ) := by
    simp only [pg13VisibleWeight, Nat.cast_sum, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  norm_num only [Nat.cast_ofNat] at h
  rwa [hs] at h

end
end Erdos539Geometry
