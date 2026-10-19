/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryEntropyDuality
import Erdos539.StationaryEntropyImageBound
import Erdos539.ImageFiberConditionalEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq H]
local instance entropyFibringImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

theorem entropy_image_dual_bound (Q : StationaryAdditiveLaw S ν)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (φ : G → H)
    (t : (y : S.image φ) → fiber S φ y.val → ℝ) :
    Q.entropy ≤ finiteEntropy (Q.imageFlat φ) + ∑ y, finitePush ν (imageEndpoint S φ) y *
      stationaryEntropyDualValue (fiber S φ y.val) (imageFiberReference S φ ν y) (t y) := by
  let f := fun (y : S.image φ) (x : fiber S φ y.val) ↦ Real.exp (t y x)
  let F := imageAssembleWeight S φ f
  let B := fun y ↦ weightedGibbsPartition (fiber S φ y.val) (f y)
  have hf : ∀ y x, 0 < f y x := fun y x ↦ Real.exp_pos _
  have hB : ∀ y, 0 < B y := fun y ↦ weightedGibbsPartition_pos (imageFiber_nonempty S φ y) (hf y)
  have h := Q.entropy_image_partition_bound hs φ F (imageAssembleWeight_pos S φ f hf) B hB (by
    intro y
    rw [imageFiberWeight_assemble])
  have hcross : (∑ x, ν x * Real.log (F x)) = ∑ y, finitePush ν (imageEndpoint S φ) y *
      ∑ x, imageFiberReference S φ ν y x * t y x := by
    rw [imageFiber_expectation_of_nonneg S φ ν hν (fun x ↦ Real.log (F x))]
    simp only [F, imageAssembleWeight_onFiber, f, Real.log_exp]
  rw [hcross] at h
  have hcost : (∑ y, finitePush ν (imageEndpoint S φ) y * Real.log (B y)) -
      4 * (∑ y, finitePush ν (imageEndpoint S φ) y * ∑ x, imageFiberReference S φ ν y x * t y x) =
      ∑ y, finitePush ν (imageEndpoint S φ) y *
        stationaryEntropyDualValue (fiber S φ y.val) (imageFiberReference S φ ν y) (t y) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    simp only [stationaryEntropyDualValue, B, f]
    ring
  linarith

/-- Entropy fibring for the actual projected parent quadruple and the
actual endpoint conditional laws. This holds for arbitrary label maps;
zero-mass fibers are retained and contribute zero. -/
theorem entropy_image_fibring (Q : StationaryAdditiveLaw S ν)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (φ : G → H) :
    Q.entropy ≤ finiteEntropy (Q.imageFlat φ) + ∑ y, finitePush ν (imageEndpoint S φ) y *
      stationaryAdditiveEntropy (fiber S φ y.val) (imageFiberReference S φ ν y) := by
  have happrox (ε : ℝ) (hε : 0 < ε) : Q.entropy ≤ finiteEntropy (Q.imageFlat φ) +
      (∑ y, finitePush ν (imageEndpoint S φ) y *
        stationaryAdditiveEntropy (fiber S φ y.val) (imageFiberReference S φ ν y)) + ε := by
    have hex : ∀ y : S.image φ, ∃ t : fiber S φ y.val → ℝ,
        finitePush ν (imageEndpoint S φ) y * stationaryEntropyDualValue (fiber S φ y.val) (imageFiberReference S φ ν y) t ≤
          finitePush ν (imageEndpoint S φ) y * (stationaryAdditiveEntropy (fiber S φ y.val) (imageFiberReference S φ ν y) + ε) := by
      intro y
      by_cases hy : finitePush ν (imageEndpoint S φ) y = 0
      · exact ⟨0, by simp only [hy, zero_mul, le_refl]⟩
      obtain ⟨t, ht⟩ := stationaryEntropyDualValue_approximate (imageFiber_nonempty S φ y)
        (imageFiberReference_nonneg S φ ν hν y) (imageFiberReference_sum_of_mass_ne_zero S φ ν y hy) hε
      exact ⟨t, mul_le_mul_of_nonneg_left ht.le (finitePush_nonneg ν (imageEndpoint S φ) hν y)⟩
    choose t ht using hex
    have h := Q.entropy_image_dual_bound hν hs φ t
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ ↦ ht y)
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, finitePush_sum, hs, one_mul] at hsum
    linarith
  by_contra hn
  have hgap := sub_pos.mpr (lt_of_not_ge hn)
  have h := happrox _ (half_pos hgap)
  linarith

end StationaryAdditiveLaw

variable [AddCommGroup H]

/-- The actual additive image is feasible for its own entropy maximum,
giving the manuscript's optimized image-and-fiber inequality. -/
theorem stationaryAdditiveEntropy_fibring {S : Finset G} {ν : S → ℝ}
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (φ : G →+ H) :
    stationaryAdditiveEntropy S ν ≤ stationaryAdditiveEntropy (S.image φ) (finitePush ν (imageEndpoint S φ)) +
      ∑ y, finitePush ν (imageEndpoint S φ) y * stationaryAdditiveEntropy (fiber S φ y.val) (imageFiberReference S φ ν y) := by
  obtain ⟨Q, hQ⟩ := stationaryAdditiveEntropy_attained S ν hν hs
  have h := Q.entropy_image_fibring hν hs φ
  let P := Q.map (imageEndpoint S φ) (imageEndpoint_preserves_additive S φ)
  have hP := P.entropy_le_stationaryAdditiveEntropy (finitePush_nonneg ν (imageEndpoint S φ) hν)
    (by rw [finitePush_sum, hs])
  have he : finiteEntropy (Q.imageFlat φ) = P.entropy := by
    simp only [StationaryAdditiveLaw.imageFlat, StationaryAdditiveLaw.entropy, P,
      StationaryAdditiveLaw.map, finiteEntropy, Fintype.sum_prod_type]
  rw [he, hQ] at h
  linarith

theorem stationaryEntropyDefect_superadditive {S : Finset G} {ν : S → ℝ}
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (φ : G →+ H) :
    stationaryEntropyDefect (S.image φ) (finitePush ν (imageEndpoint S φ)) +
      (∑ y, finitePush ν (imageEndpoint S φ) y * stationaryEntropyDefect (fiber S φ y.val) (imageFiberReference S φ ν y)) ≤
        stationaryEntropyDefect S ν := by
  have h := stationaryAdditiveEntropy_fibring hν hs φ
  have he := imageFiber_entropy_chain S φ ν hν
  unfold stationaryEntropyDefect
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hsum : (∑ y, finitePush ν (imageEndpoint S φ) y * (3 * finiteEntropy (imageFiberReference S φ ν y))) =
      3 * ∑ y, finitePush ν (imageEndpoint S φ) y * finiteEntropy (imageFiberReference S φ ν y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hsum]
  linarith

end
end Erdos539Geometry
