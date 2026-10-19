/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryEntropyMaximum
import Erdos539.FiniteEntropyConcavity
import Mathlib.Tactic.FinCases

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G : Type*} [AddCommGroup G]

/-- All actual additive quadruple probabilities, before prescribing their
four endpoint marginals. -/
def additiveProbabilities (S : Finset G) : Set ((S × S) × (S × S) → ℝ) :=
  {p | (∀ z, 0 ≤ p z) ∧ (∑ z, p z = 1) ∧
    (∀ z, z.1.1.val + z.1.2.val ≠ z.2.1.val + z.2.2.val → p z = 0)}

theorem additiveProbabilities_isCompact (S : Finset G) : IsCompact (additiveProbabilities S) := by
  let C : Set ((S × S) × (S × S) → ℝ) :=
    {p | ∀ z, z.1.1.val + z.1.2.val ≠ z.2.1.val + z.2.2.val → p z = 0}
  have hC : IsClosed C := by
    simp only [C, Set.setOf_forall]
    apply isClosed_iInter
    intro z
    apply isClosed_iInter
    intro _
    exact isClosed_eq (continuous_apply z) continuous_const
  have he : additiveProbabilities S = Set.Icc (0 : (S × S) × (S × S) → ℝ) 1 ∩
      {p | ∑ z, p z = 1} ∩ C := by
    ext p
    constructor
    · rintro ⟨hp, hs, hrel⟩
      refine ⟨⟨⟨hp, ?_⟩, hs⟩, hrel⟩
      intro z
      change p z ≤ 1
      rw [← hs]
      exact Finset.single_le_sum (fun z _ ↦ hp z) (Finset.mem_univ z)
    · rintro ⟨⟨⟨hp, _⟩, hs⟩, hrel⟩
      exact ⟨hp, hs, hrel⟩
  rw [he]
  exact (isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)).inter_right hC

theorem additiveProbabilities_convex (S : Finset G) : Convex ℝ (additiveProbabilities S) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun z ↦ add_nonneg (mul_nonneg ha (hp.1 z)) (mul_nonneg hb (hq.1 z)), ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp.2.1, hq.2.1, mul_one, hab]
  · intro z hz
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp.2.2 z hz, hq.2.2 z hz,
      mul_zero, add_zero]

theorem additiveProbabilities_entropy_concave (S : Finset G) :
    ConcaveOn ℝ (additiveProbabilities S) finiteEntropy := by
  refine ⟨additiveProbabilities_convex S, ?_⟩
  intro p hp q hq a b ha hb hab
  exact finiteEntropy_concave p q hp.1 hq.1 ha hb hab

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

theorem flat_mem_additiveProbabilities (Q : StationaryAdditiveLaw S ν) (hs : ∑ x, ν x = 1) :
    Q.flat ∈ additiveProbabilities S := by
  refine ⟨fun z ↦ Q.nonneg z.1.1 z.1.2 z.2.1 z.2.2, ?_,
    fun z ↦ Q.supported z.1.1 z.1.2 z.2.1 z.2.2⟩
  simpa only [flat, Fintype.sum_prod_type] using Q.total_mass hs

end StationaryAdditiveLaw

omit [AddCommGroup G] in
def quadrupleEndpoint (S : Finset G) (i : Fin 4) (z : (S × S) × (S × S)) : S :=
  if i = 0 then z.1.1 else if i = 1 then z.1.2 else if i = 2 then z.2.1 else z.2.2

omit [AddCommGroup G] in
def quadrupleMarginals (S : Finset G) :
    (((S × S) × (S × S)) → ℝ) →ₗ[ℝ] ((Fin 4 × S) → ℝ) where
  toFun p ix := finitePush p (quadrupleEndpoint S ix.1) ix.2
  map_add' p q := by
    funext ix
    exact congrFun ((finitePushLinear (quadrupleEndpoint S ix.1)).map_add p q) ix.2
  map_smul' a p := by
    funext ix
    exact congrFun ((finitePushLinear (quadrupleEndpoint S ix.1)).map_smul a p) ix.2

omit [AddCommGroup G] in
def repeatedMarginal (S : Finset G) : (S → ℝ) →ₗ[ℝ] ((Fin 4 × S) → ℝ) where
  toFun ν ix := ν ix.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem StationaryAdditiveLaw.quadrupleMarginals_flat {S : Finset G} {ν : S → ℝ}
    (Q : StationaryAdditiveLaw S ν) : quadrupleMarginals S Q.flat = repeatedMarginal S ν := by
  funext ⟨i, x⟩
  fin_cases i
  · simpa only [quadrupleMarginals, LinearMap.coe_mk, AddHom.coe_mk,
      quadrupleEndpoint, if_pos rfl, repeatedMarginal] using congrFun Q.flat_first x
  · simpa [quadrupleMarginals, quadrupleEndpoint, repeatedMarginal] using congrFun Q.flat_second x
  · simpa [quadrupleMarginals, quadrupleEndpoint, repeatedMarginal] using congrFun Q.flat_third x
  · simpa [quadrupleMarginals, quadrupleEndpoint, repeatedMarginal] using congrFun Q.flat_fourth x

theorem stationaryAdditiveWeights_of_marginals {S : Finset G} {ν : S → ℝ}
    {p : (S × S) × (S × S) → ℝ} (hp : p ∈ additiveProbabilities S)
    (hm : quadrupleMarginals S p = repeatedMarginal S ν) : p ∈ stationaryAdditiveWeights S ν := by
  refine ⟨hp.1, hp.2.2, ?_, ?_, ?_, ?_⟩
  · funext x
    simpa [quadrupleMarginals, quadrupleEndpoint, repeatedMarginal] using congrFun hm (0, x)
  · funext x
    simpa [quadrupleMarginals, quadrupleEndpoint, repeatedMarginal] using congrFun hm (1, x)
  · funext x
    simpa [quadrupleMarginals, quadrupleEndpoint, repeatedMarginal] using congrFun hm (2, x)
  · funext x
    simpa [quadrupleMarginals, quadrupleEndpoint, repeatedMarginal] using congrFun hm (3, x)

end
end Erdos539Geometry
