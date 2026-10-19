/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProductCriticalExclusion
import Erdos539.SparseReflectionProductExistence

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
local instance productCriticalScalarDecidableEq : DecidableEq ℤ := Classical.decEq _
local instance productCriticalEmbeddingDecidableEq {ι : Type} : DecidableEq (ι → ℝ) := Classical.decEq _

def scalarRealCoordinateHom : ℤ →+ (Unit → ℝ) where
  toFun z := fun _ ↦ (z : ℝ)
  map_zero' := by funext i; simp
  map_add' _ _ := by funext i; simp

theorem scalarRealCoordinateHom_injective : Function.Injective scalarRealCoordinateHom := by
  intro a b he
  have h := congrFun he ()
  change (a : ℝ) = (b : ℝ) at h
  exact_mod_cast h

theorem sparseReflectionProduct_not_critical {S : Finset ℤ} (hS : S.Nonempty)
    (hlarge : 1 < energyNorm S) {T : ℕ} (hT : 0 < T) {b : ℝ} (hb : 1 < b)
    (parent : Finset (ReflectionProductCoordinates → ℝ)) (I : Finset ReflectionProductCoordinates) :
    ¬ IsProjectionCriticalCore parent b I (sparseReflectionProduct S T) := by
  rw [sparseReflectionProduct_eq]
  let A := S.image scalarRealCoordinateHom
  have hn : energyNorm A = energyNorm S := energyNorm_image_of_injective S _ scalarRealCoordinateHom_injective
  have hq : energyNorm A ≤ (posDiff A).card := by
    apply (energyNorm_le_card A).trans
    have hh := maxFan_le_card_posDiff A
    rw [maxFan_eq_card_one_dimensional ()] at hh
    exact_mod_cast hh
  exact product_not_projectionCriticalCore (hS.image _) ((gibbsStrip_nonempty hT _).image _)
    (by rwa [hn]) hq hb parent I

/-- The same literal examples used for product amplification are excluded
by the actual selection predicate, for any original parent and mask. -/
theorem exists_sparse_products_with_critical_exclusion (m : ℕ) (hm : 10 ≤ m) :
    ∃ S : Finset ℤ, S.Nonempty ∧ ∀ T : ℕ, 0 < T →
      (sparseReflectionProduct S T).Nonempty ∧
      (T : ℝ) / (27 * (m : ℝ)) ≤ energyNorm (sparseReflectionProduct S T) / maxFan (sparseReflectionProduct S T) ∧
      (∀ w, energyNorm (reflectedSupport (sparseReflectionProduct S T) w) ≤
        energyNorm (sparseReflectionProduct S T) * (24 / (m : ℝ) ^ 2)) ∧
      ∀ b : ℝ, 1 < b → ∀ parent I, ¬ IsProjectionCriticalCore parent b I (sparseReflectionProduct S T) := by
  obtain ⟨S, hS, _, hlarge, hprod⟩ := exists_sparse_reflection_products m hm
  refine ⟨S, hS, ?_⟩
  intro T hT
  obtain ⟨hP, hfan, _, href⟩ := hprod T hT
  exact ⟨hP, hfan, href, fun b hb parent I ↦ sparseReflectionProduct_not_critical hS hlarge hT hb parent I⟩

end
end Erdos539Geometry
